// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) 2022-2023 SUSE LLC
//
// Author: Joerg Roedel <jroedel@suse.de>

extern crate alloc;

use crate::address::{Address, VirtAddr};
use crate::types::PAGE_SIZE;
use alloc::vec::Vec;
use core::ops::{Add, BitAnd, Not, Sub};
use verus_stub::*;
use zeroize::{Zeroize, ZeroizeOnDrop};

#[cfg(verus_keep_ghost)]
include!("util.verus.rs");

#[verus_spec(ret =>
    requires
        align_up_requires((addr, align)),
    ensures
        align_up_ens((addr, align), ret),
)]
pub fn align_up<T>(addr: T, align: T) -> T
where
    T: Add<Output = T> + Sub<Output = T> + BitAnd<Output = T> + Not<Output = T> + From<u8> + Copy,
{
    let mask: T = align - T::from(1u8);
    (addr + mask) & !mask
}

#[verus_spec(ret =>
    requires
        align_down_requires((addr, align)),
    ensures
        align_down_ens((addr, align), ret),
)]
pub fn align_down<T>(addr: T, align: T) -> T
where
    T: Sub<Output = T> + Not<Output = T> + BitAnd<Output = T> + From<u8> + Copy,
{
    addr & !(align - T::from(1u8))
}

#[verus_spec(ret =>
    requires
        is_aligned_requires((addr, align)),
    ensures
        is_aligned_ens((addr, align), ret)
)]
pub fn is_aligned<T>(addr: T, align: T) -> bool
where
    T: Sub<Output = T> + BitAnd<Output = T> + PartialEq + From<u8>,
{
    (addr & (align - T::from(1u8))) == T::from(0u8)
}

pub fn page_align_up(x: usize) -> usize {
    align_up(x, PAGE_SIZE)
}

pub fn round_to_pages(x: usize) -> usize {
    page_align_up(x) / PAGE_SIZE
}

pub fn page_offset(x: usize) -> usize {
    x & (PAGE_SIZE - 1)
}

pub fn overlap<T>(x1: T, x2: T, y1: T, y2: T) -> bool
where
    T: PartialOrd,
{
    x1 <= y2 && y1 <= x2
}

/// # Safety
///
/// Caller should ensure [`core::ptr::write_bytes`] safety rules.
pub unsafe fn zero_mem_region(start: VirtAddr, end: VirtAddr) {
    if start.is_null() {
        panic!("Attempted to zero out a NULL pointer");
    }

    let count = end
        .checked_sub(start.as_usize())
        .expect("Invalid size calculation")
        .as_usize();

    // Zero region
    // SAFETY: the safety rules must be upheld by the caller.
    unsafe { start.as_mut_ptr::<u8>().write_bytes(0, count) }
}

/// Obtain bit for a given position
#[macro_export]
macro_rules! BIT {
    ($x: expr) => {
        (1 << ($x))
    };
}

/// Obtain bit mask for the given positions
#[macro_export]
macro_rules! BIT_MASK {
    ($e: expr, $s: expr) => {{
        assert!(
            $s <= 63 && $e <= 63 && $s <= $e,
            "Start bit position must be less than or equal to end bit position"
        );
        (((1u64 << ($e - $s + 1)) - 1) << $s)
    }};
}

#[derive(Debug, Clone, Copy)]
pub enum SecretBoxError {
    /// Secret is larger than the box capacity N.
    TooLarge { got: usize, cap: usize },
}

/// Secret Box which zeros our memory on drop. Useful for storing sensitive data like cryptographic keys.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SecretBox<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> SecretBox<N> {
    pub fn new(mut secret: Vec<u8>) -> Result<Self, SecretBoxError> {
        let len = secret.len();
        if len > N {
            secret.zeroize();
            return Err(SecretBoxError::TooLarge { got: len, cap: N });
        }
        let mut data = [0u8; N];
        data[..len].copy_from_slice(&secret);
        secret.zeroize();
        Ok(Self { data, len })
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.data[..self.len]
    }
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.data[..self.len]
    }
}

impl<const N: usize> core::fmt::Debug for SecretBox<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecretBox")
            .field("len", &self.len)
            .field("data", &"[REDACTED]")
            .finish()
    }
}

#[cfg(test)]
mod tests {

    use crate::utils::util::*;
    use alloc::vec::Vec;
    use zeroize::Zeroize;

    #[test]
    fn test_mem_utils() {
        // Align up
        assert_eq!(align_up(7, 4), 8);
        assert_eq!(align_up(15, 8), 16);
        assert_eq!(align_up(10, 2), 10);
        // Align down
        assert_eq!(align_down(7, 4), 4);
        assert_eq!(align_down(15, 8), 8);
        assert_eq!(align_down(10, 2), 10);
        // Page align up
        assert_eq!(page_align_up(4096), 4096);
        assert_eq!(page_align_up(4097), 8192);
        assert_eq!(page_align_up(0), 0);
        // Page offset
        assert_eq!(page_offset(4096), 0);
        assert_eq!(page_offset(4097), 1);
        assert_eq!(page_offset(0), 0);
        // Overlaps
        assert!(overlap(1, 5, 3, 6));
        assert!(overlap(0, 10, 5, 15));
        assert!(!overlap(1, 5, 6, 8));
    }

    #[test]
    fn test_zero_mem_region() {
        let mut data: [u8; 10] = [1; 10];
        let start = VirtAddr::from(data.as_mut_ptr());
        let end = start + core::mem::size_of_val(&data);

        // SAFETY: start and end correctly point respectively to the start and
        // end of data.
        unsafe {
            zero_mem_region(start, end);
        }

        for byte in &data {
            assert_eq!(*byte, 0);
        }
    }

    #[test]
    fn secretbox_stores_secret_and_zero_pads() {
        let b = SecretBox::<8>::new(Vec::from([1u8, 2, 3, 4, 5])).unwrap();
        assert_eq!(b.as_slice(), &[1, 2, 3, 4, 5]);
        assert_eq!(b.len, 5);
        assert_eq!(b.data[5..], [0u8; 3]); // bytes past len are zero
    }

    #[test]
    fn secretbox_exact_capacity_ok() {
        let b = SecretBox::<4>::new(Vec::from([9u8; 4])).unwrap();
        assert_eq!(b.as_slice(), &[9, 9, 9, 9]);
        assert_eq!(b.len, 4);
    }

    #[test]
    fn secretbox_empty_ok() {
        let b = SecretBox::<8>::new(Vec::new()).unwrap();
        assert!(b.as_slice().is_empty());
        assert_eq!(b.len, 0);
    }

    #[test]
    fn secretbox_too_large_errors() {
        match SecretBox::<8>::new(Vec::from([0u8; 9])) {
            Err(SecretBoxError::TooLarge { got, cap }) => {
                assert_eq!(got, 9);
                assert_eq!(cap, 8);
            }
            _ => panic!("expected TooLarge"),
        }
    }

    #[test]
    fn secretbox_as_mut_slice_mutates() {
        let mut b = SecretBox::<8>::new(Vec::from([1u8, 2, 3, 4])).unwrap();
        b.as_mut_slice()[0] = 42;
        assert_eq!(b.as_slice(), &[42, 2, 3, 4]);
    }

    #[test]
    fn secretbox_zeroize_wipes_fields() {
        let mut b = SecretBox::<8>::new(Vec::from([1u8, 2, 3, 4, 5, 6, 7, 8])).unwrap();
        b.zeroize();
        assert_eq!(b.data, [0u8; 8]);
        assert_eq!(b.len, 0);
    }

    #[test]
    fn secretbox_drop_zeroizes() {
        use core::mem::ManuallyDrop;

        let mut b =
            ManuallyDrop::new(SecretBox::<8>::new(Vec::from([1u8, 2, 3, 4, 5, 6, 7, 8])).unwrap());
        // SAFETY: `b` is a valid, initialized SecretBox dropped exactly once;
        // ManuallyDrop keeps its memory alive afterward so reading the
        // plain-integer bytes the destructor left behind is sound.
        unsafe {
            core::ptr::drop_in_place(&raw mut *b);
        }
        assert_eq!(b.data, [0u8; 8]);
        assert_eq!(b.len, 0);
    }
}
