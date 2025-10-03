#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]

use core::fmt;
use core::{
    cell::{Cell, UnsafeCell},
    cmp::Ordering,
    fmt::{Debug, Display, Formatter},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// A mutable memory location with dynamically checked borrow rules.
///
/// `UncheckedRefCell` behaves exactly like `std::cell::RefCell` when `debug_assertions` is enabled or `checked` feature
/// flag is enabled (for non-release-like builds). For release-like builds, `UncheckedRefCell` does not
/// perform any borrow checking. Thus it is faster than `RefCell` (see benchmarks), but may lead to
/// undefined behavior instead of panicking like `RefCell`. Use this over `RefCell` for performance
/// critical code where it is known a `RefCell` would never panic.
pub struct UncheckedRefCell<T: ?Sized> {
    #[cfg(any(feature = "checked", debug_assertions))]
    borrow: Cell<BorrowCounter>,
    // Stores the location of the earliest currently active borrow.
    // This gets updated whenever we go from having zero borrows
    // to having a single borrow. When a borrow occurs, this gets included
    // in the generated `BorrowError`/`BorrowMutError`
    #[cfg(feature = "debug_refcell")]
    borrowed_at: Cell<Option<&'static core::panic::Location<'static>>>,
    // to make not sync since `impl<T: ?Sized> !Sync for RefCell<T> {}` is not possible on stable outside of core
    marker: PhantomData<*mut T>,
    value: UnsafeCell<T>,
}

/// An error returned by [`RefCell::try_borrow`].
#[non_exhaustive]
#[derive(Debug)]
pub struct BorrowError {
    #[cfg(feature = "debug_refcell")]
    location: &'static core::panic::Location<'static>,
}

impl Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(feature = "debug_refcell")]
        let res = write!(
            f,
            "RefCell already mutably borrowed; a previous borrow was at {}",
            self.location
        );

        #[cfg(not(feature = "debug_refcell"))]
        let res = Display::fmt("RefCell already mutably borrowed", f);

        res
    }
}

/// An error returned by [`RefCell::try_borrow_mut`].
#[non_exhaustive]
#[derive(Debug)]
pub struct BorrowMutError {
    #[cfg(feature = "debug_refcell")]
    location: &'static core::panic::Location<'static>,
}

impl Display for BorrowMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg(feature = "debug_refcell")]
        let res = write!(
            f,
            "RefCell already borrowed; a previous borrow was at {}",
            self.location
        );

        #[cfg(not(feature = "debug_refcell"))]
        let res = Display::fmt("RefCell already borrowed", f);

        res
    }
}

// This ensures the panicking code is outlined from `borrow_mut` for `RefCell`.
#[track_caller]
#[cold]
fn panic_already_borrowed(err: BorrowError) -> ! {
    panic!("RefCell already borrowed: {err}")
}

// This ensures the panicking code is outlined from `borrow` for `RefCell`.
#[track_caller]
#[cold]
fn panic_already_mutably_borrowed(err: BorrowMutError) -> ! {
    panic!("RefCell already mutably borrowed: {err}")
}

// Positive values represent the number of `UncheckedRef` active. Negative values
// represent the number of `UncheckedRefMut` active. Multiple `UncheckedRefMut`s can only be
// active at a time if they refer to distinct, nonoverlapping components of a
// `RefCell` (e.g., different ranges of a slice).
//
// `UncheckedRef` and `UncheckedRefMut` are both two words in size, and so there will likely never
// be enough `UncheckedRef`s or `UncheckedRefMut`s in existence to overflow half of the `usize`
// range. Thus, a `BorrowCounter` will probably never overflow or underflow.
// However, this is not a guarantee, as a pathological program could repeatedly
// create and then mem::forget `UncheckedRef`s or `UncheckedRefMut`s. Thus, all code must
// explicitly check for overflow and underflow in order to avoid unsafety, or at
// least behave correctly in the event that overflow or underflow happens (e.g.,
// see BorrowRef::new).
type BorrowCounter = isize;
const UNUSED: BorrowCounter = 0;

#[inline(always)]
const fn is_writing(x: BorrowCounter) -> bool {
    x < UNUSED
}

#[inline(always)]
const fn is_reading(x: BorrowCounter) -> bool {
    x > UNUSED
}

impl<T> UncheckedRefCell<T> {
    /// Creates a new `RefCell` containing `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    /// ```
    #[inline]
    pub const fn new(value: T) -> UncheckedRefCell<T> {
        UncheckedRefCell {
            value: UnsafeCell::new(value),
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: Cell::new(UNUSED),
            marker: PhantomData,
            #[cfg(feature = "debug_refcell")]
            borrowed_at: Cell::new(None),
        }
    }

    /// Consumes the `RefCell`, returning the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// let five = c.into_inner();
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        // Since this function takes `self` (the `RefCell`) by value, the
        // compiler statically verifies that it is not currently borrowed.
        self.value.into_inner()
    }

    /// Replaces the wrapped value with a new one, returning the old value,
    /// without deinitializing either one.
    ///
    /// This function corresponds to [`std::mem::replace`](../mem/fn.replace.html).
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    /// let cell = UncheckedRefCell::new(5);
    /// let old_value = cell.replace(6);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, UncheckedRefCell::new(6));
    /// ```
    #[track_caller]
    pub fn replace(&self, t: T) -> T {
        mem::replace(&mut self.borrow_mut(), t)
    }

    /// Replaces the wrapped value with a new one computed from `f`, returning
    /// the old value, without deinitializing either one.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    /// let cell = UncheckedRefCell::new(5);
    /// let old_value = cell.replace_with(|&mut old| old + 1);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, UncheckedRefCell::new(6));
    /// ```
    #[inline]
    #[track_caller]
    pub fn replace_with<F: FnOnce(&mut T) -> T>(&self, f: F) -> T {
        let mut_borrow = &mut *self.borrow_mut();
        let replacement = f(mut_borrow);
        mem::replace(mut_borrow, replacement)
    }

    /// Swaps the wrapped value of `self` with the wrapped value of `other`,
    /// without deinitializing either one.
    ///
    /// This function corresponds to [`std::mem::swap`](../mem/fn.swap.html).
    ///
    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently borrowed, or
    /// if `self` and `other` point to the same `RefCell`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    /// let c = UncheckedRefCell::new(5);
    /// let d = UncheckedRefCell::new(6);
    /// c.swap(&d);
    /// assert_eq!(c, UncheckedRefCell::new(6));
    /// assert_eq!(d, UncheckedRefCell::new(5));
    /// ```
    #[inline]
    pub fn swap(&self, other: &Self) {
        mem::swap(&mut *self.borrow_mut(), &mut *other.borrow_mut())
    }
}

impl<T: ?Sized> UncheckedRefCell<T> {
    /// Immutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `UncheckedRef` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed. For a non-panicking variant, use
    /// [`try_borrow`](#method.try_borrow).
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// let borrowed_five = c.borrow();
    /// let borrowed_five2 = c.borrow();
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// let m = c.borrow_mut();
    /// let b = c.borrow(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow(&self) -> UncheckedRef<'_, T> {
        match self.try_borrow() {
            Ok(b) => b,
            Err(err) => panic_already_borrowed(err),
        }
    }

    /// Immutably borrows the wrapped value, returning an error if the value is currently mutably
    /// borrowed.
    ///
    /// The borrow lasts until the returned `UncheckedRef` exits scope. Multiple immutable borrows can be
    /// taken out at the same time.
    ///
    /// This is the non-panicking variant of [`borrow`](#method.borrow).
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow_mut();
    ///     assert!(c.try_borrow().is_err());
    /// }
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(c.try_borrow().is_ok());
    /// }
    /// ```
    #[inline]
    pub fn try_borrow(&self) -> Result<UncheckedRef<'_, T>, BorrowError> {
        #[cfg(any(feature = "checked", debug_assertions))]
        match BorrowRef::new(&self.borrow) {
            Some(b) => {
                // SAFETY: `BorrowRef` ensures that there is only immutable access
                // to the value while borrowed.
                let value = unsafe { NonNull::new_unchecked(self.value.get()) };
                Ok(UncheckedRef { value, borrow: b })
            }
            None => Err(BorrowError {
                // If a borrow occurred, then we must already have an outstanding borrow,
                // so `borrowed_at` will be `Some`
                #[cfg(feature = "debug_refcell")]
                location: self.borrowed_at.get().unwrap(),
            }),
        }
        #[cfg(not(any(feature = "checked", debug_assertions)))]
        {
            // SAFETY: `BorrowRef` ensures that there is only immutable access
            // to the value while borrowed.
            let value = unsafe { NonNull::new_unchecked(self.value.get()) };
            Ok(UncheckedRef {
                value,
                marker: PhantomData,
            })
        }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `UncheckedRefMut` or all `UncheckedRefMut`s derived
    /// from it exit scope. The value cannot be borrowed while this borrow is
    /// active.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed. For a non-panicking variant, use
    /// [`try_borrow_mut`](#method.try_borrow_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new("hello".to_owned());
    ///
    /// *c.borrow_mut() = "bonjour".to_owned();
    ///
    /// assert_eq!(&*c.borrow(), "bonjour");
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    /// let m = c.borrow();
    ///
    /// let b = c.borrow_mut(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow_mut(&self) -> UncheckedRefMut<'_, T> {
        match self.try_borrow_mut() {
            Ok(b) => b,
            Err(err) => panic_already_mutably_borrowed(err),
        }
    }

    /// Mutably borrows the wrapped value, returning an error if the value is currently borrowed.
    ///
    /// The borrow lasts until the returned `UncheckedRefMut` or all `UncheckedRefMut`s derived
    /// from it exit scope. The value cannot be borrowed while this borrow is
    /// active.
    ///
    /// This is the non-panicking variant of [`borrow_mut`](#method.borrow_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(c.try_borrow_mut().is_err());
    /// }
    ///
    /// assert!(c.try_borrow_mut().is_ok());
    /// ```
    #[inline]
    #[cfg_attr(feature = "debug_refcell", track_caller)]
    pub fn try_borrow_mut(&self) -> Result<UncheckedRefMut<'_, T>, BorrowMutError> {
        #[cfg(any(feature = "checked", debug_assertions))]
        {
            match BorrowRefMut::new(&self.borrow) {
                Some(b) => {
                    #[cfg(feature = "debug_refcell")]
                    {
                        self.borrowed_at
                            .replace(Some(core::panic::Location::caller()));
                    }

                    // SAFETY: `BorrowRefMut` guarantees unique access.
                    let value = unsafe { NonNull::new_unchecked(self.value.get()) };
                    Ok(UncheckedRefMut {
                        value,
                        borrow: b,
                        marker: PhantomData,
                    })
                }
                None => Err(BorrowMutError {
                    // If a borrow occurred, then we must already have an outstanding borrow,
                    // so `borrowed_at` will be `Some`
                    #[cfg(feature = "debug_refcell")]
                    location: self.borrowed_at.get().unwrap(),
                }),
            }
        }
        #[cfg(not(any(feature = "checked", debug_assertions)))]
        {
            let value = unsafe { NonNull::new_unchecked(self.value.get()) };
            Ok(UncheckedRefMut {
                value,
                marker: PhantomData,
            })
        }
    }

    /// Returns a raw pointer to the underlying data in this cell.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// let ptr = c.as_ptr();
    /// ```
    #[inline]
    pub const fn as_ptr(&self) -> *mut T {
        self.value.get()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this method borrows `RefCell` mutably, it is statically guaranteed
    /// that no borrows to the underlying data exist. The dynamic checks inherent
    /// in [`borrow_mut`] and most other methods of `RefCell` are therefore
    /// unnecessary. Note that this method does not reset the borrowing state if borrows were previously leaked
    /// (e.g., via [`forget()`] on a [`UncheckedRef`] or [`UncheckedRefMut`]). For that purpose,
    /// consider using the unstable [`undo_leak`] method.
    ///
    /// This method can only be called if `RefCell` can be mutably borrowed,
    /// which in general is only the case directly after the `RefCell` has
    /// been created. In these situations, skipping the aforementioned dynamic
    /// borrowing checks may yield better ergonomics and runtime-performance.
    ///
    /// In most situations where `RefCell` is used, it can't be borrowed mutably.
    /// Use [`borrow_mut`] to get mutable access to the underlying data then.
    ///
    /// [`borrow_mut`]: UncheckedRefCell::borrow_mut()
    /// [`forget()`]: mem::forget
    /// [`undo_leak`]: UncheckedRefCell::undo_leak()
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let mut c = UncheckedRefCell::new(5);
    /// *c.get_mut() += 1;
    ///
    /// assert_eq!(c, UncheckedRefCell::new(6));
    /// ```
    #[inline]
    pub const fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    /// Undo the effect of leaked guards on the borrow state of the `RefCell`.
    ///
    /// This call is similar to [`get_mut`] but more specialized. It borrows `RefCell` mutably to
    /// ensure no borrows exist and then resets the state tracking shared borrows. This is relevant
    /// if some `UncheckedRef` or `UncheckedRefMut` borrows have been leaked.
    ///
    /// [`get_mut`]: UncheckedRefCell::get_mut()
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let mut c = UncheckedRefCell::new(0);
    /// std::mem::forget(c.borrow_mut());
    ///
    /// assert!(c.try_borrow().is_err());
    /// c.undo_leak();
    /// assert!(c.try_borrow().is_ok());
    /// ```
    pub const fn undo_leak(&mut self) -> &mut T {
        #[cfg(any(feature = "checked", debug_assertions))]
        {
            *self.borrow.get_mut() = UNUSED;
        }
        self.get_mut()
    }

    /// Immutably borrows the wrapped value, returning an error if the value is
    /// currently mutably borrowed.
    ///
    /// # Safety
    ///
    /// Unlike `RefCell::borrow`, this method is unsafe because it does not
    /// return a `UncheckedRef`, thus leaving the borrow flag untouched. Mutably
    /// borrowing the `RefCell` while the reference returned by this method
    /// is alive is undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    ///
    /// {
    ///     let m = c.borrow_mut();
    ///     assert!(unsafe { c.try_borrow_unguarded() }.is_err());
    /// }
    ///
    /// {
    ///     let m = c.borrow();
    ///     assert!(unsafe { c.try_borrow_unguarded() }.is_ok());
    /// }
    /// ```
    #[inline]
    pub const unsafe fn try_borrow_unguarded(&self) -> Result<&T, BorrowError> {
        #[cfg(any(feature = "checked", debug_assertions))]
        {
            if !is_writing(self.borrow.get()) {
                // SAFETY: We check that nobody is actively writing now, but it is
                // the caller's responsibility to ensure that nobody writes until
                // the returned reference is no longer in use.
                // Also, `self.value.get()` refers to the value owned by `self`
                // and is thus guaranteed to be valid for the lifetime of `self`.
                Ok(unsafe { &*self.value.get() })
            } else {
                Err(BorrowError {
                    // If a borrow occurred, then we must already have an outstanding borrow,
                    // so `borrowed_at` will be `Some`
                    #[cfg(feature = "debug_refcell")]
                    location: self.borrowed_at.get().unwrap(),
                })
            }
        }
        #[cfg(not(any(feature = "checked", debug_assertions)))]
        Ok(unsafe { &*self.value.get() })
    }
}

impl<T: Default> UncheckedRefCell<T> {
    /// Takes the wrapped value, leaving `Default::default()` in its place.
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::UncheckedRefCell;
    ///
    /// let c = UncheckedRefCell::new(5);
    /// let five = c.take();
    ///
    /// assert_eq!(five, 5);
    /// assert_eq!(c.into_inner(), 0);
    /// ```
    pub fn take(&self) -> T {
        self.replace(Default::default())
    }
}

unsafe impl<T: ?Sized> Send for UncheckedRefCell<T> where T: Send {}

impl<T: Clone> Clone for UncheckedRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed.
    #[inline]
    #[track_caller]
    fn clone(&self) -> UncheckedRefCell<T> {
        UncheckedRefCell::new(self.borrow().clone())
    }

    /// # Panics
    ///
    /// Panics if `source` is currently mutably borrowed.
    #[inline]
    #[track_caller]
    fn clone_from(&mut self, source: &Self) {
        self.get_mut().clone_from(&source.borrow())
    }
}

impl<T: Default> Default for UncheckedRefCell<T> {
    /// Creates a `RefCell<T>`, with the `Default` value for T.
    #[inline]
    fn default() -> UncheckedRefCell<T> {
        UncheckedRefCell::new(Default::default())
    }
}

impl<T: ?Sized + PartialEq> PartialEq for UncheckedRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn eq(&self, other: &UncheckedRefCell<T>) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl<T: ?Sized + Eq> Eq for UncheckedRefCell<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for UncheckedRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn partial_cmp(&self, other: &UncheckedRefCell<T>) -> Option<Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }

    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn lt(&self, other: &UncheckedRefCell<T>) -> bool {
        *self.borrow() < *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn le(&self, other: &UncheckedRefCell<T>) -> bool {
        *self.borrow() <= *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn gt(&self, other: &UncheckedRefCell<T>) -> bool {
        *self.borrow() > *other.borrow()
    }

    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn ge(&self, other: &UncheckedRefCell<T>) -> bool {
        *self.borrow() >= *other.borrow()
    }
}

impl<T: ?Sized + Ord> Ord for UncheckedRefCell<T> {
    /// # Panics
    ///
    /// Panics if the value in either `RefCell` is currently mutably borrowed.
    #[inline]
    fn cmp(&self, other: &UncheckedRefCell<T>) -> Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

impl<T> From<T> for UncheckedRefCell<T> {
    /// Creates a new `RefCell<T>` containing the given value.
    fn from(t: T) -> UncheckedRefCell<T> {
        UncheckedRefCell::new(t)
    }
}

struct BorrowRef<'b> {
    borrow: &'b Cell<BorrowCounter>,
}

impl<'b> BorrowRef<'b> {
    #[inline]
    const fn new(borrow: &'b Cell<BorrowCounter>) -> Option<BorrowRef<'b>> {
        let b = borrow.get().wrapping_add(1);
        if !is_reading(b) {
            // Incrementing borrow can result in a non-reading value (<= 0) in these cases:
            // 1. It was < 0, i.e. there are writing borrows, so we can't allow a read borrow
            //    due to Rust's reference aliasing rules
            // 2. It was isize::MAX (the max amount of reading borrows) and it overflowed
            //    into isize::MIN (the max amount of writing borrows) so we can't allow
            //    an additional read borrow because isize can't represent so many read borrows
            //    (this can only happen if you mem::forget more than a small constant amount of
            //    `UncheckedRef`s, which is not good practice)
            None
        } else {
            // Incrementing borrow can result in a reading value (> 0) in these cases:
            // 1. It was = 0, i.e. it wasn't borrowed, and we are taking the first read borrow
            // 2. It was > 0 and < isize::MAX, i.e. there were read borrows, and isize
            //    is large enough to represent having one more read borrow
            borrow.replace(b);
            Some(BorrowRef { borrow })
        }
    }
}

impl Drop for BorrowRef<'_> {
    #[inline]
    fn drop(&mut self) {
        let borrow = self.borrow.get();
        debug_assert!(is_reading(borrow));
        self.borrow.replace(borrow - 1);
    }
}

impl Clone for BorrowRef<'_> {
    #[inline]
    fn clone(&self) -> Self {
        // Since this Ref exists, we know the borrow flag
        // is a reading borrow.
        let borrow = self.borrow.get();
        debug_assert!(is_reading(borrow));
        // Prevent the borrow counter from overflowing into
        // a writing borrow.
        assert!(borrow != BorrowCounter::MAX);
        self.borrow.replace(borrow + 1);
        BorrowRef {
            borrow: self.borrow,
        }
    }
}

/// Wraps a borrowed reference to a value in a `RefCell` box.
/// A wrapper type for an immutably borrowed value from a `RefCell<T>`.
///
/// See the [module-level documentation](self) for more.
pub struct UncheckedRef<'b, T: ?Sized + 'b> {
    // NB: we use a pointer instead of `&'b T` to avoid `noalias` violations, because a
    // `UncheckedRef` argument doesn't hold immutability for its whole scope, only until it drops.
    // `NonNull` is also covariant over `T`, just like we would have with `&T`.
    value: NonNull<T>,
    #[cfg(any(feature = "checked", debug_assertions))]
    borrow: BorrowRef<'b>,
    #[cfg(not(any(feature = "checked", debug_assertions)))]
    marker: PhantomData<&'b ()>,
}

impl<T: ?Sized> Deref for UncheckedRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_ref() }
    }
}

impl<'b, T: ?Sized> UncheckedRef<'b, T> {
    /// Copies a `UncheckedRef`.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRef::clone(...)`. A `Clone` implementation or a method would interfere
    /// with the widespread use of `r.borrow().clone()` to clone the contents of
    /// a `RefCell`.
    #[must_use]
    #[inline]
    pub fn clone(orig: &UncheckedRef<'b, T>) -> UncheckedRef<'b, T> {
        UncheckedRef {
            value: orig.value,
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow.clone(),
            #[cfg(not(any(feature = "checked", debug_assertions)))]
            marker: PhantomData,
        }
    }

    /// Makes a new `UncheckedRef` for a component of the borrowed data.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as `UncheckedRef::map(...)`.
    /// A method would interfere with methods of the same name on the contents
    /// of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRef};
    ///
    /// let c = UncheckedRefCell::new((5, 'b'));
    /// let b1: UncheckedRef<'_, (u32, char)> = c.borrow();
    /// let b2: UncheckedRef<'_, u32> = UncheckedRef::map(b1, |t| &t.0);
    /// assert_eq!(*b2, 5)
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(orig: UncheckedRef<'b, T>, f: F) -> UncheckedRef<'b, U>
    where
        F: FnOnce(&T) -> &U,
    {
        UncheckedRef {
            value: NonNull::from(f(&*orig)),
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow,
            #[cfg(not(any(feature = "checked", debug_assertions)))]
            marker: PhantomData,
        }
    }

    /// Makes a new `UncheckedRef` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRef::filter_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRef};
    ///
    /// let c = UncheckedRefCell::new(vec![1, 2, 3]);
    /// let b1: UncheckedRef<'_, Vec<u32>> = c.borrow();
    /// let b2: Result<UncheckedRef<'_, u32>, _> = UncheckedRef::filter_map(b1, |v| v.get(1));
    /// assert_eq!(*b2.unwrap(), 2);
    /// ```
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: UncheckedRef<'b, T>, f: F) -> Result<UncheckedRef<'b, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        match f(&*orig) {
            Some(value) => Ok(UncheckedRef {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            }),
            None => Err(orig),
        }
    }

    /// Tries to makes a new `UncheckedRef` for a component of the borrowed data.
    /// On failure, the original guard is returned alongside with the error
    /// returned by the closure.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRef::try_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRef};
    /// use std::str::{from_utf8, Utf8Error};
    ///
    /// let c = UncheckedRefCell::new(vec![0xF0, 0x9F, 0xA6 ,0x80]);
    /// let b1: UncheckedRef<'_, Vec<u8>> = c.borrow();
    /// let b2: Result<UncheckedRef<'_, str>, _> = UncheckedRef::try_map(b1, |v| from_utf8(v));
    /// assert_eq!(&*b2.unwrap(), "🦀");
    ///
    /// let c = UncheckedRefCell::new(vec![0xF0, 0x9F, 0xA6]);
    /// let b1: UncheckedRef<'_, Vec<u8>> = c.borrow();
    /// let b2: Result<_, (UncheckedRef<'_, Vec<u8>>, Utf8Error)> = UncheckedRef::try_map(b1, |v| from_utf8(v));
    /// let (b3, e) = b2.unwrap_err();
    /// assert_eq!(*b3, vec![0xF0, 0x9F, 0xA6]);
    /// assert_eq!(e.valid_up_to(), 0);
    /// ```
    #[inline]
    pub fn try_map<U: ?Sized, E>(
        orig: UncheckedRef<'b, T>,
        f: impl FnOnce(&T) -> Result<&U, E>,
    ) -> Result<UncheckedRef<'b, U>, (Self, E)> {
        match f(&*orig) {
            Ok(value) => Ok(UncheckedRef {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            }),
            Err(e) => Err((orig, e)),
        }
    }

    /// Splits a `UncheckedRef` into multiple `UncheckedRef`s for different components of the
    /// borrowed data.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRef::map_split(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRef};
    ///
    /// let cell = UncheckedRefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow();
    /// let (begin, end) = UncheckedRef::map_split(borrow, |slice| slice.split_at(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// ```
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(orig: UncheckedRef<'b, T>, f: F) -> (UncheckedRef<'b, U>, UncheckedRef<'b, V>)
    where
        F: FnOnce(&T) -> (&U, &V),
    {
        let (a, b) = f(&*orig);
        #[cfg(any(feature = "checked", debug_assertions))]
        let borrow = orig.borrow.clone();
        (
            UncheckedRef {
                value: NonNull::from(a),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            },
            UncheckedRef {
                value: NonNull::from(b),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            },
        )
    }

    /// Converts into a reference to the underlying data.
    ///
    /// The underlying `RefCell` can never be mutably borrowed from again and will always appear
    /// already immutably borrowed. It is not a good idea to leak more than a constant number of
    /// references. The `RefCell` can be immutably borrowed again if only a smaller number of leaks
    /// have occurred in total.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRef::leak(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRef};
    /// let cell = UncheckedRefCell::new(0);
    ///
    /// let value = UncheckedRef::leak(cell.borrow());
    /// assert_eq!(*value, 0);
    ///
    /// assert!(cell.try_borrow().is_ok());
    /// assert!(cell.try_borrow_mut().is_err());
    /// ```
    pub fn leak(orig: UncheckedRef<'b, T>) -> &'b T {
        // By forgetting this Ref we ensure that the borrow counter in the RefCell can't go back to
        // UNUSED within the lifetime `'b`. Resetting the reference tracking state would require a
        // unique reference to the borrowed RefCell. No further mutable references can be created
        // from the original cell.
        #[cfg(any(feature = "checked", debug_assertions))]
        mem::forget(orig.borrow);
        // SAFETY: after forgetting, we can form a reference for the rest of lifetime `'b`.
        unsafe { orig.value.as_ref() }
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for UncheckedRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<'b, T: ?Sized> UncheckedRefMut<'b, T> {
    /// Makes a new `UncheckedRefMut` for a component of the borrowed data, e.g., an enum
    /// variant.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRefMut::map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRefMut};
    ///
    /// let c = UncheckedRefCell::new((5, 'b'));
    /// {
    ///     let b1: UncheckedRefMut<'_, (u32, char)> = c.borrow_mut();
    ///     let mut b2: UncheckedRefMut<'_, u32> = UncheckedRefMut::map(b1, |t| &mut t.0);
    ///     assert_eq!(*b2, 5);
    ///     *b2 = 42;
    /// }
    /// assert_eq!(*c.borrow(), (42, 'b'));
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(mut orig: UncheckedRefMut<'b, T>, f: F) -> UncheckedRefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let value = NonNull::from(f(&mut *orig));
        UncheckedRefMut {
            value,
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow,
            marker: PhantomData,
        }
    }

    /// Makes a new `UncheckedRefMut` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRefMut::filter_map(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRefMut};
    ///
    /// let c = UncheckedRefCell::new(vec![1, 2, 3]);
    ///
    /// {
    ///     let b1: UncheckedRefMut<'_, Vec<u32>> = c.borrow_mut();
    ///     let mut b2: Result<UncheckedRefMut<'_, u32>, _> = UncheckedRefMut::filter_map(b1, |v| v.get_mut(1));
    ///
    ///     if let Ok(mut b2) = b2 {
    ///         *b2 += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(*c.borrow(), vec![1, 4, 3]);
    /// ```
    #[inline]
    pub fn filter_map<U: ?Sized, F>(mut orig: UncheckedRefMut<'b, T>, f: F) -> Result<UncheckedRefMut<'b, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        // SAFETY: function holds onto an exclusive reference for the duration
        // of its call through `orig`, and the pointer is only de-referenced
        // inside of the function call never allowing the exclusive reference to
        // escape.
        match f(&mut *orig) {
            Some(value) => Ok(UncheckedRefMut {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                marker: PhantomData,
            }),
            None => Err(orig),
        }
    }

    /// Tries to makes a new `UncheckedRefMut` for a component of the borrowed data.
    /// On failure, the original guard is returned alongside with the error
    /// returned by the closure.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRefMut::try_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRefMut};
    /// use std::str::{from_utf8_mut, Utf8Error};
    ///
    /// let c = UncheckedRefCell::new(vec![0x68, 0x65, 0x6C, 0x6C, 0x6F]);
    /// {
    ///     let b1: UncheckedRefMut<'_, Vec<u8>> = c.borrow_mut();
    ///     let b2: Result<UncheckedRefMut<'_, str>, _> = UncheckedRefMut::try_map(b1, |v| from_utf8_mut(v));
    ///     let mut b2 = b2.unwrap();
    ///     assert_eq!(&*b2, "hello");
    ///     b2.make_ascii_uppercase();
    /// }
    /// assert_eq!(*c.borrow(), "HELLO".as_bytes());
    ///
    /// let c = UncheckedRefCell::new(vec![0xFF]);
    /// let b1: UncheckedRefMut<'_, Vec<u8>> = c.borrow_mut();
    /// let b2: Result<_, (UncheckedRefMut<'_, Vec<u8>>, Utf8Error)> = UncheckedRefMut::try_map(b1, |v| from_utf8_mut(v));
    /// let (b3, e) = b2.unwrap_err();
    /// assert_eq!(*b3, vec![0xFF]);
    /// assert_eq!(e.valid_up_to(), 0);
    /// ```
    #[inline]
    pub fn try_map<U: ?Sized, E>(
        mut orig: UncheckedRefMut<'b, T>,
        f: impl FnOnce(&mut T) -> Result<&mut U, E>,
    ) -> Result<UncheckedRefMut<'b, U>, (Self, E)> {
        // SAFETY: function holds onto an exclusive reference for the duration
        // of its call through `orig`, and the pointer is only de-referenced
        // inside of the function call never allowing the exclusive reference to
        // escape.
        match f(&mut *orig) {
            Ok(value) => Ok(UncheckedRefMut {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                marker: PhantomData,
            }),
            Err(e) => Err((orig, e)),
        }
    }

    /// Splits a `UncheckedRefMut` into multiple `UncheckedRefMut`s for different components of the
    /// borrowed data.
    ///
    /// The underlying `RefCell` will remain mutably borrowed until both
    /// returned `UncheckedRefMut`s go out of scope.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRefMut::map_split(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRefMut};
    ///
    /// let cell = UncheckedRefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow_mut();
    /// let (mut begin, mut end) = UncheckedRefMut::map_split(borrow, |slice| slice.split_at_mut(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// begin.copy_from_slice(&[4, 3]);
    /// end.copy_from_slice(&[2, 1]);
    /// ```
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(
        mut orig: UncheckedRefMut<'b, T>,
        f: F,
    ) -> (UncheckedRefMut<'b, U>, UncheckedRefMut<'b, V>)
    where
        F: FnOnce(&mut T) -> (&mut U, &mut V),
    {
        #[cfg(any(feature = "checked", debug_assertions))]
        let borrow = orig.borrow.clone();
        let (a, b) = f(&mut *orig);
        (
            UncheckedRefMut {
                value: NonNull::from(a),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow,
                marker: PhantomData,
            },
            UncheckedRefMut {
                value: NonNull::from(b),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                marker: PhantomData,
            },
        )
    }

    /// Converts into a mutable reference to the underlying data.
    ///
    /// The underlying `RefCell` can not be borrowed from again and will always appear already
    /// mutably borrowed, making the returned reference the only to the interior.
    ///
    /// This is an associated function that needs to be used as
    /// `UncheckedRefMut::leak(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use unchecked_refcell::{UncheckedRefCell, UncheckedRefMut};
    /// let cell = UncheckedRefCell::new(0);
    ///
    /// let value = UncheckedRefMut::leak(cell.borrow_mut());
    /// assert_eq!(*value, 0);
    /// *value = 1;
    ///
    /// assert!(cell.try_borrow_mut().is_err());
    /// ```
    pub fn leak(mut orig: UncheckedRefMut<'b, T>) -> &'b mut T {
        // By forgetting this BorrowRefMut we ensure that the borrow counter in the RefCell can't
        // go back to UNUSED within the lifetime `'b`. Resetting the reference tracking state would
        // require a unique reference to the borrowed RefCell. No further references can be created
        // from the original cell within that lifetime, making the current borrow the only
        // reference for the remaining lifetime.
        #[cfg(any(feature = "checked", debug_assertions))]
        mem::forget(orig.borrow);
        // SAFETY: after forgetting, we can form a reference for the rest of lifetime `'b`.
        unsafe { orig.value.as_mut() }
    }
}

struct BorrowRefMut<'b> {
    borrow: &'b Cell<BorrowCounter>,
}

impl Drop for BorrowRefMut<'_> {
    #[inline]
    fn drop(&mut self) {
        let borrow = self.borrow.get();
        debug_assert!(is_writing(borrow));
        self.borrow.replace(borrow + 1);
    }
}

impl<'b> BorrowRefMut<'b> {
    #[inline]
    const fn new(borrow: &'b Cell<BorrowCounter>) -> Option<BorrowRefMut<'b>> {
        // NOTE: Unlike BorrowRefMut::clone, new is called to create the initial
        // mutable reference, and so there must currently be no existing
        // references. Thus, while clone increments the mutable refcount, here
        // we explicitly only allow going from UNUSED to UNUSED - 1.
        match borrow.get() {
            UNUSED => {
                borrow.replace(UNUSED - 1);
                Some(BorrowRefMut { borrow })
            }
            _ => None,
        }
    }

    // Clones a `BorrowRefMut`.
    //
    // This is only valid if each `BorrowRefMut` is used to track a mutable
    // reference to a distinct, nonoverlapping range of the original object.
    // This isn't in a Clone impl so that code doesn't call this implicitly.
    #[inline]
    fn clone(&self) -> BorrowRefMut<'b> {
        let borrow = self.borrow.get();
        debug_assert!(is_writing(borrow));
        // Prevent the borrow counter from underflowing.
        assert!(borrow != BorrowCounter::MIN);
        self.borrow.set(borrow - 1);
        BorrowRefMut {
            borrow: self.borrow,
        }
    }
}

/// A wrapper type for a mutably borrowed value from a `RefCell<T>`.
///
/// See the [module-level documentation](self) for more.
pub struct UncheckedRefMut<'b, T: ?Sized + 'b> {
    // NB: we use a pointer instead of `&'b mut T` to avoid `noalias` violations, because a
    // `UncheckedRefMut` argument doesn't hold exclusivity for its whole scope, only until it drops.
    value: NonNull<T>,
    #[cfg(any(feature = "checked", debug_assertions))]
    borrow: BorrowRefMut<'b>,
    // `NonNull` is covariant over `T`, so we need to reintroduce invariance.
    marker: PhantomData<&'b mut T>,
}

impl<T: ?Sized> Deref for UncheckedRefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for UncheckedRefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_mut() }
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for UncheckedRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

//************************************************************************//

impl<T: ?Sized + Debug> Debug for UncheckedRefCell<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("RefCell");
        match self.try_borrow() {
            Ok(borrow) => d.field("value", &borrow),
            Err(_) => d.field("value", &format_args!("<borrowed>")),
        };
        d.finish()
    }
}

impl<T: ?Sized + Debug> Debug for UncheckedRef<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + Debug> Debug for UncheckedRefMut<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&*(self.deref()), f)
    }
}
