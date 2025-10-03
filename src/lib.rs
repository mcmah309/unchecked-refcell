use core::fmt;
use core::{
    cell::{Cell, UnsafeCell},
    cmp::Ordering,
    fmt::Display,
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

// Positive values represent the number of `Ref` active. Negative values
// represent the number of `RefMut` active. Multiple `RefMut`s can only be
// active at a time if they refer to distinct, nonoverlapping components of a
// `RefCell` (e.g., different ranges of a slice).
//
// `Ref` and `RefMut` are both two words in size, and so there will likely never
// be enough `Ref`s or `RefMut`s in existence to overflow half of the `usize`
// range. Thus, a `BorrowCounter` will probably never overflow or underflow.
// However, this is not a guarantee, as a pathological program could repeatedly
// create and then mem::forget `Ref`s or `RefMut`s. Thus, all code must
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    /// use std::cell::RefCell;
    /// let cell = RefCell::new(5);
    /// let old_value = cell.replace(6);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, RefCell::new(6));
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
    /// use std::cell::RefCell;
    /// let cell = RefCell::new(5);
    /// let old_value = cell.replace_with(|&mut old| old + 1);
    /// assert_eq!(old_value, 5);
    /// assert_eq!(cell, RefCell::new(6));
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
    /// use std::cell::RefCell;
    /// let c = RefCell::new(5);
    /// let d = RefCell::new(6);
    /// c.swap(&d);
    /// assert_eq!(c, RefCell::new(6));
    /// assert_eq!(d, RefCell::new(5));
    /// ```
    #[inline]
    pub fn swap(&self, other: &Self) {
        mem::swap(&mut *self.borrow_mut(), &mut *other.borrow_mut())
    }
}

impl<T: ?Sized> UncheckedRefCell<T> {
    /// Immutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `Ref` exits scope. Multiple
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
    ///
    /// let borrowed_five = c.borrow();
    /// let borrowed_five2 = c.borrow();
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
    ///
    /// let m = c.borrow_mut();
    /// let b = c.borrow(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow(&self) -> Ref<'_, T> {
        match self.try_borrow() {
            Ok(b) => b,
            Err(err) => panic_already_borrowed(err),
        }
    }

    /// Immutably borrows the wrapped value, returning an error if the value is currently mutably
    /// borrowed.
    ///
    /// The borrow lasts until the returned `Ref` exits scope. Multiple immutable borrows can be
    /// taken out at the same time.
    ///
    /// This is the non-panicking variant of [`borrow`](#method.borrow).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    pub fn try_borrow(&self) -> Result<Ref<'_, T>, BorrowError> {
        #[cfg(any(feature = "checked", debug_assertions))]
        match BorrowRef::new(&self.borrow) {
            Some(b) => {
                // SAFETY: `BorrowRef` ensures that there is only immutable access
                // to the value while borrowed.
                let value = unsafe { NonNull::new_unchecked(self.value.get()) };
                Ok(Ref { value, borrow: b })
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
            Ok(Ref {
                value,
                marker: PhantomData,
            })
        }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `RefMut` or all `RefMut`s derived
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new("hello".to_owned());
    ///
    /// *c.borrow_mut() = "bonjour".to_owned();
    ///
    /// assert_eq!(&*c.borrow(), "bonjour");
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
    /// let m = c.borrow();
    ///
    /// let b = c.borrow_mut(); // this causes a panic
    /// ```
    #[inline]
    #[track_caller]
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        match self.try_borrow_mut() {
            Ok(b) => b,
            Err(err) => panic_already_mutably_borrowed(err),
        }
    }

    /// Mutably borrows the wrapped value, returning an error if the value is currently borrowed.
    ///
    /// The borrow lasts until the returned `RefMut` or all `RefMut`s derived
    /// from it exit scope. The value cannot be borrowed while this borrow is
    /// active.
    ///
    /// This is the non-panicking variant of [`borrow_mut`](#method.borrow_mut).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    pub fn try_borrow_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
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
                    Ok(RefMut {
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
            Ok(RefMut {
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    /// (e.g., via [`forget()`] on a [`Ref`] or [`RefMut`]). For that purpose,
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
    /// [`borrow_mut`]: RefCell::borrow_mut()
    /// [`forget()`]: mem::forget
    /// [`undo_leak`]: RefCell::undo_leak()
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// let mut c = RefCell::new(5);
    /// *c.get_mut() += 1;
    ///
    /// assert_eq!(c, RefCell::new(6));
    /// ```
    #[inline]
    pub const fn get_mut(&mut self) -> &mut T {
        self.value.get_mut()
    }

    /// Undo the effect of leaked guards on the borrow state of the `RefCell`.
    ///
    /// This call is similar to [`get_mut`] but more specialized. It borrows `RefCell` mutably to
    /// ensure no borrows exist and then resets the state tracking shared borrows. This is relevant
    /// if some `Ref` or `RefMut` borrows have been leaked.
    ///
    /// [`get_mut`]: RefCell::get_mut()
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(cell_leak)]
    /// use std::cell::RefCell;
    ///
    /// let mut c = RefCell::new(0);
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
    /// return a `Ref`, thus leaving the borrow flag untouched. Mutably
    /// borrowing the `RefCell` while the reference returned by this method
    /// is alive is undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
    /// use std::cell::RefCell;
    ///
    /// let c = RefCell::new(5);
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
            //    `Ref`s, which is not good practice)
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
pub struct Ref<'b, T: ?Sized + 'b> {
    // NB: we use a pointer instead of `&'b T` to avoid `noalias` violations, because a
    // `Ref` argument doesn't hold immutability for its whole scope, only until it drops.
    // `NonNull` is also covariant over `T`, just like we would have with `&T`.
    value: NonNull<T>,
    #[cfg(any(feature = "checked", debug_assertions))]
    borrow: BorrowRef<'b>,
    #[cfg(not(any(feature = "checked", debug_assertions)))]
    marker: PhantomData<&'b ()>,
}

impl<T: ?Sized> Deref for Ref<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_ref() }
    }
}

impl<'b, T: ?Sized> Ref<'b, T> {
    /// Copies a `Ref`.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::clone(...)`. A `Clone` implementation or a method would interfere
    /// with the widespread use of `r.borrow().clone()` to clone the contents of
    /// a `RefCell`.
    #[must_use]
    #[inline]
    pub fn clone(orig: &Ref<'b, T>) -> Ref<'b, T> {
        Ref {
            value: orig.value,
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow.clone(),
            #[cfg(not(any(feature = "checked", debug_assertions)))]
            marker: PhantomData,
        }
    }

    /// Makes a new `Ref` for a component of the borrowed data.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as `Ref::map(...)`.
    /// A method would interfere with methods of the same name on the contents
    /// of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{RefCell, Ref};
    ///
    /// let c = RefCell::new((5, 'b'));
    /// let b1: Ref<'_, (u32, char)> = c.borrow();
    /// let b2: Ref<'_, u32> = Ref::map(b1, |t| &t.0);
    /// assert_eq!(*b2, 5)
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(orig: Ref<'b, T>, f: F) -> Ref<'b, U>
    where
        F: FnOnce(&T) -> &U,
    {
        Ref {
            value: NonNull::from(f(&*orig)),
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow,
            #[cfg(not(any(feature = "checked", debug_assertions)))]
            marker: PhantomData,
        }
    }

    /// Makes a new `Ref` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::filter_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{RefCell, Ref};
    ///
    /// let c = RefCell::new(vec![1, 2, 3]);
    /// let b1: Ref<'_, Vec<u32>> = c.borrow();
    /// let b2: Result<Ref<'_, u32>, _> = Ref::filter_map(b1, |v| v.get(1));
    /// assert_eq!(*b2.unwrap(), 2);
    /// ```
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: Ref<'b, T>, f: F) -> Result<Ref<'b, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        match f(&*orig) {
            Some(value) => Ok(Ref {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            }),
            None => Err(orig),
        }
    }

    /// Tries to makes a new `Ref` for a component of the borrowed data.
    /// On failure, the original guard is returned alongside with the error
    /// returned by the closure.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::try_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(refcell_try_map)]
    /// use std::cell::{RefCell, Ref};
    /// use std::str::{from_utf8, Utf8Error};
    ///
    /// let c = RefCell::new(vec![0xF0, 0x9F, 0xA6 ,0x80]);
    /// let b1: Ref<'_, Vec<u8>> = c.borrow();
    /// let b2: Result<Ref<'_, str>, _> = Ref::try_map(b1, |v| from_utf8(v));
    /// assert_eq!(&*b2.unwrap(), "🦀");
    ///
    /// let c = RefCell::new(vec![0xF0, 0x9F, 0xA6]);
    /// let b1: Ref<'_, Vec<u8>> = c.borrow();
    /// let b2: Result<_, (Ref<'_, Vec<u8>>, Utf8Error)> = Ref::try_map(b1, |v| from_utf8(v));
    /// let (b3, e) = b2.unwrap_err();
    /// assert_eq!(*b3, vec![0xF0, 0x9F, 0xA6]);
    /// assert_eq!(e.valid_up_to(), 0);
    /// ```
    #[inline]
    pub fn try_map<U: ?Sized, E>(
        orig: Ref<'b, T>,
        f: impl FnOnce(&T) -> Result<&U, E>,
    ) -> Result<Ref<'b, U>, (Self, E)> {
        match f(&*orig) {
            Ok(value) => Ok(Ref {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            }),
            Err(e) => Err((orig, e)),
        }
    }

    /// Splits a `Ref` into multiple `Ref`s for different components of the
    /// borrowed data.
    ///
    /// The `RefCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::map_split(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{Ref, RefCell};
    ///
    /// let cell = RefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow();
    /// let (begin, end) = Ref::map_split(borrow, |slice| slice.split_at(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// ```+>
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(orig: Ref<'b, T>, f: F) -> (Ref<'b, U>, Ref<'b, V>)
    where
        F: FnOnce(&T) -> (&U, &V),
    {
        let (a, b) = f(&*orig);
        #[cfg(any(feature = "checked", debug_assertions))]
        let borrow = orig.borrow.clone();
        (
            Ref {
                value: NonNull::from(a),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow,
                #[cfg(not(any(feature = "checked", debug_assertions)))]
                marker: PhantomData,
            },
            Ref {
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
    /// `Ref::leak(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(cell_leak)]
    /// use std::cell::{RefCell, Ref};
    /// let cell = RefCell::new(0);
    ///
    /// let value = Ref::leak(cell.borrow());
    /// assert_eq!(*value, 0);
    ///
    /// assert!(cell.try_borrow().is_ok());
    /// assert!(cell.try_borrow_mut().is_err());
    /// ```
    pub fn leak(orig: Ref<'b, T>) -> &'b T {
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

impl<T: ?Sized + fmt::Display> fmt::Display for Ref<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<'b, T: ?Sized> RefMut<'b, T> {
    /// Makes a new `RefMut` for a component of the borrowed data, e.g., an enum
    /// variant.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `RefMut::map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{RefCell, RefMut};
    ///
    /// let c = RefCell::new((5, 'b'));
    /// {
    ///     let b1: RefMut<'_, (u32, char)> = c.borrow_mut();
    ///     let mut b2: RefMut<'_, u32> = RefMut::map(b1, |t| &mut t.0);
    ///     assert_eq!(*b2, 5);
    ///     *b2 = 42;
    /// }
    /// assert_eq!(*c.borrow(), (42, 'b'));
    /// ```
    #[inline]
    pub fn map<U: ?Sized, F>(mut orig: RefMut<'b, T>, f: F) -> RefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let value = NonNull::from(f(&mut *orig));
        RefMut {
            value,
            #[cfg(any(feature = "checked", debug_assertions))]
            borrow: orig.borrow,
            marker: PhantomData,
        }
    }

    /// Makes a new `RefMut` for an optional component of the borrowed data. The
    /// original guard is returned as an `Err(..)` if the closure returns
    /// `None`.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `RefMut::filter_map(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{RefCell, RefMut};
    ///
    /// let c = RefCell::new(vec![1, 2, 3]);
    ///
    /// {
    ///     let b1: RefMut<'_, Vec<u32>> = c.borrow_mut();
    ///     let mut b2: Result<RefMut<'_, u32>, _> = RefMut::filter_map(b1, |v| v.get_mut(1));
    ///
    ///     if let Ok(mut b2) = b2 {
    ///         *b2 += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(*c.borrow(), vec![1, 4, 3]);
    /// ```
    #[inline]
    pub fn filter_map<U: ?Sized, F>(mut orig: RefMut<'b, T>, f: F) -> Result<RefMut<'b, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        // SAFETY: function holds onto an exclusive reference for the duration
        // of its call through `orig`, and the pointer is only de-referenced
        // inside of the function call never allowing the exclusive reference to
        // escape.
        match f(&mut *orig) {
            Some(value) => Ok(RefMut {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                marker: PhantomData,
            }),
            None => Err(orig),
        }
    }

    /// Tries to makes a new `RefMut` for a component of the borrowed data.
    /// On failure, the original guard is returned alongside with the error
    /// returned by the closure.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `RefMut::try_map(...)`. A method would interfere with methods of the same
    /// name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(refcell_try_map)]
    /// use std::cell::{RefCell, RefMut};
    /// use std::str::{from_utf8_mut, Utf8Error};
    ///
    /// let c = RefCell::new(vec![0x68, 0x65, 0x6C, 0x6C, 0x6F]);
    /// {
    ///     let b1: RefMut<'_, Vec<u8>> = c.borrow_mut();
    ///     let b2: Result<RefMut<'_, str>, _> = RefMut::try_map(b1, |v| from_utf8_mut(v));
    ///     let mut b2 = b2.unwrap();
    ///     assert_eq!(&*b2, "hello");
    ///     b2.make_ascii_uppercase();
    /// }
    /// assert_eq!(*c.borrow(), "HELLO".as_bytes());
    ///
    /// let c = RefCell::new(vec![0xFF]);
    /// let b1: RefMut<'_, Vec<u8>> = c.borrow_mut();
    /// let b2: Result<_, (RefMut<'_, Vec<u8>>, Utf8Error)> = RefMut::try_map(b1, |v| from_utf8_mut(v));
    /// let (b3, e) = b2.unwrap_err();
    /// assert_eq!(*b3, vec![0xFF]);
    /// assert_eq!(e.valid_up_to(), 0);
    /// ```
    #[inline]
    pub fn try_map<U: ?Sized, E>(
        mut orig: RefMut<'b, T>,
        f: impl FnOnce(&mut T) -> Result<&mut U, E>,
    ) -> Result<RefMut<'b, U>, (Self, E)> {
        // SAFETY: function holds onto an exclusive reference for the duration
        // of its call through `orig`, and the pointer is only de-referenced
        // inside of the function call never allowing the exclusive reference to
        // escape.
        match f(&mut *orig) {
            Ok(value) => Ok(RefMut {
                value: NonNull::from(value),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow: orig.borrow,
                marker: PhantomData,
            }),
            Err(e) => Err((orig, e)),
        }
    }

    /// Splits a `RefMut` into multiple `RefMut`s for different components of the
    /// borrowed data.
    ///
    /// The underlying `RefCell` will remain mutably borrowed until both
    /// returned `RefMut`s go out of scope.
    ///
    /// The `RefCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `RefMut::map_split(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::{RefCell, RefMut};
    ///
    /// let cell = RefCell::new([1, 2, 3, 4]);
    /// let borrow = cell.borrow_mut();
    /// let (mut begin, mut end) = RefMut::map_split(borrow, |slice| slice.split_at_mut(2));
    /// assert_eq!(*begin, [1, 2]);
    /// assert_eq!(*end, [3, 4]);
    /// begin.copy_from_slice(&[4, 3]);
    /// end.copy_from_slice(&[2, 1]);
    /// ```
    #[inline]
    pub fn map_split<U: ?Sized, V: ?Sized, F>(
        mut orig: RefMut<'b, T>,
        f: F,
    ) -> (RefMut<'b, U>, RefMut<'b, V>)
    where
        F: FnOnce(&mut T) -> (&mut U, &mut V),
    {
        #[cfg(any(feature = "checked", debug_assertions))]
        let borrow = orig.borrow.clone();
        let (a, b) = f(&mut *orig);
        (
            RefMut {
                value: NonNull::from(a),
                #[cfg(any(feature = "checked", debug_assertions))]
                borrow,
                marker: PhantomData,
            },
            RefMut {
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
    /// `RefMut::leak(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefCell` used through `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(cell_leak)]
    /// use std::cell::{RefCell, RefMut};
    /// let cell = RefCell::new(0);
    ///
    /// let value = RefMut::leak(cell.borrow_mut());
    /// assert_eq!(*value, 0);
    /// *value = 1;
    ///
    /// assert!(cell.try_borrow_mut().is_err());
    /// ```
    pub fn leak(mut orig: RefMut<'b, T>) -> &'b mut T {
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
pub struct RefMut<'b, T: ?Sized + 'b> {
    // NB: we use a pointer instead of `&'b mut T` to avoid `noalias` violations, because a
    // `RefMut` argument doesn't hold exclusivity for its whole scope, only until it drops.
    value: NonNull<T>,
    #[cfg(any(feature = "checked", debug_assertions))]
    borrow: BorrowRefMut<'b>,
    // `NonNull` is covariant over `T`, so we need to reintroduce invariance.
    marker: PhantomData<&'b mut T>,
}

impl<T: ?Sized> Deref for RefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for RefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the value is accessible as long as we hold our borrow.
        unsafe { self.value.as_mut() }
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for RefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}
