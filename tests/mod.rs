use std::cell::Cell;
use unchecked_refcell::{Ref, RefMut, UncheckedRefCell};

#[test]
fn ref_and_refmut_have_sensible_show() {
    let refcell = UncheckedRefCell::new("foo");

    let refcell_refmut = refcell.borrow_mut();
    assert_eq!(format!("{refcell_refmut}"), "foo"); // Display
    assert!(format!("{refcell_refmut:?}").contains("foo")); // Debug
    drop(refcell_refmut);

    let refcell_ref = refcell.borrow();
    assert_eq!(format!("{refcell_ref}"), "foo"); // Display
    assert!(format!("{refcell_ref:?}").contains("foo")); // Debug
    drop(refcell_ref);
}

#[test]
fn double_imm_borrow() {
    let x = UncheckedRefCell::new(0);
    let _b1 = x.borrow();
    x.borrow();
}

#[test]
fn no_mut_then_imm_borrow() {
    let x = UncheckedRefCell::new(0);
    let _b1 = x.borrow_mut();
    assert!(x.try_borrow().is_err());
}

#[test]
fn no_imm_then_borrow_mut() {
    let x = UncheckedRefCell::new(0);
    let _b1 = x.borrow();
    assert!(x.try_borrow_mut().is_err());
}

#[test]
fn no_double_borrow_mut() {
    let x = UncheckedRefCell::new(0);
    assert!(x.try_borrow().is_ok());
    let _b1 = x.borrow_mut();
    assert!(x.try_borrow().is_err());
}

#[test]
fn imm_release_borrow_mut() {
    let x = UncheckedRefCell::new(0);
    {
        let _b1 = x.borrow();
    }
    x.borrow_mut();
}

#[test]
fn mut_release_borrow_mut() {
    let x = UncheckedRefCell::new(0);
    {
        let _b1 = x.borrow_mut();
    }
    x.borrow();
}

#[test]
fn double_borrow_single_release_no_borrow_mut() {
    let x = UncheckedRefCell::new(0);
    let _b1 = x.borrow();
    {
        let _b2 = x.borrow();
    }
    assert!(x.try_borrow().is_ok());
    assert!(x.try_borrow_mut().is_err());
}

#[test]
#[should_panic]
fn discard_doesnt_unborrow() {
    let x = UncheckedRefCell::new(0);
    let _b = x.borrow();
    let _ = _b;
    let _b = x.borrow_mut();
}

#[test]
fn ref_clone_updates_flag() {
    let x = UncheckedRefCell::new(0);
    {
        let b1 = x.borrow();
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_err());
        {
            let _b2 = Ref::clone(&b1);
            assert!(x.try_borrow().is_ok());
            assert!(x.try_borrow_mut().is_err());
        }
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_err());
    }
    assert!(x.try_borrow().is_ok());
    assert!(x.try_borrow_mut().is_ok());
}

#[test]
fn ref_map_does_not_update_flag() {
    let x = UncheckedRefCell::new(Some(5));
    {
        let b1: Ref<'_, Option<u32>> = x.borrow();
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_err());
        {
            let b2: Ref<'_, u32> = Ref::map(b1, |o| o.as_ref().unwrap());
            assert_eq!(*b2, 5);
            assert!(x.try_borrow().is_ok());
            assert!(x.try_borrow_mut().is_err());
        }
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_ok());
    }
    assert!(x.try_borrow().is_ok());
    assert!(x.try_borrow_mut().is_ok());
}

#[test]
fn ref_map_split_updates_flag() {
    let x = UncheckedRefCell::new([1, 2]);
    {
        let b1 = x.borrow();
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_err());
        {
            let (_b2, _b3) = Ref::map_split(b1, |slc| slc.split_at(1));
            assert!(x.try_borrow().is_ok());
            assert!(x.try_borrow_mut().is_err());
        }
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_ok());
    }
    assert!(x.try_borrow().is_ok());
    assert!(x.try_borrow_mut().is_ok());

    {
        let b1 = x.borrow_mut();
        assert!(x.try_borrow().is_err());
        assert!(x.try_borrow_mut().is_err());
        {
            let (_b2, _b3) = RefMut::map_split(b1, |slc| slc.split_at_mut(1));
            assert!(x.try_borrow().is_err());
            assert!(x.try_borrow_mut().is_err());
            drop(_b2);
            assert!(x.try_borrow().is_err());
            assert!(x.try_borrow_mut().is_err());
        }
        assert!(x.try_borrow().is_ok());
        assert!(x.try_borrow_mut().is_ok());
    }
    assert!(x.try_borrow().is_ok());
    assert!(x.try_borrow_mut().is_ok());
}

#[test]
fn ref_map_split() {
    let x = UncheckedRefCell::new([1, 2]);
    let (b1, b2) = Ref::map_split(x.borrow(), |slc| slc.split_at(1));
    assert_eq!(*b1, [1]);
    assert_eq!(*b2, [2]);
}

#[test]
fn ref_mut_map_split() {
    let x = UncheckedRefCell::new([1, 2]);
    {
        let (mut b1, mut b2) = RefMut::map_split(x.borrow_mut(), |slc| slc.split_at_mut(1));
        assert_eq!(*b1, [1]);
        assert_eq!(*b2, [2]);
        b1[0] = 2;
        b2[0] = 1;
    }
    assert_eq!(*x.borrow(), [2, 1]);
}

#[test]
fn ref_map_accessor() {
    struct X(UncheckedRefCell<(u32, char)>);
    impl X {
        fn accessor(&self) -> Ref<'_, u32> {
            Ref::map(self.0.borrow(), |tuple| &tuple.0)
        }
    }
    let x = X(UncheckedRefCell::new((7, 'z')));
    let d: Ref<'_, u32> = x.accessor();
    assert_eq!(*d, 7);
}

#[test]
fn ref_mut_map_accessor() {
    struct X(UncheckedRefCell<(u32, char)>);
    impl X {
        fn accessor(&self) -> RefMut<'_, u32> {
            RefMut::map(self.0.borrow_mut(), |tuple| &mut tuple.0)
        }
    }
    let x = X(UncheckedRefCell::new((7, 'z')));
    {
        let mut d: RefMut<'_, u32> = x.accessor();
        assert_eq!(*d, 7);
        *d += 1;
    }
    assert_eq!(*x.0.borrow(), (8, 'z'));
}

#[test]
fn as_ptr() {
    let c1: Cell<usize> = Cell::new(0);
    c1.set(1);
    assert_eq!(1, unsafe { *c1.as_ptr() });

    let c2: Cell<usize> = Cell::new(0);
    unsafe {
        *c2.as_ptr() = 1;
    }
    assert_eq!(1, c2.get());

    let r1: UncheckedRefCell<usize> = UncheckedRefCell::new(0);
    *r1.borrow_mut() = 1;
    assert_eq!(1, unsafe { *r1.as_ptr() });

    let r2: UncheckedRefCell<usize> = UncheckedRefCell::new(0);
    unsafe {
        *r2.as_ptr() = 1;
    }
    assert_eq!(1, *r2.borrow());
}

#[test]
fn refcell_default() {
    let cell: UncheckedRefCell<u64> = Default::default();
    assert_eq!(0, *cell.borrow());
}

// #[test]
// fn refcell_unsized() {
//     let cell: &UncheckedRefCell<[i32]> = &UncheckedRefCell::new([1, 2, 3]);
//     {
//         let b = &mut *cell.borrow_mut();
//         b[0] = 4;
//         b[2] = 5;
//     }
//     let comp: &mut [i32] = &mut [4, 2, 5];
//     assert_eq!(&*cell.borrow(), comp);
// }

// #[test]
// fn refcell_ref_coercion() {
//     let cell: UncheckedRefCell<[i32; 3]> = UncheckedRefCell::new([1, 2, 3]);
//     {
//         let mut cellref: RefMut<'_, [i32; 3]> = cell.borrow_mut();
//         cellref[0] = 4;
//         let mut coerced: RefMut<'_, [i32]> = cellref;
//         coerced[2] = 5;
//     }
//     {
//         let comp: &mut [i32] = &mut [4, 2, 5];
//         let cellref: Ref<'_, [i32; 3]> = cell.borrow();
//         assert_eq!(&*cellref, comp);
//         let coerced: Ref<'_, [i32]> = cellref;
//         assert_eq!(&*coerced, comp);
//     }
// }

#[test]
#[should_panic]
fn refcell_swap_borrows() {
    let x = UncheckedRefCell::new(0);
    let _b = x.borrow();
    let y = UncheckedRefCell::new(1);
    x.swap(&y);
}

#[test]
#[should_panic]
fn refcell_replace_borrows() {
    let x = UncheckedRefCell::new(0);
    let _b = x.borrow();
    x.replace(1);
}

#[test]
fn refcell_format() {
    let name = UncheckedRefCell::new("rust");
    let what = UncheckedRefCell::new("rocks");
    let msg = format!("{name} {}", &*what.borrow(), name = &*name.borrow());
    assert_eq!(msg, "rust rocks".to_string());
}

// #[allow(dead_code)]
// fn const_cells() {
//     const UNSAFE_CELL: UnsafeCell<i32> = UnsafeCell::new(3);
//     const _: i32 = UNSAFE_CELL.into_inner();

//     const REF_CELL: UncheckedRefCell<i32> = UncheckedRefCell::new(3);
//     const _: i32 = REF_CELL.into_inner();

//     const CELL: Cell<i32> = Cell::new(3);
//     const _: i32 = CELL.into_inner();

//     /* FIXME(#110395)
//         const UNSAFE_CELL_FROM: UnsafeCell<i32> = UnsafeCell::from(3);
//         const _: i32 = UNSAFE_CELL.into_inner();

//         const REF_CELL_FROM: RefCell<i32> = UncheckedRefCell::from(3);
//         const _: i32 = REF_CELL.into_inner();

//         const CELL_FROM: Cell<i32> = Cell::from(3);
//         const _: i32 = CELL.into_inner();
//     */
// }

// #[test]
// fn refcell_borrow() {
//     // Check that `borrow` is usable at compile-time
//     const {
//         let a = UncheckedRefCell::new(0);
//         assert!(a.try_borrow().is_ok());
//         assert!(a.try_borrow_mut().is_ok());
//         let a_ref = a.borrow();
//         assert!(*a_ref == 0);
//         assert!(a.try_borrow().is_ok());
//         assert!(a.try_borrow_mut().is_err());
//     }
// }

// #[test]
// fn refcell_borrow_mut() {
//     // Check that `borrow_mut` is usable at compile-time
//     const {
//         let mut a = UncheckedRefCell::new(0);
//         {
//             assert!(a.try_borrow().is_ok());
//             assert!(a.try_borrow_mut().is_ok());
//             let mut a_ref = a.borrow_mut();
//             assert!(*a_ref == 0);
//             *a_ref = 10;
//             assert!(*a_ref == 10);
//             assert!(a.try_borrow().is_err());
//             assert!(a.try_borrow_mut().is_err());
//         }
//         assert!(*a.get_mut() == 10);
//     };
// }
// struct NeverDrop;
// impl Drop for NeverDrop {
//     fn drop(&mut self) {
//         panic!("should never be called");
//     }
// }

// #[test]
// fn refcell_replace() {
//     // Check that `replace` is usable at compile-time
//     const {
//         let a = UncheckedRefCell::new(0);
//         assert!(a.replace(10) == 0);
//         let a = a.into_inner();
//         assert!(a == 10);

//         let b = UncheckedRefCell::new(NeverDrop);
//         forget(b.replace(NeverDrop));
//         forget(b)
//     };
// }

// #[test]
// fn refcell_swap() {
//     // Check that `swap` is usable at compile-time
//     const {
//         let (a, b) = (UncheckedRefCell::new(31), UncheckedRefCell::new(41));
//         a.swap(&b);
//         let (a, b) = (a.into_inner(), b.into_inner());
//         assert!(a == 41);
//         assert!(b == 31);

//         let c = UncheckedRefCell::new(NeverDrop);
//         let d = UncheckedRefCell::new(NeverDrop);
//         c.swap(&d);
//         forget((c, d));
//     };
// }
