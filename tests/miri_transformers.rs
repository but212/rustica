#![cfg(miri)]

use rustica::transformers::ReaderT;

#[test]
fn reader_t_bind_owns_strings_without_aliasing_or_double_drop() {
    let reader: ReaderT<(), Option<String>, String> =
        ReaderT::new(|()| Some(String::from("owned")));
    let bound: ReaderT<(), Option<String>, String> =
        reader.bind(|value| ReaderT::new(move |()| Some(format!("{value}-next"))));

    assert_eq!(bound.run_reader(()), Some(String::from("owned-next")));
}
