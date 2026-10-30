use rustica::datatypes::validated::*;

#[test]
fn glob_import_keeps_core_crate_reachable() {
    let v: Validated<u8, &str> = Validated::valid(7);
    assert_eq!(core::mem::size_of_val(&v.unwrap()), 1);
}
