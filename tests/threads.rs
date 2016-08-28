extern crate lua;

#[test]
fn thread_test() {
    let root = lua::State::new();
    let lua = root.new_thread();
    lua.open_libs();
    assert_eq!(lua.load_buffer(b"return (5 * 20) - 64", ""), lua::ThreadStatus::Ok);
    assert_eq!(lua.pcall(0, 1, 0), lua::ThreadStatus::Ok);
    assert_eq!(lua.to_integer(-1), (5 * 20) - 64);
}

#[test]
fn main_thread_lookup() {
    let root = lua::State::new();
    root.raw_geti(lua::REGISTRYINDEX, lua::RIDX_MAINTHREAD);
    assert_eq!(root.as_ptr(), root.to_thread(-1).unwrap().as_ptr());
}

#[test]
fn overlapping_main_thread() {
    let ctx = lua::Context::new();
    let lua = ctx.main_thread();
    let lua2 = lua.main_thread();
    assert!(lua == lua2);
    lua.open_libs();
    assert_eq!(lua2.load_buffer(b"return 2 * 200", ""), lua::ThreadStatus::Ok);
    assert_eq!(lua.pcall(0, 0, 0), lua::ThreadStatus::Ok);
}

#[test]
fn atpanic() {
    let lua = lua::State::new();
    assert_eq!(lua.at_panic(None), None);
    assert_eq!(lua.at_panic(None), None);
}

#[test]
fn reference() {
    let string = "two hundred years";

    let lua = lua::State::new();
    lua.new_table();
    let top = lua.get_top();
    lua.push_string(string);
    let reference = lua.reference(top);
    assert_eq!(lua.get_top(), top);
    assert_eq!(lua.len_direct(top), 1);
    assert_eq!(lua.get_reference(top, reference), lua::Type::String);
    assert_eq!(lua.to_str_in_place(-1), Some(string));
}
