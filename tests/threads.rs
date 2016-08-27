extern crate lua;

#[test]
fn thread_test() {
    let mut root = lua::State::new();
    let mut lua = root.new_thread();
    lua.open_libs();
    lua.load_buffer(b"return (5 * 20) - 64", "");
    assert_eq!(lua.pcall(0, 1, 0), lua::ThreadStatus::Ok);
    assert_eq!(lua.to_integer(-1), (5 * 20) - 64);
}

#[test]
fn atpanic() {
    let mut lua = lua::State::new();
    assert_eq!(lua.at_panic(None), None);
    assert_eq!(lua.at_panic(None), None);
}

#[test]
fn reference() {
    let string = "two hundred years";

    let mut lua = lua::State::new();
    lua.new_table();
    let top = lua.get_top();
    lua.push_string(string);
    let reference = lua.reference(top);
    assert_eq!(lua.get_top(), top);
    assert_eq!(lua.len_direct(top), 1);
    assert_eq!(lua.get_reference(top, reference), lua::Type::String);
    assert_eq!(lua.to_str_in_place(-1), Some(string));
}
