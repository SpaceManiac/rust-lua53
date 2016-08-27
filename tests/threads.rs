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
