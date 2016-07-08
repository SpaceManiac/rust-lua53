extern crate lua;

#[test]
fn thread_test() {
    let mut root = lua::State::new();
    let mut lua = root.new_thread();
    lua.load_library(lua::Library::Io);
    lua.load_buffer(b"return (5 * 20) - 64", "");
    assert_eq!(lua.pcall(0, 1, 0), lua::ThreadStatus::Ok);
    assert_eq!(lua.to_integer(-1), (5 * 20) - 64);
}
