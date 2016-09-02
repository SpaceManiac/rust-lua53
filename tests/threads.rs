extern crate lua;

macro_rules! check {
    ($l:expr, $e:expr) => {
        let s = $e;
        if s != lua::ThreadStatus::Ok {
            panic!("{:?}: {}", s, $l.to_str(-1).as_ref().map(|x| &**x).unwrap_or("<no message>"));
        }
    }
}

#[test]
fn thread_test() {
    let root = lua::State::new();
    let lua = root.new_thread();
    lua.open_libs();
    check!(lua, lua.load_buffer(b"return (5 * 20) - 64", ""));
    check!(lua, lua.pcall(0, 1, 0));
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
    check!(lua2, lua2.load_buffer(b"return 2 * 200", ""));
    check!(lua, lua.pcall(0, 0, 0));
}

#[test]
fn hell() {
    let lua = lua::Context::new();
    println!("<{}>", lua.get_top());
    let thread = lua.new_thread();
    println!("<{}>", lua.get_top());
    lua.xmove(&thread, 1);
    println!("<{}>", lua.get_top());
    lua.gc(lua::GcOption::Collect, 0);

    check!(thread, thread.load_buffer(b"return 2 * 200", ""));
    check!(thread, thread.pcall(0, 0, 0));
}

fn stuff(state: &lua::State) -> i32 {
    println!("in = {}", state.main_thread().get_top());
    0
}

#[test]
fn stack() {
    let ctx = lua::Context::new();
    ctx.push_bool(false);
    ctx.push_bool(false);
    ctx.push_bool(false);
    println!("top = {}", ctx.get_top());
    let thread2 = ctx.new_thread();
    thread2.push_fn(lua::wrap_fn(stuff));
    check!(thread2, thread2.pcall(0, 0, 0));
    println!("top = {}", ctx.get_top());
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
    assert_eq!(lua.to_str_in_place(-1).as_ref().map(|x| &**x), Some(string));
}

fn more_stuff(lua: &lua::State) -> i32 {
    let stack = lua.get_stack(1).expect("get_stack");
    println!("getlocal = {:?}", lua.get_local(Some(&stack), 1));
    lua.co_yield(0);
}

#[test]
fn getlocal() {
    let lua = lua::State::new();
    lua.push_fn(lua::wrap_fn(more_stuff));
    lua.set_global("foo");
    lua.open_libs();
    check!(lua, lua.load_buffer(b"local c = coroutine.create(function() local x = 5; foo(); end); coroutine.resume(c); return c", ""));
    check!(lua, lua.pcall(0, 1, 0));
    let thread = lua.to_thread(-1).unwrap();
    let name = thread.get_local(Some(&thread.get_stack(1).expect("get_stack")), 1);
    check!(lua, lua.load_buffer(b"coroutine.resume(...);", ""));
    lua.rotate(1, 1);
    check!(lua, lua.pcall(1, 0, 0));
    lua.gc(lua::GcOption::Collect, 0);
    println!("name is now: {:?}", name);
}
