extern crate lua;

struct ExtraData {
    value: String,
}

fn check(state: &lua::State) {
    let extra = ExtraData {
      value: "Initial data".to_string(),
    };

    assert!(state.get_extra().is_none());
    assert!(state.set_extra(None).is_none());

    state.set_extra(Some(Box::new(extra)));

    for x in 0..10 {
        let extra = state.get_extra()
            .and_then(|a| a.downcast_mut::<ExtraData>()).unwrap();
        extra.value = format!("Changed to {}", x);
    }

    {
        let extra = state.set_extra(None).unwrap();
        let extra = extra.downcast::<ExtraData>().unwrap();
        assert_eq!(extra.value, "Changed to 9");
    }

    assert!(state.get_extra().is_none());
    assert!(state.set_extra(None).is_none());
}

#[test]
fn basic_checks() {
    check(&lua::State::new());
}

#[test]
fn new_thread_rust() {
    let state = lua::State::new();
    state.set_extra(Some(Box::new(ExtraData {
        value: "Won't be shared!".to_string(),
    })));
    check(state.new_thread());
}

#[test]
fn new_thread_lua() {
    let lua = lua::State::new();
    lua.open_libs();
    lua.set_extra(Some(Box::new(ExtraData {
        value: "Won't be shared!".to_string(),
    })));
    assert_eq!(lua.load_buffer(b"return coroutine.create(function () end)", ""), lua::ThreadStatus::Ok);
    assert_eq!(lua.pcall(0, 1, 0), lua::ThreadStatus::Ok);
    let thread = lua.to_thread(-1).unwrap();
    check(thread);
}

#[test]
fn main_thread_unimpacted() {
    let state = lua::State::new();
    check(state.new_thread());
    assert!(state.get_extra().is_none());
}
