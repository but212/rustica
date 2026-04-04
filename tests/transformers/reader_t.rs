use rustica::transformers::ReaderT;

#[test]
fn test_reader_t_lifecycle() {
    #[derive(Clone)]
    struct Env {
        factor: i32,
        prefix: String,
    }

    // 1. Basic creation and execution
    let get_val: ReaderT<Env, Option<i32>, i32> = ReaderT::new(|env: Env| Some(env.factor));
    let get_pref: ReaderT<Env, Option<usize>, usize> =
        ReaderT::new(|env: Env| Some(env.prefix.len()));

    // 2. Manual composition via closure (demonstrating environment sharing)
    let combined: ReaderT<Env, Option<i32>, i32> = ReaderT::new(move |env: Env| {
        let v = get_val.run_reader(env.clone())?;
        let l = get_pref.run_reader(env)? as i32;
        Some(v + l)
    });

    let env = Env {
        factor: 40,
        prefix: "hello".into(),
    };
    assert_eq!(combined.run_reader(env), Some(45));
}

#[test]
fn test_reader_t_error_ergonomics() {
    #[derive(Clone)]
    struct Config {
        max: i32,
    }

    let safe_proc: ReaderT<Config, Result<i32, String>, i32> = ReaderT::new(|cfg: Config| {
        if cfg.max <= 0 {
            Err("Invalid max".to_string())
        } else {
            Ok(cfg.max * 2)
        }
    });

    // 1. Success case with automatic Result conversion
    let res_ok = safe_proc.try_run_reader(Config { max: 10 });
    assert_eq!(res_ok.unwrap(), 20);

    // 2. Failure case with context attachment
    let res_err = safe_proc.try_run_reader_with_context(Config { max: 0 }, "init_service");
    match res_err {
        Err(e) => {
            assert_eq!(e.core_error(), "Invalid max");
            assert_eq!(e.context()[0], "init_service");
        },
        _ => panic!("Expected error"),
    }

    // 3. Error mapping (Result<A, E> -> Result<A, E2>)
    let mapped = safe_proc.map_error(|e: String| e.len());
    assert_eq!(mapped.run_reader(Config { max: 0 }), Err(11)); // "Invalid max" length is 11
}
