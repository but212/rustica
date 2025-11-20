use rustica::transformers::ReaderT;

#[test]
fn test_reader_t_creation_and_running() {
    // Create a ReaderT that doubles the environment value
    let reader_t: ReaderT<i32, Option<i32>, i32> = ReaderT::new(|env: i32| Some(env * 2));

    // Run with a specific environment
    let result = reader_t.run_reader(21);
    assert_eq!(result, Some(42));
}

#[test]
fn test_reader_t_composition() {
    // A reader that extracts a value from an environment
    let get_config_value: ReaderT<(i32, String), Option<i32>, i32> =
        ReaderT::new(|env: (i32, String)| Some(env.0));

    // Another reader that processes the environment's string
    let get_string_length: ReaderT<(i32, String), Option<usize>, usize> =
        ReaderT::new(|env: (i32, String)| Some(env.1.len()));

    // Combine both readers to perform a calculation
    let composed: ReaderT<(i32, String), Option<i32>, i32> =
        ReaderT::new(move |env: (i32, String)| {
            let value = get_config_value.run_reader(env.clone())?;
            let length = get_string_length.run_reader(env)? as i32;
            Some(value + length)
        });

    // Test the composed reader
    let result = composed.run_reader((40, "hello".to_string()));
    assert_eq!(result, Some(45)); // 40 + 5 = 45
}

#[test]
fn test_reader_t_standardized_error_handling() {
    // Create a ReaderT that may fail with division
    let safe_div: ReaderT<i32, Result<i32, String>, i32> = ReaderT::new(|n: i32| {
        if n == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(100 / n)
        }
    });

    // Test try_run_reader with success case
    let result = safe_div.try_run_reader(4);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 25); // 100/4 = 25

    // Test try_run_reader with error case
    let result = safe_div.try_run_reader(0);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().core_error(), "Division by zero");

    // Test try_run_reader_with_context with success case
    let result = safe_div.try_run_reader_with_context(4, "processing user input");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 25);

    // Test try_run_reader_with_context with error case
    let result = safe_div.try_run_reader_with_context(0, "processing user input");
    assert!(result.is_err());
    let error = result.unwrap_err();
    assert_eq!(error.core_error(), "Division by zero");
    assert_eq!(error.context(), vec!["processing user input".to_string()]);

    // Test map_error to transform error types
    let mapped = safe_div.map_error(|e: String| e.len() as i32);

    // The error is now the length of the original error string
    let result = mapped.run_reader(0);
    assert_eq!(result, Err(16)); // "Division by zero" has length 16

    // Success case still works
    let result = mapped.run_reader(5);
    assert_eq!(result, Ok(20)); // 100/5 = 20
}

#[test]
fn test_reader_t_with_complex_error_handling() {
    // Define a more complex environment type
    #[derive(Debug, Clone, PartialEq)]
    struct Config {
        debug_mode: bool,
        max_value: i32,
    }

    // Create a series of operations that might fail
    let validate_config: ReaderT<Config, Result<bool, String>, bool> =
        ReaderT::new(|cfg: Config| {
            if cfg.max_value <= 0 {
                Err("Max value must be positive".to_string())
            } else {
                Ok(true)
            }
        });

    let process_value: ReaderT<Config, Result<i32, String>, i32> = ReaderT::new(|cfg: Config| {
        if cfg.debug_mode {
            println!("Debug: Processing with max_value {}", cfg.max_value);
        }

        if cfg.max_value % 2 != 0 {
            Err("Cannot process odd max values".to_string())
        } else {
            Ok(cfg.max_value * 2)
        }
    });

    // Test validation with a valid config
    let valid_config = Config {
        debug_mode: false,
        max_value: 10,
    };
    let result = validate_config.try_run_reader(valid_config.clone());
    assert!(result.is_ok());
    assert!(result.unwrap());

    // Test validation with an invalid config
    let invalid_config = Config {
        debug_mode: true,
        max_value: 0,
    };
    let result = validate_config.try_run_reader(invalid_config.clone());
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().core_error(), "Max value must be positive");

    // Test processing with a valid config (even max_value)
    let result = process_value.try_run_reader(valid_config.clone());
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 20); // 10 * 2 = 20

    // Test processing with a config that has an odd max_value
    let odd_config = Config {
        debug_mode: false,
        max_value: 7,
    };
    let result = process_value.try_run_reader(odd_config);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().core_error(), "Cannot process odd max values");

    // Test with context for better error reporting
    let result =
        process_value.try_run_reader_with_context(valid_config, "performing number processing");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 20);
}
