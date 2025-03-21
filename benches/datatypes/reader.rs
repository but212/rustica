use criterion::{black_box, Criterion};
use rustica::datatypes::reader::Reader;
use std::collections::HashMap;

/// Function to use all fields to avoid unused field warnings in benchmarks
#[allow(dead_code)]
fn use_all_fields(
    app_config: &AppConfig,
    cache_config: &CacheConfig,
    session_data: &SessionData,
) -> String {
    // Get a reference to cache_settings to mark it as used
    let _cache_ref = &app_config.cache_settings;

    format!(
        "Config: api_key={}, base_url={}, timeout_ms={}, max_retries={}, debug_mode={}, \
         cache: enabled={}, ttl={}, max_size={}, \
         session: id={}, created={}, last_active={}",
        app_config.api_key,
        app_config.base_url,
        app_config.timeout_ms,
        app_config.max_retries,
        app_config.debug_mode,
        cache_config.enabled,
        cache_config.ttl_seconds,
        cache_config.max_size,
        session_data.session_id,
        session_data.created_at,
        session_data.last_active
    )
}

/// Complex environment for real-world use cases
#[derive(Clone)]
#[allow(dead_code)]
struct AppConfig {
    api_key: String,
    base_url: String,
    timeout_ms: u32,
    max_retries: u32,
    debug_mode: bool,
    cache_settings: CacheConfig,
    feature_flags: HashMap<String, bool>,
}

#[derive(Clone)]
struct CacheConfig {
    enabled: bool,
    ttl_seconds: u32,
    max_size: usize,
}

#[derive(Clone)]
struct UserContext {
    user_id: String,
    permissions: Vec<String>,
    preferences: HashMap<String, String>,
    session_data: Option<SessionData>,
}

#[derive(Clone)]
struct SessionData {
    session_id: String,
    created_at: u64,
    last_active: u64,
}

#[derive(Clone)]
struct DatabaseConfig {
    host: String,
    port: u16,
    username: String,
    password: String,
    database: String,
    pool_size: u32,
}

pub fn reader_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Reader");

    // ======== BASIC OPERATIONS ========

    // Define a simple environment
    #[derive(Clone)]
    struct Config {
        multiplier: i32,
        prefix: String,
    }

    let basic_config = Config {
        multiplier: 10,
        prefix: "value: ".to_string(),
    };

    // Benchmark for creating and running a basic reader
    group.bench_function("create_and_run", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier * 5);
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    // ======== CORE OPERATIONS ========

    // Benchmark for the ask operation
    group.bench_function("ask", |b| {
        b.iter(|| {
            let reader: Reader<Config, Config> = Reader::<Config, Config>::ask();
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for the asks operation
    group.bench_function("asks", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> =
                Reader::<Config, i32>::asks(|cfg: Config| cfg.multiplier);
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for the ask_with operation
    group.bench_function("ask_with", |b| {
        b.iter(|| {
            let reader: Reader<Config, String> =
                Reader::<Config, String>::ask_with(|cfg: &Config| {
                    format!("Multiplier: {}", cfg.multiplier)
                });
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for the asks_with operation
    group.bench_function("asks_with", |b| {
        b.iter(|| {
            let reader: Reader<Config, String> = Reader::<Config, String>::asks_with(
                |cfg: &Config| cfg.multiplier,
                |m: i32| format!("Multiplier is {}", m),
            );
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    // ======== FUNCTOR OPERATIONS ========

    // Benchmark for fmap operation
    group.bench_function("fmap", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);
            let mapped: Reader<Config, String> = reader.fmap(|x: i32| format!("Result: {}", x));
            black_box(mapped.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for chained fmap operations
    group.bench_function("fmap_chain", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);
            let mapped: Reader<Config, String> = reader
                .fmap(|x: i32| x * 2)
                .fmap(|x: i32| x + 5)
                .fmap(|x: i32| format!("Result after operations: {}", x));
            black_box(mapped.run_reader(basic_config.clone()))
        })
    });

    // ======== APPLICATIVE OPERATIONS ========

    // Benchmark for combine operation
    group.bench_function("combine", |b| {
        b.iter(|| {
            let reader1: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);
            let reader2: Reader<Config, String> = Reader::new(|cfg: Config| cfg.prefix.clone());

            let combined: Reader<Config, String> =
                reader1.combine(&reader2, |x: i32, s: String| format!("{}{}", s, x));

            black_box(combined.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for lift2 operation
    group.bench_function("lift2", |b| {
        b.iter(|| {
            let reader1: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);
            let reader2: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier + 5);

            let lift_fn = Reader::lift2(|x: i32, y: i32| x + y);
            let result: Reader<Config, i32> = lift_fn(&reader1, &reader2);

            black_box(result.run_reader(basic_config.clone()))
        })
    });

    // ======== MONAD OPERATIONS ========

    // Benchmark for bind operation
    group.bench_function("bind", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);

            let bound: Reader<Config, String> = reader
                .bind(|x: i32| Reader::new(move |cfg: Config| format!("{}{}", cfg.prefix, x)));

            black_box(bound.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for chained bind operations
    group.bench_function("bind_chain", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);

            let bound: Reader<Config, String> = reader
                .bind(|x: i32| Reader::new(move |_: Config| x * 2))
                .bind(|x: i32| Reader::new(move |cfg: Config| format!("{}{}", cfg.prefix, x)));

            black_box(bound.run_reader(basic_config.clone()))
        })
    });

    // ======== ENVIRONMENT MODIFICATION ========

    // Benchmark for local operation
    group.bench_function("local", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier * 2);

            let local_reader: Reader<Config, i32> = reader.local(|mut cfg: Config| {
                cfg.multiplier *= 3;
                cfg
            });

            black_box(local_reader.run_reader(basic_config.clone()))
        })
    });

    // Benchmark for nested local operations
    group.bench_function("nested_local", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier);

            let local1: Reader<Config, i32> = reader.local(|mut cfg: Config| {
                cfg.multiplier *= 2;
                cfg
            });

            let local2: Reader<Config, i32> = local1.local(|mut cfg: Config| {
                cfg.multiplier += 5;
                cfg
            });

            black_box(local2.run_reader(basic_config.clone()))
        })
    });

    // ======== REAL-WORLD USE CASES ========

    // Setup for real-world use cases
    let app_config = AppConfig {
        api_key: "api_key_12345".to_string(),
        base_url: "https://api.example.com".to_string(),
        timeout_ms: 5000,
        max_retries: 3,
        debug_mode: false,
        cache_settings: CacheConfig {
            enabled: true,
            ttl_seconds: 3600,
            max_size: 1000,
        },
        feature_flags: {
            let mut flags = HashMap::new();
            flags.insert("new_ui".to_string(), true);
            flags.insert("analytics".to_string(), true);
            flags.insert("experimental".to_string(), false);
            flags
        },
    };

    let user_context = UserContext {
        user_id: "user123".to_string(),
        permissions: vec!["read".to_string(), "write".to_string()],
        preferences: {
            let mut prefs = HashMap::new();
            prefs.insert("theme".to_string(), "dark".to_string());
            prefs.insert("language".to_string(), "en".to_string());
            prefs
        },
        session_data: Some(SessionData {
            session_id: "session_456".to_string(),
            created_at: 1647515427,
            last_active: 1647518427,
        }),
    };

    // Combined environment for real-world use cases
    #[derive(Clone)]
    struct AppEnvironment {
        config: AppConfig,
        user: UserContext,
        db_config: Option<DatabaseConfig>,
    }

    let environment = AppEnvironment {
        config: app_config,
        user: user_context,
        db_config: Some(DatabaseConfig {
            host: "localhost".to_string(),
            port: 5432,
            username: "admin".to_string(),
            password: "password".to_string(),
            database: "app_db".to_string(),
            pool_size: 10,
        }),
    };

    // Use case 1: API request construction
    group.bench_function("use_case_api_request", |b| {
        b.iter(|| {
            // Reader that builds API request URL with proper authentication
            let build_request: Reader<AppEnvironment, String> =
                Reader::<AppEnvironment, String>::ask_with(|env: &AppEnvironment| {
                    let config = &env.config;
                    let endpoint = "/users";
                    let url = format!("{}{}", config.base_url, endpoint);
                    let auth_header = format!("Bearer {}", config.api_key);
                    format!(
                        "GET {} HTTP/1.1\nAuthorization: {}\nTimeout: {}",
                        url, auth_header, config.timeout_ms
                    )
                });

            black_box(build_request.run_reader(environment.clone()))
        })
    });

    // Use case 2: Feature flag checking with user context
    group.bench_function("use_case_feature_flag_check", |b| {
        b.iter(|| {
            // Create readers for extracting configuration data
            let get_feature_flag: Reader<AppEnvironment, bool> =
                Reader::<AppEnvironment, bool>::asks_with(
                    |env: &AppEnvironment| (env.config.clone(), env.user.clone()),
                    |(config, user): (AppConfig, UserContext)| {
                        // Check if feature is enabled globally
                        let feature_enabled =
                            config.feature_flags.get("new_ui").cloned().unwrap_or(false);

                        // Check if user has permission to access the feature
                        let user_has_permission = user.permissions.contains(&"read".to_string());

                        // Only show feature if both conditions are met
                        feature_enabled && user_has_permission
                    },
                );

            black_box(get_feature_flag.run_reader(environment.clone()))
        })
    });

    // Use case 3: Database operations with environment modification
    group.bench_function("use_case_db_operations", |b| {
        b.iter(|| {
            // Base reader that gets DB connection info
            let get_db_connection: Reader<AppEnvironment, Result<String, String>> =
                Reader::<AppEnvironment, Result<String, String>>::ask_with(
                    |env: &AppEnvironment| {
                        env.db_config
                            .as_ref()
                            .map(|db| {
                                format!(
                                    "postgresql://{}:{}@{}:{}/{}?pool_size={}",
                                    db.username,
                                    db.password,
                                    db.host,
                                    db.port,
                                    db.database,
                                    db.pool_size
                                )
                            })
                            .ok_or_else(|| "Database configuration not found".to_string())
                    },
                );

            // Reader for a transaction with modified timeout
            let run_transaction: Reader<AppEnvironment, Result<String, String>> = get_db_connection
                .bind(|conn_result: Result<String, String>| {
                    // 캡처된 변수에 불변 참조만 사용하는 함수 생성
                    let result_fn =
                        move |conn_result: &Result<String, String>| -> Result<String, String> {
                            conn_result
                                .as_ref()
                                .map(|conn| format!("Executed query on connection: {}", conn))
                                .map_err(|e| e.clone())
                        };

                    Reader::new(move |_: AppEnvironment| {
                        // 클로저에서 conn_result를 불변 참조로만 사용
                        result_fn(&conn_result)
                    })
                })
                .local(|mut env: AppEnvironment| {
                    // Modify the environment to use a longer timeout for DB operations
                    if let Some(ref mut db) = env.db_config {
                        db.pool_size = 20; // Increase connection pool size
                    }
                    env
                });

            black_box(run_transaction.run_reader(environment.clone()))
        })
    });

    // Use case 4: User authentication and permission checking
    group.bench_function("use_case_auth_flow", |b| {
        b.iter(|| {
            // Check if user is authenticated
            let is_authenticated: Reader<AppEnvironment, bool> =
                Reader::<AppEnvironment, bool>::ask_with(|env: &AppEnvironment| {
                    env.user.session_data.is_some()
                });

            // Check if user has required permission
            let has_permission: Reader<AppEnvironment, bool> =
                Reader::<AppEnvironment, bool>::ask_with(|env: &AppEnvironment| {
                    env.user.permissions.contains(&"write".to_string())
                });

            // Combine authentication and permission check
            let can_access: Reader<AppEnvironment, bool> = is_authenticated
                .combine(&has_permission, |authed: bool, has_perm: bool| {
                    authed && has_perm
                });

            // Add logging in debug mode
            let with_logging: Reader<AppEnvironment, String> =
                can_access.bind(|can_access: bool| {
                    Reader::<AppEnvironment, String>::ask_with(move |env: &AppEnvironment| {
                        let user_id = &env.user.user_id;
                        let result = if can_access {
                            format!("User {} granted access", user_id)
                        } else {
                            format!("User {} denied access", user_id)
                        };

                        // Add extra debug info if in debug mode
                        if env.config.debug_mode {
                            format!(
                                "{} [DEBUG: authenticated={}, has_permission={}]",
                                result,
                                env.user.session_data.is_some(),
                                env.user.permissions.contains(&"write".to_string())
                            )
                        } else {
                            result
                        }
                    })
                });

            black_box(with_logging.run_reader(environment.clone()))
        })
    });

    // Use case 5: Complex configuration transformation
    group.bench_function("use_case_config_transformation", |b| {
        b.iter(|| {
            // Extract and transform multiple config values
            let transform_config: Reader<AppEnvironment, HashMap<String, String>> =
                Reader::<AppEnvironment, HashMap<String, String>>::ask_with(
                    |env: &AppEnvironment| {
                        let config = &env.config;
                        let user = &env.user;

                        let mut result = HashMap::new();

                        // Add base configuration
                        result.insert(
                            "api_endpoint".to_string(),
                            format!("{}/api", config.base_url),
                        );
                        result.insert("timeout".to_string(), config.timeout_ms.to_string());

                        // Add user preferences
                        for (key, value) in &user.preferences {
                            result.insert(format!("pref_{}", key), value.clone());
                        }

                        // Add feature flags the user can access
                        for (feature, enabled) in &config.feature_flags {
                            if *enabled && user.permissions.contains(&"read".to_string()) {
                                result
                                    .insert(format!("feature_{}", feature), "enabled".to_string());
                            }
                        }

                        result
                    },
                );

            black_box(transform_config.run_reader(environment.clone()))
        })
    });

    group.finish();
}
