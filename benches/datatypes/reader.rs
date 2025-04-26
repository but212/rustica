use criterion::{black_box, Criterion};
use rustica::datatypes::id::Id;
use rustica::datatypes::reader::Reader;
use std::collections::BTreeMap;

/// Function to use all fields to avoid unused field warnings in benchmarks
#[allow(dead_code)]
fn use_all_fields(
    app_config: &AppConfig, cache_config: &CacheConfig, session_data: &SessionData,
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
#[derive(Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
struct AppConfig {
    api_key: String,
    base_url: String,
    timeout_ms: u32,
    max_retries: u32,
    debug_mode: bool,
    cache_settings: CacheConfig,
    feature_flags: BTreeMap<String, bool>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CacheConfig {
    enabled: bool,
    ttl_seconds: u32,
    max_size: usize,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
struct UserContext {
    user_id: String,
    permissions: Vec<String>,
    preferences: BTreeMap<String, String>,
    session_data: Option<SessionData>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct SessionData {
    session_id: String,
    created_at: u64,
    last_active: u64,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
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

    // Basic environment setup
    #[derive(Clone)]
    struct Config {
        multiplier: i32,
        prefix: String,
    }

    let basic_config = Config {
        multiplier: 10,
        prefix: "value: ".to_string(),
    };

    // Core operations benchmarks
    group.bench_function("create_and_run", |b| {
        b.iter(|| {
            let reader: Reader<Config, i32> = Reader::new(|cfg: Config| cfg.multiplier * 5);
            black_box(reader.run_reader(basic_config.clone()))
        })
    });

    group.bench_function("ask_operations", |b| {
        b.iter(|| {
            let reader1 = Reader::<Config, Config>::ask();
            let reader2 = Reader::<Config, i32>::asks(|cfg: Config| cfg.multiplier);
            let reader3 = Reader::<Config, String>::ask_with(
                |cfg: &Config| format!("Multiplier: {}", cfg.multiplier),
                Id::new,
            );

            black_box((
                reader1.run_reader(basic_config.clone()),
                reader2.run_reader(basic_config.clone()),
                reader3.run_reader(basic_config.clone()),
            ))
        })
    });

    // Functor and monad operations
    group.bench_function("transformation_operations", |b| {
        b.iter(|| {
            let reader = Reader::new(|cfg: Config| cfg.multiplier);

            let mapped = reader.fmap(|x: i32| Id::new(format!("Result: {}", x)));
            let bound = reader.bind(|x: i32| {
                Reader::new(move |cfg: Config| Id::new(format!("{}{}", cfg.prefix, x)))
            });

            black_box((
                mapped.run_reader(basic_config.clone()),
                bound.run_reader(basic_config.clone()),
            ))
        })
    });

    // Environment modification
    group.bench_function("environment_modification", |b| {
        b.iter(|| {
            let reader = Reader::new(|cfg: Config| Id::new(cfg.multiplier * 2));
            let local_reader = reader.local(|mut cfg: Config| {
                cfg.multiplier *= 3;
                cfg
            });

            black_box(local_reader.run_reader(basic_config.clone()))
        })
    });

    // Real-world environment setup
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
            let mut flags = BTreeMap::new();
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
            let mut prefs = BTreeMap::new();
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

    #[derive(Clone, PartialEq, Eq, Hash)]
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

    // Combined real-world use cases
    group.bench_function("real_world_use_cases", |b| {
        // Create readers once, outside the benchmark loop
        let build_request = Reader::<AppEnvironment, String>::ask_with(
            |env: &AppEnvironment| {
                let config = &env.config;
                format!(
                    "GET {}/users HTTP/1.1\nAuthorization: Bearer {}\nTimeout: {}",
                    config.base_url, config.api_key, config.timeout_ms
                )
            },
            Id::new,
        );

        let get_feature_flag = Reader::<AppEnvironment, bool>::ask_with(
            |env: &AppEnvironment| {
                let feature_enabled = env
                    .config
                    .feature_flags
                    .get("new_ui")
                    .cloned()
                    .unwrap_or(false);
                let user_has_permission = env.user.permissions.contains(&"read".to_string());
                feature_enabled && user_has_permission
            },
            Id::new,
        );

        let is_authenticated = Reader::<AppEnvironment, bool>::ask_with(
            |env: &AppEnvironment| env.user.session_data.is_some(),
            Id::new,
        );

        // Clone environment once
        let env = environment.clone();

        b.iter(|| {
            black_box((
                build_request.run_reader(env.clone()),
                get_feature_flag.run_reader(env.clone()),
                is_authenticated.run_reader(env.clone()),
            ))
        })
    });

    // Benchmark to compare memoized reader performance
    group.bench_function("real_world_use_cases_memoized", |b| {
        // Create readers once, outside the benchmark loop
        let build_request = Reader::<AppEnvironment, String>::ask_with(
            |env: &AppEnvironment| {
                let config = &env.config;
                format!(
                    "GET {}/users HTTP/1.1\nAuthorization: Bearer {}\nTimeout: {}",
                    config.base_url, config.api_key, config.timeout_ms
                )
            },
            Id::new,
        );

        let get_feature_flag = Reader::<AppEnvironment, bool>::ask_with(
            |env: &AppEnvironment| {
                let feature_enabled = env
                    .config
                    .feature_flags
                    .get("new_ui")
                    .cloned()
                    .unwrap_or(false);
                let user_has_permission = env.user.permissions.contains(&"read".to_string());
                feature_enabled && user_has_permission
            },
            Id::new,
        );

        let is_authenticated = Reader::<AppEnvironment, bool>::ask_with(
            |env: &AppEnvironment| env.user.session_data.is_some(),
            Id::new,
        );

        // Clone environment once
        let env = environment.clone();

        b.iter(|| {
            black_box((
                build_request.run_reader(env.clone()),
                get_feature_flag.run_reader(env.clone()),
                is_authenticated.run_reader(env.clone()),
            ))
        })
    });

    group.finish();
}
