# Migration Guide: `AsyncM` to Native `async`/`await` (v0.17.0)

`AsyncM<A>` is deprecated in `v0.17.0` and scheduled for removal in `v0.18.0`.

## Rationale

Native `async`/`await` and `std::future::Future` supersede `AsyncM`:

1. **Zero-cost execution**: `AsyncM` allocates every step in a `Pin<Box<dyn Future>>` with dynamic dispatch. Native `async`/`await` compiles to a single state machine. Benchmarks show native async is **2.3x–6.1x faster** (chaining: ~137ns native vs ~834ns `AsyncM`).
2. **Standard composition**: Native futures integrate directly with runtime primitives (`tokio::select!`, `tokio::join!`, timeouts, cancellation tokens).
3. **Idiomatic syntax**: Rust uses `.await` over monadic `.bind()` / `.fmap()` chains for asynchronous control flow.

> **Note**: Combinators on `Validated` (`fmap_valid_async`, `fmap_invalid_async`) operate on standard `Future`s and remain fully supported.

---

## Migration Cheatsheet

| `AsyncM<A>` Pattern | Native Rust Equivalent |
| --- | --- |
| `AsyncM::pure(x)` / `AsyncM::new(async { x })` | `std::future::ready(x)` or `async move { x }` |
| `comp.fmap(\|x\| x + 1)` | `async move { comp.await + 1 }` |
| `comp.bind(\|x\| fetch(x))` | `async move { fetch(comp.await).await }` |
| `comp1.zip(comp2)` | `tokio::join!(comp1, comp2)` or `futures::join!(comp1, comp2)` |
| `comp1.zip_with(comp2, \|a, b\| ...)` | `async move { let (a, b) = tokio::join!(comp1, comp2); ...(a, b) }` |
| `comp.recover_with(\|e\| ...)` | `async move { match comp.await { Ok(v) => Ok(v), Err(e) => ...(e).await } }` |
| `comp.try_get()` | `comp.await` (or `runtime.block_on(comp)`) |

---

## Concrete Migration Examples

### 1. Sequential Chaining (`bind` / `fmap`)

#### Before (`AsyncM`)

```rust
use rustica::datatypes::async_monad::AsyncM;

async fn fetch_user_id() -> u32 { 42 }
async fn fetch_user_name(id: u32) -> String { format!("user_{id}") }

let program = AsyncM::new(fetch_user_id())
    .bind(|id| AsyncM::new(fetch_user_name(id)))
    .fmap(|name| name.to_uppercase());

let result = program.try_get().await;
assert_eq!(result, "USER_42");
```

#### After (Native `async`/`await`)

```rust
async fn fetch_user_id() -> u32 { 42 }
async fn fetch_user_name(id: u32) -> String { format!("user_{id}") }

let user_id = fetch_user_id().await;
let name = fetch_user_name(user_id).await;
let result = name.to_uppercase();

assert_eq!(result, "USER_42");
```

---

### 2. Concurrent Composition (`zip` / `zip_with`)

#### Before (`AsyncM`)

```rust
use rustica::datatypes::async_monad::AsyncM;

let a = AsyncM::pure(10);
let b = AsyncM::pure(20);
let combined = a.zip_with(b, |x, y| x + y);

let result = combined.try_get().await;
assert_eq!(result, 30);
```

#### After (`tokio::join!` or `futures::join!`)

```rust
let a = async { 10 };
let b = async { 20 };

let (val_a, val_b) = tokio::join!(a, b);
let result = val_a + val_b;

assert_eq!(result, 30);
```

---

### 3. Error Recovery (`recover_with`)

#### Before (`AsyncM`)

```rust
use rustica::datatypes::async_monad::AsyncM;

let failing = AsyncM::new(async { Err::<i32, &'static str>("failed") });
let recovered = failing.recover_with(|_err| AsyncM::pure(Ok(42)));

let result = recovered.try_get().await;
assert_eq!(result, Ok(42));
```

#### After (Native Result matching)

```rust
async fn do_work() -> Result<i32, &'static str> {
    Err("failed")
}

let result = match do_work().await {
    Ok(v) => Ok(v),
    Err(_err) => Ok(42),
};
assert_eq!(result, Ok(42));
```
