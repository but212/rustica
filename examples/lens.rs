//! Lens Usage Example
//!
//! Demonstrates bidirectional functional accessors (optics) for product types:
//! - Viewing, updating, and modifying fields immutably
//! - Composing lenses to navigate and modify deeply nested structures
//! - Structural sharing when updates result in identical values
//! - Bidirectional type mapping (`fmap`)

use rustica::datatypes::lens::Lens;

#[derive(Clone, Debug, PartialEq)]
struct Theme {
    mode: String,
    font_size: u32,
}

#[derive(Clone, Debug, PartialEq)]
struct Settings {
    theme: Theme,
    notifications_enabled: bool,
}

#[derive(Clone, Debug, PartialEq)]
struct UserProfile {
    name: String,
    settings: Settings,
}

const fn theme_mode_lens()
-> Lens<Theme, String, impl Fn(&Theme) -> String + Clone, impl Fn(Theme, String) -> Theme + Clone> {
    Lens::new(|t: &Theme| t.mode.clone(), |t, mode| Theme { mode, ..t })
}

const fn theme_font_size_lens()
-> Lens<Theme, u32, impl Fn(&Theme) -> u32 + Clone, impl Fn(Theme, u32) -> Theme + Clone> {
    Lens::new(
        |t: &Theme| t.font_size,
        |t, font_size| Theme { font_size, ..t },
    )
}

const fn settings_theme_lens() -> Lens<
    Settings,
    Theme,
    impl Fn(&Settings) -> Theme + Clone,
    impl Fn(Settings, Theme) -> Settings + Clone,
> {
    Lens::new(
        |s: &Settings| s.theme.clone(),
        |s, theme| Settings { theme, ..s },
    )
}

const fn user_settings_lens() -> Lens<
    UserProfile,
    Settings,
    impl Fn(&UserProfile) -> Settings + Clone,
    impl Fn(UserProfile, Settings) -> UserProfile + Clone,
> {
    Lens::new(
        |u: &UserProfile| u.settings.clone(),
        |u, settings| UserProfile { settings, ..u },
    )
}

fn main() {
    println!("=== Rustica Lens Example ===\n");

    let initial_user = UserProfile {
        name: "Alice".to_string(),
        settings: Settings {
            theme: Theme {
                mode: "light".to_string(),
                font_size: 14,
            },
            notifications_enabled: true,
        },
    };

    // Stage 1: Basic View, Set, and Modify on shallow structures
    println!("1. Basic Field Access and Modification:");
    let mode_lens = theme_mode_lens();
    let theme = initial_user.settings.theme.clone();

    let current_mode = mode_lens.get(&theme);
    println!("  Current theme mode: {}", current_mode);
    assert_eq!(current_mode, "light");

    let dark_theme = mode_lens.set(theme.clone(), "dark".to_string());
    println!("  Updated mode: {}", dark_theme.mode);
    assert_eq!(dark_theme.mode, "dark");
    assert_eq!(dark_theme.font_size, 14); // Preserves other fields

    let larger_font_theme = theme_font_size_lens().modify(theme, |size| size + 2);
    println!("  Modified font size: {}", larger_font_theme.font_size);
    assert_eq!(larger_font_theme.font_size, 16);

    println!();

    // Stage 2: Deep Composition with `then`
    println!("2. Composing Lenses for Deep Nested Updates:");
    // UserProfile -> Settings -> Theme -> font_size
    let user_font_lens = user_settings_lens()
        .then(settings_theme_lens())
        .then(theme_font_size_lens());

    let original_font = user_font_lens.get(&initial_user);
    println!("  Directly fetched nested font size: {}", original_font);
    assert_eq!(original_font, 14);

    let updated_user = user_font_lens.set(initial_user.clone(), 18);
    println!(
        "  Updated nested font size: {}",
        updated_user.settings.theme.font_size
    );
    assert_eq!(updated_user.settings.theme.font_size, 18);
    assert_eq!(updated_user.name, "Alice");
    assert!(updated_user.settings.notifications_enabled);

    let bumped_user = user_font_lens.modify(updated_user, |size| size + 2);
    println!(
        "  Bumped nested font size via modify: {}",
        bumped_user.settings.theme.font_size
    );
    assert_eq!(bumped_user.settings.theme.font_size, 20);

    println!();

    // Stage 3: Structural Sharing
    println!("3. Structural Sharing on Unchanged Updates:");
    let same_font_user = user_font_lens.set(initial_user.clone(), 14);
    assert_eq!(same_font_user, initial_user);
    println!("  Setting identical value returns original instance unchanged.");

    let identity_modified_user = user_font_lens.modify(initial_user.clone(), |size| size);
    assert_eq!(identity_modified_user, initial_user);
    println!("  Modifying with identity function preserves structural equality.");

    println!();

    // Stage 4: Bidirectional Type Transformation with `iso_map`
    println!("4. Type Transformation via `iso_map`:");
    // `to_le_bytes` / `from_le_bytes` are exact inverses, so the lens laws hold
    let font_bytes_lens = theme_font_size_lens().iso_map(
        |size: u32| size.to_le_bytes(),
        |bytes: [u8; 4]| u32::from_le_bytes(bytes),
    );

    let current_theme = Theme {
        mode: "dark".to_string(),
        font_size: 16,
    };

    let font_bytes = font_bytes_lens.get(&current_theme);
    println!("  Viewed font size as bytes: {:?}", font_bytes);
    assert_eq!(font_bytes, 16u32.to_le_bytes());

    let resized_theme = font_bytes_lens.set(current_theme, 24u32.to_le_bytes());
    println!("  Set font size using bytes: {}", resized_theme.font_size);
    assert_eq!(resized_theme.font_size, 24);

    println!("\n=== Lens Example Completed Successfully ===");
}
