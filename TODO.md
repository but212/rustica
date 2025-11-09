# Rustica TODO

## Target v0.11.0

### Documentation & User Experience

- [ ] Fix documentation inconsistencies
  - [ ] Update examples with realistic use case guidance
  - [ ] Write "When to Use Rustica" guide
  - [ ] Create comparison with direct Rust implementations
  - [ ] Write migration guide from production code to Rustica
  - [ ] Add clear performance expectations to docs
  - [ ] Create troubleshooting guide for common issues
  - [ ] Add more practical examples to docs

### Code Quality & API

- [ ] Code quality improvements
  - [x] Fix remaining clippy warnings
  - [ ] Standardize error handling patterns
  - [x] Remove unused dependencies from Cargo.toml
  - [ ] Review and simplify public APIs
  - [ ] Add convenience methods for common patterns
  - [ ] Improve error messages for better developer experience

### Testing & Validation

- [ ] Testing improvements
  - [ ] Add integration tests for common workflows
  - [ ] Validate all documented examples work

### Serde Integration

- [ ] Complete serde integration for all data types
  - [ ] Add serialization examples
  - [ ] Test roundtrip serialization

### Lens Functionality (Performance-Dependent)

- [ ] Enhanced lens functionality (only if performance acceptable)
  - [ ] Add lens composition utilities
  - [ ] Improve lens error handling

### Transformer Compositions

- [ ] Add transformer composition utilities
