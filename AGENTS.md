# Repository Guidelines

## Project Structure & Module Organization
This repository is a multi-module Scala/SBT project.

- Core JVM modules: `core`, `eval`, `checker`, `tactic`, `syntax`, `extract`, `kernel`, `cli`
- Standard layout per module: `src/main/scala` and `src/test/scala`
- Native mirror modules: `*-native/` (sources are shared from JVM modules via `build.sbt`; do not add separate logic there)
- Proof examples: `examples/*.sroof`
- VS Code extension: `vscode-sroof/`
- sbt plugin: `sbt-sroof/`

## Build, Test, and Development Commands
Use SBT from the repository root unless noted.

```bash
sbt compile
sbt test
sbt checker/test
sbt "cli/run check examples/nat.sroof"
sbt "cli/run extract examples/nat.sroof --output Nat.scala"
sbt cliNative/compile
sbt cliNative/nativeLink
cd vscode-sroof && npm ci && npm run compile
```

- `sbt test` runs all MUnit suites across modules.
- `cliNative/nativeLink` requires `clang`, `lld`, and `libunwind-dev`.

## Coding Style & Naming Conventions
- Scala uses Scala 3 significant indentation and `:`-style definitions.
- Follow existing 2-space indentation and keep changes localized.
- Package names use `sroof.<module>`; types/objects use `PascalCase`; methods/vals use `camelCase`.
- Test files follow `*Suite.scala` naming and live in the matching module.
- No repository-wide formatter config is committed; avoid unrelated formatting churn.

## Testing Guidelines
- Test framework: `munit` (configured in `build.sbt`).
- Prefer targeted runs while iterating (`sbt cli/test`, `sbt syntax/test`) and finish with `sbt test`.
- Add or update tests for behavior changes, especially parser/elaboration, tactics, and checker logic.
- When CLI proof flows change, verify end-to-end with `sbt "cli/run check examples/nat.sroof"` and `sbt "cli/run check examples/int.sroof"`.

## Commit & Pull Request Guidelines
- Match the existing commit style seen in history: `feat: ...`, `fix: ...`, `chore: ...`.
- Keep commits focused to one logical change and include tests when possible.
- In PRs, include: purpose, affected modules, and exact verification commands executed.
- For `vscode-sroof` UX changes, include screenshots or brief output snippets.
