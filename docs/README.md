# sroof documentation

Start here if you are not sure which document you need.

## If you want to…

| … then read | |
|---|---|
| Write proofs about ordinary Scala 3 code | [scala3-frontend.md](scala3-frontend.md) |
| Know what sroof actually guarantees, and what it trusts to give that guarantee | [trust-model.md](trust-model.md) |
| Learn the proof patterns that come up in practice | [proof-cookbook.md](proof-cookbook.md) |
| See what the standard library provides | [stdlib.md](stdlib.md) |
| Integrate a tool with `check --json` | [json-schema.md](json-schema.md) |
| Understand where effects are allowed and where they are not | [effects.md](effects.md) |
| Reuse a named group of simplification lemmas | [lemma-bundles.md](lemma-bundles.md) |

## The two frontends

sroof has one core and one kernel, reached by two paths:

- **Scala 3 frontend** (new in v0.3) — you write `.scala`; a compiler plugin
  proves annotated theorems during compilation. Covers a deliberately narrow
  subset today. See [scala3-frontend.md](scala3-frontend.md).
- **`.sroof` language** — the mature path, with Scala-like brace syntax, a CLI, a
  standard library, extraction to Scala 3, and a native binary. Fully supported;
  not deprecated. See the [README](../README.md) language guide.

Both submit every completed proof to the same trusted kernel. The difference in
what each *claims* is the subject of [trust-model.md](trust-model.md), and it is
worth reading before relying on either.

## Elsewhere in the repository

- [`../README.md`](../README.md) / [`../README-ja.md`](../README-ja.md) — language guide, tactic reference, quick start
- [`../CHANGELOG.md`](../CHANGELOG.md) — what changed, per release
- [`../RELEASE_NOTES_v0.5.md`](../RELEASE_NOTES_v0.5.md) — the current release in detail
- [`../INCREMENTAL_CHECKING.md`](../INCREMENTAL_CHECKING.md) — the caching strategy behind repeated checks
- [`../AGENTS.md`](../AGENTS.md) / [`../CLAUDE.md`](../CLAUDE.md) — contributor and agent guidance
- [`../examples/`](../examples) — `.sroof` proof examples
- [`../examples-scala3/`](../examples-scala3) — the Scala 3 example, compiled with the plugin
