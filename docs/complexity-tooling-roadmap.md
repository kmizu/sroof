# Complexity Tooling Roadmap

This roadmap defines the engineering plan to make `sproof` capable of large-scale formalization work in complexity theory.
It intentionally focuses on tooling, libraries, and workflow infrastructure.

## Scope

- Build a reusable formalization stack for complexity-theory definitions and proofs.
- Support very large proofs through modularization, automation, and machine-checked validation.
- Establish a human+AI workflow for high-throughput proof exploration.

## Non-goals (for this roadmap)

- Claiming new mathematical results.
- Publishing conjecture-level statements without machine-checked proof artifacts.

## Milestones

### M0: Proof Infrastructure Hardening

- Stabilize theorem reuse across declarations.
- Strengthen `sorry` taint tracking and CI policy.
- Improve proof debugging UX (`proof-state`, diagnostics, reproducible failures).

Exit criteria:
- Full CI green with strict kernel gate.
- Deterministic replay for representative proof failures.

### M1: Discrete Math Core Library

- Expand standard libraries for finite sets, finite maps, relations, and combinators.
- Add proof bundles for rewriting common algebraic/relational lemmas.

Exit criteria:
- A curated library of reusable lemmas with examples and bundle docs.
- No-copy proof style for most routine transformations.

### M2: Computation Model Formalization

- Formalize one executable baseline model (e.g., deterministic TM or circuit model).
- Define step semantics, input encoding, and size measures.
- Add machine-checked examples of concrete programs and traces.

Exit criteria:
- End-to-end checked examples from model definition to acceptance/rejection theorem.

### M3: Complexity Framework Layer

- Formalize time bounds, reductions, verifier-style definitions, and closure properties.
- Standardize interfaces so results are portable across models.

Exit criteria:
- Core framework theorems (sound definitions, equivalence glue lemmas, composition lemmas) are checked and documented.

### M4: Reduction & Completeness Toolkit

- Build reusable reduction templates.
- Provide canonical proof skeletons for reduction correctness.
- Add extraction helpers for executable checkers where useful.

Exit criteria:
- Multiple benchmark reductions formalized with shared templates.

### M5: Barrier/Meta-Check Tooling

- Encode known proof-strategy constraints as machine-checkable meta-checks.
- Add candidate filters that reject obviously non-viable proof routes early.

Exit criteria:
- Automated pre-check pipeline that flags blocked proof strategies before deep formalization.

### M6: AI-Assisted Exploration Loop

- Candidate generation: synthesize lemma/proof skeleton proposals.
- Candidate triage: run meta-checks + small-instance refutation.
- Candidate formalization: convert survivors into `sproof` obligations.
- Candidate verification: kernel-check + regression integration.

Exit criteria:
- Reproducible loop in CI: `generate -> triage -> formalize -> verify -> learn`.

## Human + AI Operating Model

- Human role:
  - choose search direction and abstraction level
  - define acceptance criteria for candidate families
  - review high-level proof structure
- AI role:
  - enumerate and rank candidates at scale
  - generate local lemmas and intermediate obligations
  - perform bulk proof refactoring and replay checks
- Kernel role:
  - final authority for correctness

## Engineering Rules

- Every PR must include:
  - definitions
  - at least one non-trivial checked theorem
  - regression tests
- Keep theorem APIs stable once adopted in bundles.
- Prefer small composable lemmas over monolithic proofs.

## Tracking

Recommended issue labels:

- `roadmap:m0` ... `roadmap:m6`
- `formalization:core-lib`
- `formalization:model`
- `formalization:reductions`
- `automation:search`
- `automation:barrier-check`
