# Trust Model and Trusted Computing Base (TCB)

This document defines the soundness boundary of `sroof`.

## Two distinct claims

sroof makes two claims that must not be conflated, because they rest on
different components.

**1. Core logical validity.** The generated proof term inhabits the claimed core
proposition. This is decided by the trusted kernel and the core semantics it
uses. It holds identically on both frontends.

**2. Scala semantic correspondence.** *(Scala frontend only.)* The core
proposition is about the Scala program the user actually wrote. The kernel
cannot check this: it sees core terms and has no way to know whether they model
the Scala source. This claim rests on the Scala-to-core translation.

On the `.sroof` path only claim 1 is made — a `.sroof` file has no meaning apart
from its elaboration, so there is nothing to correspond *to*. On the Scala path,
a theorem is asserted to say something about a real Scala function, so claim 2 is
part of what the user is being told, and the translation is therefore inside the
TCB for that claim. Describing the Scala frontend as wholly outside the TCB would
be false.

## Safety Principle

`sroof` is sound only if the trusted kernel is sound.
Bugs outside the kernel may cause proof search failures, bad UX, or false negatives, but they must not be able to accept an invalid proof term as valid.

For the Scala frontend this principle needs a second sentence: a bug in the
Scala-to-core bridge cannot make the kernel accept an invalid proof, but it can
make a valid proof be about the wrong function. That is why the bridge is kept
deliberately small and is covered by golden and differential tests rather than
being trusted on inspection.

## Trusted vs Untrusted Components

Trusted for **core logical validity** (TCB):

- `kernel/` (`sroof.kernel.Kernel`)
- Core type-checking semantics used by kernel verification: `checker.Bidirectional`,
  **`checker.IndChecker`** (constructor and match rules — `Bidirectional` calls
  straight into it), and term/eval semantics

`IndChecker` is called out by name because "everything in `checker/` except
`Bidirectional` is re-checked" is a tempting and wrong reading. `Kernel.verify`
delegates to `Bidirectional.check`, which delegates to `IndChecker`; the kernel
re-checks a proof term *using* those rules, so it cannot catch a bug in them.
The v0.10.0 constructor-index unsoundness was exactly that, and it survived
seven releases with the kernel accepting it every time.

Additionally trusted for **Scala semantic correspondence** (Scala frontend only):

- `scala-frontend/` translation from resolved IR into core terms
  (`frontend.CoreTranslator`): binder order, recursion encoding, constructor and
  match translation
- `scala-plugin/` extraction from typed trees into that IR
  (`plugin.dotc.TreeExtractor`): which Scala construct maps to which IR node

Untrusted (must be re-checked by kernel):

- `tactic/` (proof-term generation)
- `checker/` orchestration only — the pipeline that decides *what* to check.
  The typing rules themselves (`Bidirectional`, `IndChecker`) are trusted, above.
- `syntax/` parser/elaborator
- `cli/` command-line and JSON formatting
- `vscode-sroof/` editor integration
- `cli/agent` automated proof search
- `frontend.ProofRunner` tactic scheduling — it builds candidates, and every one
  goes through `Kernel.verify`

### Why the bridge is small on purpose

The bridge accepts only constructs with one obvious core reading, and rejects
everything else rather than approximating it. A mistranslation is undetectable by
the kernel, so the mitigation is to keep the set of translated constructs small
enough to audit, and to test the correspondence directly:

- golden tests pinning the exact core term for `Nat` and `plus`;
- a finite differential test comparing Scala `plus` against core evaluation;
- negative tests asserting unsupported Scala is rejected, not mistranslated;
- an assertion that no accepted translation contains a `Meta` node.

## Annotations do not verify anything

`@proofModule` and `@theorem` are inert `StaticAnnotation`s. Without the sroof
compiler plugin enabled by the build (`-Xplugin:...`), annotated code compiles
and runs normally and **nothing is proved**. Verification is a build
configuration, not a property of the source file.

The plugin fails closed in the other direction too: a `@theorem` written outside
a `@proofModule` is a compile error rather than an ignored annotation, so an
unproved "theorem" cannot compile clean.

## Kernel Responsibilities

The kernel is the final authority for accepting completed proofs.

- Verify a candidate proof term against its claimed proposition.
- Reject type-incorrect terms and ill-typed equality proofs.
- Return typed failures (no implicit success/fallback path).

Kernel entrypoints:

- `Kernel.check(ctx, proof, claimedType): Either[TypeError, Unit]`
- `Kernel.infer(ctx, term): Either[TypeError, Term]`

The final accept/reject decision for defspec proofs must pass through `Kernel.check`.
The same holds for `@theorem` proofs on the Scala path, via
`Kernel.verify` in `frontend.ProofRunner`. The Scala path has no `sorry`, no
warning-only mode, and no path that accepts a theorem without the kernel.

**The kernel answers one question, and it is narrower than it looks.** It is asked
whether a term has a claimed type. It is not asked whether the claim *is* a type,
and it is not asked about anything the caller did not hand it. Two consequences
were live defects until v0.28:

- A **definition** on the Scala path was never checked against its declared type.
  `CoreTranslator` produced the body and then trusted itself, and it is inside the
  TCB, so an ill-typed body had no one left to catch it. The `.sroof` path had
  closed this in v0.14 (`Checker.checkDefBodies`); `ModuleVerifier.verifyDefBody`
  is the same check on the other path.
- A **theorem statement** was never checked to be a proposition. `translateProp`
  emits the 2-argument `Eq` form, and `Bidirectional.inferUniverse` answers
  `Right(0)` for an applied `Eq` *without inspecting the arguments* — the shape
  alone is taken as evidence. `Kernel.check`'s `refl` case then skips the type
  check on that form, recording the assumption that the caller already made it.
  `ProofRunner.wellFormedProp` now makes it: infer the left side, check the right
  against that type.

If you add a caller of `Kernel.verify`, ask what *else* that caller is asserting
that the kernel is not being shown.

## Kernel API Contract

Callers must provide:

- A complete context for local assumptions/definitions.
- A candidate proof term.
- The claimed type/proposition for that term.

Expected behavior:

- `Right(())`: proof accepted by the trusted kernel.
- `Left(TypeError)`: proof rejected; caller must fail verification.

Non-goals of the kernel:

- Proof search, heuristics, simplification strategy, or UX diagnostics polish.

## Threat Model

Out of scope:

- Malicious runtime/JVM or compromised build infrastructure.
- Supply-chain attacks on dependencies.

In scope:

- Parser/elaborator bugs.
- Tactic engine bugs.
- CLI/agent bugs that generate wrong terms.
- Refactoring mistakes that bypass kernel verification.
- Scala-to-core translation bugs (Scala frontend): a proof about the wrong model.
- Compiler-plugin extraction bugs: a Scala construct read as something it is not.

## Failure Modes

- Parser/elaborator bug: may build wrong term, but kernel should reject invalid proofs.
- Tactic bug: may produce invalid candidate term, but kernel should reject.
- CLI bug: may print misleading output, but must not bypass kernel final check.
- Kernel bug: may accept invalid proof term (soundness break, highest severity).
- Translation/extraction bug (Scala frontend): produces a *valid* proof of a
  proposition about a *different* function than the user wrote. The kernel cannot
  detect this; only the translation tests can. Second-highest severity.

## Soundness Review Checklist

When reviewing changes, verify:

1. Is every successful proof acceptance path still gated by `Kernel.check` / `Kernel.verify`?
2. Did any new shortcut bypass kernel verification?
3. Did kernel logic change for equality/type checking behavior?
4. Are new negative regression tests present for known-unsound patterns?
5. (Scala frontend) Did the accepted Scala subset grow? If so, does each new
   construct have exactly one core reading, and is that reading pinned by a test?
6. (Scala frontend) Does any accepted translation now produce a `Meta` node, or
   any other placeholder standing in for something unresolved?
