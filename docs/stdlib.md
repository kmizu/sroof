# stdlib v1 layout and naming

This document defines stdlib v1 layout for `Nat`, `List`, `Vec`, `Bool`, `Relation`, `Dictionary`, `Effect`, `Option`, `Either`, `Pair`, `PolyList`, `Char`, `String`, `Sigma`, and `Regex`.

## Layout

- `stdlib/Nat.sroof`
- `stdlib/List.sroof`
- `stdlib/Vec.sroof`
- `stdlib/Bool.sroof`
- `stdlib/Relation.sroof`
- `stdlib/Effect.sroof`
- `stdlib/Dictionary.sroof`
- `stdlib/Option.sroof`
- `stdlib/Either.sroof`
- `stdlib/Pair.sroof`
- `stdlib/PolyList.sroof`
- `stdlib/Char.sroof`
- `stdlib/String.sroof`
- `stdlib/Sigma.sroof`
- `stdlib/Regex.sroof`

Each file is self-contained and checker-runnable by itself.

## Naming conventions

- File names use PascalCase domain names (`Nat`, `List`, `Vec`, `Bool`, `Relation`, `Dictionary`, `Effect`, `Option`, `Either`, `Pair`, `PolyList`, `Char`, `String`, `Sigma`, `Regex`).
- Definitions and lemmas use `snake_case`.
- Core operations keep short canonical names (`plus`, `append`, `length`, `concat`, `not`, `and`, `or`, `map_option`, `get_or_else`, `map_either`, `fst`, `snd`).
- Baseline lemmas use descriptive suffixes (`_nil`, `_left`, `_right`, `_none`, `_some`, `_mk`).

## Module Summary

| Module | Types | Key operations | Defspecs |
|--------|-------|---------------|---------|
| Nat | Nat | plus | plus_zero_left, plus_zero_right, plus_succ_left, plus_succ_right |
| List | Nat, List | length, append, reverse, map, filter, fold_left, fold_right | length_nil, append_nil_left/right, append_assoc, map_cons, length_append |
| Vec | Nat, Vec(A)(n) | concat | concat_nil |
| Bool | Bool | not, and, or | not_not, and_true, or_false |
| Relation | Nat, Bool, Relation | contains, insert, union, subset, remove, size | contains_empty, union_empty_left, … |
| Effect | Nat, IO | io_pure, io_bind, io_then, echo_once | io_then_desugars |
| Dictionary | Nat, Bool, MaybeNat, Dictionary | insert, lookup, member, remove, size | lookup_empty, lookup_insert_zero, … |
| Option | Nat, Bool, Option | map_option, get_or_else, is_some, is_none | map_option_none/some, get_or_else_none/some, is_some/is_none variants |
| Either | Nat, Bool, Either | map_either, is_left, is_right, get_left, get_right | map_either_left/right, is_left/right variants, get_left/right |
| Pair | Nat, Pair | fst, snd, swap | fst_mk, snd_mk, swap_mk |
| PolyList | Nat, Bool, PolyList(A) | poly_length, poly_append, poly_reverse | poly_length_nil, poly_append_nil_left, poly_reverse_nil (trivial only; inductive proofs for polymorphic inductives are future work) |
| Char | Nat, Char | char_code | char_code_mk |
| String | Nat, Bool, Char, String | string_length, string_append, string_reverse | string_length_empty, string_append_empty_left/right, string_append_assoc, string_length_append |
| Sigma | Nat, Sigma(A, B) | sigma_fst | sigma_fst_mk |
| Regex | Nat, Bool, List, Regex | nullable, derive, matches, nat_eqb | nullable_*, derive_*, matches_*, nat_eqb_refl, matches_char_self |

## Compatibility policy

- Existing lemma names in v1 are stable.
- New lemmas can be added in a backward-compatible way.
- Removing or renaming existing exported lemmas requires a major stdlib revision.

## Extraction status

Extraction produces Scala that compiles for **all 26** shipped `.sroof` files, and
`scala-it/ExtractionCorpusSuite` keeps it that way — its exception list is empty.
`scala-it/ExtractionRuntimeSuite` goes further and *runs* three of them, because a
back end that swapped a constructor's arguments would compile just as happily.

This is new in v0.20. v0.19 measured 8 of 26 and named one cause; sweeping the
corpus for real turned up five independent defects, and the one v0.19 named was not
the largest of them:

| Defect | Symptom |
|---|---|
| A recursive def was inlined at every use site | `{ def plus … ; plus }(x)(y)` — does not parse |
| A `Fix`-shaped body peeled no parameters | `def concat: [A <: Any] =>> …` — a type lambda where a term type belongs |
| `Type`-valued parameters stayed value parameters | `Not found: type T0` |
| Index arguments were erased from `enum` cases but not from use sites | `Wrong number of argument patterns` |
| A parameterless case in an invariant generic enum | `cannot determine type argument for enum parent class` |

Two decisions inside that work are worth knowing about:

- **Indices are data.** A length index looks erasable, since the `enum` header drops
  the index *parameter*, but the value a `Cons` stores is exactly what gets passed to
  every function taking the length as an argument. Only proofs are erased.
- **`Int` is claimed by the extractor** as Scala's `Int`. A program that declares its
  own `Int` and actually builds or matches one gets its own `enum` instead; a program
  that only mentions the type (as `stdlib/Effect.sroof` does, whose IO runtime needs
  a real `Int`) keeps the mapping.

Proof checking is unaffected; this is the extraction back end only.
