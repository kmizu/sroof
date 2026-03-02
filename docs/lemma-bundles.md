# Reusable Lemma Bundles

This document defines reusable lemma bundles for common proof maintenance workflows.

## Available bundles

- `nat-simplify`
- `list-core`
- `bool-normalize`

Bundle manifests live under `stdlib/bundles/*.bundle`.

## Bundle contents

### nat-simplify

- `plus_zero_left`
- `plus_succ_left`
- `plus_zero_right`
- `refl`

### list-core

- `length_nil`
- `append_nil_left`
- `map_nil`

### bool-normalize

- `not_not`
- `and_true`
- `or_false`

## Compatibility policy

- Bundle names are stable in v1.
- Existing lemma entries are append-only in minor updates.
- Removing or renaming an existing bundle entry requires a major stdlib revision.
