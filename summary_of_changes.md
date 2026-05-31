# Branch `prod_le_pow_card`: Summary of Changes

This branch performs a large-scale renaming and API expansion of big operator inequality lemmas across `List`, `Multiset`, `Finset`, `Fintype`, and `Finprod`, primarily in the `Algebra.Order.BigOperators` directory. The changes fall into the following categories:

## 1. Renaming in ordered monoids (removing trailing primes)

Lemmas in `Group/List.lean`, `Group/Multiset.lean`, `Group/Finset.lean`, and `Finprod.lean` are renamed to remove the trailing `'` (prime) from names. For example:
- `prod_le_prod'` → `prod_le_prod`
- `one_le_prod'` → `one_le_prod`
- `prod_le_one'` → `prod_le_one`
- `single_le_prod'` → `single_le_prod`
- `prod_le_prod_of_subset_of_one_le'` → `prod_le_prod_of_subset_of_one_le`
- etc.

Deprecated aliases with date `2026-01-18` are added for all renamed lemmas.

## 2. Renaming in ordered monoids with zero (adding `₀` suffix)

Lemmas in `GroupWithZero/List.lean`, `GroupWithZero/Multiset.lean`, `GroupWithZero/Finset.lean` are renamed to add a `₀` suffix (to disambiguate from the monoid versions, which now take the unprimed names). For example:
- `Finset.prod_le_prod` → `Finset.prod_le_prod₀`
- `Finset.prod_le_one` → `Finset.prod_le_one₀`
- `Finset.one_le_prod` → `Finset.one_le_prod₀`
- `finprod_le_finprod` → `finprod_le_finprod₀`

## 3. New API lemmas for `GroupWithZero`

Many lemmas that previously only existed for ordered monoids (in `Group/`) are now mirrored for `CommMonoidWithZero` with `PosMulMono` (in `GroupWithZero/`). These are new lemmas requiring a `0 ≤ f i` hypothesis instead of relying on `MulLeftMono`. Examples:
- `prod_le_prod_of_subset_of_one_le₀`, `prod_le_prod_of_subset_of_le_one₀`
- `prod_mono_set_of_one_le₀`, `prod_anti_set_of_le_one₀`
- `single_le_prod₀`, `mul_le_prod₀`
- `prod_eq_one_iff_of_one_le₀`, `prod_eq_one_iff_of_le_one₀`
- `prod_fiberwise_le_prod_of_one_le_prod_fiber₀`
- `Fintype` namespace versions of all of the above
- List/Multiset versions: `Forall₂.prod_le_prod₀`, `Sublist.prod_le_prod₀`, `prod_lt_prod₀`, etc.

## 4. Pow lemma renaming and additions

In `Monoid/Unbundled/Pow.lean`:
- `pow_le_pow_right'` → `pow_le_pow_right`
- `pow_le_pow_right_of_le_one'` → `pow_le_pow_right_of_le_one`
- `pow_le_pow_left'` → `pow_le_pow_left`
- `one_lt_pow'` → `one_lt_pow`
- `pow_lt_one'` → `pow_lt_one`

In `GroupWithZero/Unbundled/Basic.lean`:
- `pow_le_pow_of_le_one` → `pow_le_pow_right_of_le_one₀`
- New: `pow_le_pow₀`, `pow_le_pow_mul_of_sq_le_mul₀`

## 5. Downstream fixups (~40 files)

All call sites across Mathlib are updated to use the new names.

## 6. SpectralNorm simplification

A proof in `SpectralNorm.lean` is simplified using the new `prod_map_le_pow_card₀` lemma.
