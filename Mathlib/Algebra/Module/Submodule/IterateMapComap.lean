/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Module.Submodule.Ker

/-!

# Iterate maps and comaps of submodules

Some preliminary work for establishing the strong rank condition for noetherian rings.

Given two linear maps `f i : M →ₗ[R] M₂` and a submodule `K : Submodule R M`, we can define
`LinearMap.iterateMapComapAux f i n K : Submodule R M` to be `f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times).
If `f(K) ≤ i(K)`, then this sequence is non-decreasing (`LinearMap.iterateMapComap`).
If moreover `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComapAux f i m K = LinearMap.iterateMapComapAux f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComapAux f i n K = LinearMap.iterateMapComapAux f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComapAux_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank condition
for noetherian rings.

The construction here is adapted from the proof in Djoković's paper
*Epimorphisms of modules which must be isomorphisms* [djokovic1973].

-/

open Function Submodule

namespace LinearMap

variable {R M M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂] (f i : M →ₗ[R] M₂)

/-- The `LinearMap.iterateMapComapAux f i n K : Submodule R M` is
`f⁻¹(i(⋯(f⁻¹(i(K)))))` (`n` times). -/
def iterateMapComapAux (n : ℕ) := (fun K : Submodule R M ↦ (K.map i).comap f)^[n]

/-- If `f(K) ≤ i(K)`, then `LinearMap.iterateMapComapAux` is not decreasing. -/
theorem iterateMapComapAux_le_succ (K : Submodule R M) (h : K.map f ≤ K.map i) (n : ℕ) :
    f.iterateMapComapAux i n K ≤ f.iterateMapComapAux i (n + 1) K := by
  nth_rw 2 [iterateMapComapAux]
  rw [iterate_succ', Function.comp_apply, ← iterateMapComapAux, ← map_le_iff_le_comap]
  induction n with
  | zero => exact h
  | succ n ih =>
    simp_rw [iterateMapComapAux, iterate_succ', Function.comp_apply]
    calc
      _ ≤ (f.iterateMapComapAux i n K).map i := map_comap_le _ _
      _ ≤ (((f.iterateMapComapAux i n K).map f).comap f).map i := map_mono (le_comap_map _ _)
      _ ≤ _ := map_mono (comap_mono ih)

/-- If `f(K) ≤ i(K)`, then `LinearMap.iterateMapComapAux` is not decreasing. -/
@[simps]
def iterateMapComap (K : Submodule R M) (h : K.map f ≤ K.map i) : ℕ →o Submodule R M where
  toFun n := f.iterateMapComapAux i n K
  monotone' := monotone_nat_of_le_succ (iterateMapComapAux_le_succ f i K h)

/-- If `LinearMap.iterateMapComapAux f i 0 K < LinearMap.iterateMapComapAux f i 1 K`,
`f` is surjective, `i` is injective, then `LinearMap.iterateMapComapAux` is strictly increasing. -/
theorem iterateMapComapAux_lt_succ (K : Submodule R M)
    (h : f.iterateMapComapAux i 0 K < f.iterateMapComapAux i 1 K)
    (hf : Surjective f) (hi : Injective i) (n : ℕ) :
    f.iterateMapComapAux i n K < f.iterateMapComapAux i (n + 1) K := by
  induction n with
  | zero => exact h
  | succ n ih =>
    refine Ne.lt_of_le (fun H ↦ ?_)
      (iterateMapComapAux_le_succ f i K (map_le_iff_le_comap.2 h.le) (n + 1))
    rw [iterateMapComapAux, iterateMapComapAux, iterate_succ', iterate_succ'] at H
    exact ih.ne (map_injective_of_injective hi (comap_injective_of_surjective hf H))

/-- If `f(K) ≤ i(K)`, `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComapAux f i m K = LinearMap.iterateMapComapAux f i (m + 1) K`,
then for any `n`,
`LinearMap.iterateMapComapAux f i n K = LinearMap.iterateMapComapAux f i (n + 1) K`.
In particular, by taking `n = 0`, the kernel of `f` is contained in `K`
(`LinearMap.ker_le_of_iterateMapComapAux_eq_succ`),
which is a consequence of `LinearMap.ker_le_comap`. -/
theorem iterateMapComapAux_eq_succ (K : Submodule R M) (h : K.map f ≤ K.map i)
    (m : ℕ) (heq : f.iterateMapComapAux i m K = f.iterateMapComapAux i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) (n : ℕ) :
    f.iterateMapComapAux i n K = f.iterateMapComapAux i (n + 1) K := by
  induction n with
  | zero =>
    by_contra! H
    exact (iterateMapComapAux_lt_succ f i K (H.lt_of_le (map_le_iff_le_comap.1 h)) hf hi m).ne heq
  | succ n ih =>
    rw [iterateMapComapAux, iterateMapComapAux, iterate_succ', iterate_succ',
      Function.comp_apply, Function.comp_apply, ← iterateMapComapAux, ← iterateMapComapAux, ih]

/-- If `f(K) ≤ i(K)`, `f` is surjective, `i` is injective, and there exists some `m` such that
`LinearMap.iterateMapComapAux f i m K = LinearMap.iterateMapComapAux f i (m + 1) K`,
then the kernel of `f` is contained in `K`.
This is a corollary of `LinearMap.iterateMapComapAux_eq_succ` and `LinearMap.ker_le_comap`.
As a special case, if one can take `K` to be zero,
then `f` is injective. This is the key result for establishing the strong rank condition
for noetherian rings. -/
theorem ker_le_of_iterateMapComapAux_eq_succ (K : Submodule R M) (h : K.map f ≤ K.map i)
    (m : ℕ) (heq : f.iterateMapComapAux i m K = f.iterateMapComapAux i (m + 1) K)
    (hf : Surjective f) (hi : Injective i) : LinearMap.ker f ≤ K := by
  rw [show K = _ from f.iterateMapComapAux_eq_succ i K h m heq hf hi 0]
  exact f.ker_le_comap

end LinearMap
