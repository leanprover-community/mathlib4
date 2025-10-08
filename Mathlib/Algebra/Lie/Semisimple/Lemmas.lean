/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Lemmas about semisimple Lie algebras

This file is a home for lemmas about semisimple and reductive Lie algebras.

## Main definitions / results:
* `LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`: a finite-dimensional Lie
  algebra with a irreducible faithful finite-dimensional representation is reductive.
* `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful`: a finite-dimensional Lie
  algebra with a irreducible faithful finite-dimensional trace-free representation is semisimple.

## TODO

* Introduce a `Prop`-valued typeclass `LieModule.IsTracefree` stating
  `(toEnd R L M).range ≤ LieAlgebra.derivedSeries R (Module.End R M) 1`, prove
  `f ∈ LieAlgebra.derivedSeries k (Module.End k V) 1 ↔ LinearMap.trace k _ f = 0`, and restate
  `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` using `LieModule.IsTracefree`.

-/

namespace LieAlgebra

open LieModule LieSubmodule Module Set

variable (k L M : Type*) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
  [IsIrreducible k L M] [IsFaithful k L M] [IsTriangularizable k L M]

lemma hasCentralRadical_and_of_isIrreducible_of_isFaithful :
    HasCentralRadical k L ∧ (∀ x, x ∈ center k L ↔ toEnd k L M x ∈ k ∙ LinearMap.id) := by
  have _i := nontrivial_of_isIrreducible k L M
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual k (radical k L), Nontrivial (weightSpace M χ) :=
    exists_nontrivial_weightSpace_of_isSolvable k (radical k L) M
  let N : LieSubmodule k L M := weightSpaceOfIsLieTower k M χ
  replace hχ : Nontrivial N := hχ
  replace hχ : N = ⊤ := N.eq_top_of_isIrreducible k L M
  replace hχ (x : L) (hx : x ∈ radical k L) : toEnd k _ M x = χ ⟨x, hx⟩ • LinearMap.id := by
    ext m
    have hm : ∀ (y : L) (hy : y ∈ radical k L), ⁅y, m⁆ = χ ⟨y, hy⟩ • m := by
      simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using (hχ ▸ mem_top _ : m ∈ N)
    simpa using hm x hx
  have aux : radical k L = center k L := by
    refine le_antisymm (fun x hx ↦ (mem_maxTrivSubmodule k L L x).mpr ?_) (center_le_radical k L)
    intro y
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, hχ _ hx, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]
  refine ⟨⟨aux⟩, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ (mem_maxTrivSubmodule k L L x).mpr fun y ↦ ?_⟩⟩
  · rw [← aux] at hx
    exact Submodule.mem_span_singleton.mpr ⟨χ ⟨x, hx⟩, (hχ x hx).symm⟩
  · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), LieHom.map_lie, ← ht, lie_smul,
      (toEnd k L M y).commute_id_right.lie_eq]

theorem hasTrivialRadical_of_isIrreducible_of_isFaithful
    (h : ∀ x, LinearMap.trace k _ (toEnd k L M x) = 0) : HasTrivialRadical k L := by
  have : finrank k M ≠ 0 := ((finrank_pos_iff).mpr <| nontrivial_of_isIrreducible k L M).ne'
  obtain ⟨_i, h'⟩ := hasCentralRadical_and_of_isIrreducible_of_isFaithful k L M
  rw [hasTrivialRadical_iff, (hasCentralRadical_iff k L).mp inferInstance, LieSubmodule.eq_bot_iff]
  intro x hx
  specialize h x
  rw [h' x] at hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
  suffices t = 0 by simp [← toEnd_eq_zero_iff (R := k) (L := L) (M := M), ← ht, this]
  simpa [this, ← ht] using h

variable {k L M}
variable {R : Type*} [CommRing R] [LieAlgebra R L] [Module R M] [LieModule R L M]

open LinearMap in
lemma trace_toEnd_eq_zero {s : Set L} (hs : ∀ x ∈ s, LinearMap.trace R _ (toEnd R _ M x) = 0)
    {x : L} (hx : x ∈ LieSubalgebra.lieSpan R L s) :
    trace R _ (toEnd R _ M x) = 0 := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu => simpa using hs u hu
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]
  | lie u v _ _ _ _ => simp

end LieAlgebra
