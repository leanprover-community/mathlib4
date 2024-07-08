/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.RingTheory.JacobsonIdeal

#align_import ring_theory.nakayama from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `Submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `Submodule.smul_le_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`RingTheory.Finiteness` under the name
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/


variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

namespace Submodule

/-- **Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson J) : N = J • N := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  cases' Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN with r hr
  cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1) with s hs
  have : n = -(s * r - 1) • n := by
    rw [neg_sub, sub_smul, mul_smul, hr.2 n hn, one_smul, smul_zero, sub_zero]
  rw [this]
  exact Submodule.smul_mem_smul (Submodule.neg_mem _ hs) hn
#align submodule.eq_smul_of_le_smul_of_le_jacobson Submodule.eq_smul_of_le_smul_of_le_jacobson

lemma eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R}
    {N : Submodule R M} (hN : FG N) (hIN : N = I • N)
    (hIjac : I ≤ N.annihilator.jacobson) : N = ⊥ :=
  (eq_smul_of_le_smul_of_le_jacobson hN hIN.le hIjac).trans N.annihilator_smul

open Pointwise in
lemma eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator {r : R}
    {N : Submodule R M} (hN : FG N) (hrN : N = r • N)
    (hrJac : r ∈ N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hrN (ideal_span_singleton_smul r N).symm)
    ((span_singleton_le_iff_mem r _).mpr hrJac)

open Pointwise in
lemma eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator {s : Set R}
    {N : Submodule R M} (hN : FG N) (hsN : N = s • N)
    (hsJac : s ⊆ N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hsN (span_smul_eq s N).symm) (span_le.mpr hsJac)

lemma top_ne_ideal_smul_of_le_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {I} (h : I ≤ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ I • ⊤ := fun H => top_ne_bot <|
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.out H <|
    (congrArg (I ≤ Ideal.jacobson ·) annihilator_top).mpr h

open Pointwise in
lemma top_ne_set_smul_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {s : Set R}
    (h : s ⊆ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ s • ⊤ :=
  ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

open Pointwise in
lemma top_ne_pointwise_smul_of_mem_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {r} (h : r ∈ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ r • ⊤ :=
  ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

/-- **Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ := by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, Submodule.bot_smul]
#align submodule.eq_bot_of_le_smul_of_le_jacobson_bot Submodule.eq_bot_of_le_smul_of_le_jacobson_bot

theorem sup_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' := by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap := Submodule.comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    simpa only [← h_comap.eq_iff, comap_map_mkQ, sup_comm, eq_comm] using hNN'
  have :=
    @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkQ) (hN'.map _)
      (by rw [← map_smul'', this]) hIJ
  rwa [← map_smul'', ← h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ, sup_comm,
    sup_comm (b := N)] at this

/-- **Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' :=
  ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)
#align submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson

theorem le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N := by
  rw [← sup_eq_left, sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul, sup_bot_eq]

/-- **Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem smul_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : I • N' ≤ N :=
  smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)
#align submodule.smul_le_of_le_smul_of_le_jacobson_bot Submodule.smul_le_of_le_smul_of_le_jacobson_bot

end Submodule
