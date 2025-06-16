/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `Submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
  generalising to the Jacobson of any ideal.
* `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
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
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(2)"]
theorem eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson J) : N = J • N := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  obtain ⟨r, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)
  have : n = -(s * r - 1) • n := by
    rw [neg_sub, sub_smul, mul_smul, hr.2 n hn, one_smul, smul_zero, sub_zero]
  rw [this]
  exact Submodule.smul_mem_smul (Submodule.neg_mem _ hs) hn

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
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.fg_top H <|
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
@[stacks 00DV "(2)"]
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ := by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, Submodule.bot_smul]

theorem sup_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' := by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap :=
    comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    simpa only [← h_comap.eq_iff, comap_map_mkQ, sup_comm, eq_comm] using hNN'
  have :=
    @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkQ) (hN'.map _)
      (by rw [← map_smul'', this]) hIJ
  rwa [← map_smul'', ← h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ, sup_comm,
    sup_comm (b := N)] at this

/-- **Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(4)"]
theorem sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' :=
  ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)

theorem le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N := by
  rw [← sup_eq_left, sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul, sup_bot_eq]

/-- **Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
@[stacks 00DV "(4)"]
theorem smul_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : I • N' ≤ N :=
  smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)

open Pointwise

@[stacks 00DV "(3) see `Submodule.localized₀_le_localized₀_of_smul_le` for the second conclusion."]
lemma exists_sub_one_mem_and_smul_le_of_fg_of_le_sup {I : Ideal R}
    {N N' P : Submodule R M} (hN' : N'.FG) (hN'le : N' ≤ P) (hNN' : P ≤ N ⊔ I • N') :
    ∃ r : R, r - 1 ∈ I ∧ r • P ≤ N := by
  have hNN'' : P ≤ N ⊔ N' := le_trans hNN' (by simpa using le_trans smul_le_right le_sup_right)
  have h1 : P.map N.mkQ = N'.map N.mkQ := by
    refine le_antisymm ?_ (map_mono hN'le)
    simpa using map_mono (f := N.mkQ) hNN''
  have h2 : P.map N.mkQ = (I • N').map N.mkQ := by
    apply le_antisymm
    · simpa using map_mono (f := N.mkQ) hNN'
    · rw [h1]
      simp [smul_le_right]
  have hle : (P.map N.mkQ) ≤ I • P.map N.mkQ := by
    conv_lhs => rw [h2]
    simp [← h1]
  obtain ⟨r, hmem, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I _
    (h1 ▸ hN'.map _) hle
  refine ⟨r, hmem, fun x hx ↦ ?_⟩
  induction hx using Submodule.smul_inductionOn_pointwise with
  | smul₀ p hp =>
    rw [← Submodule.Quotient.mk_eq_zero, Quotient.mk_smul]
    exact hr _ ⟨p, hp, rfl⟩
  | smul₁ _ _ _ h => exact N.smul_mem _ h
  | add _ _ _ _ hx hy => exact N.add_mem hx hy
  | zero => exact N.zero_mem

end Submodule
