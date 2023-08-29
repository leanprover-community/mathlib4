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

* `Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `Submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`RingTheory.Noetherian` under the name
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/


variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

namespace Submodule

/-- *Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson J) : N = J • N := by
  refine' le_antisymm _ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  -- ⊢ N ≤ J • N
  intro n hn
  -- ⊢ n ∈ J • N
  cases' Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN with r hr
  -- ⊢ n ∈ J • N
  cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1) with s hs
  -- ⊢ n ∈ J • N
  have : n = -(s * r - 1) • n := by
    rw [neg_sub, sub_smul, mul_smul, hr.2 n hn, one_smul, smul_zero, sub_zero]
  rw [this]
  -- ⊢ -(s * r - 1) • n ∈ J • N
  exact Submodule.smul_mem_smul (Submodule.neg_mem _ hs) hn
  -- 🎉 no goals
#align submodule.eq_smul_of_le_smul_of_le_jacobson Submodule.eq_smul_of_le_smul_of_le_jacobson

/-- *Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ := by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, Submodule.bot_smul]
  -- 🎉 no goals
#align submodule.eq_bot_of_le_smul_of_le_jacobson_bot Submodule.eq_bot_of_le_smul_of_le_jacobson_bot

/-- *Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N ⊔ N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' := by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm hNN (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap := Submodule.comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  -- ⊢ N ⊔ I • N' = N ⊔ J • N'
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    rw [← h_comap.eq_iff]
    simpa [comap_map_eq, sup_comm, eq_comm] using hNN'
  have :=
    @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkQ) (hN'.map _)
      (by rw [← map_smul'', this]) hIJ
  rw [← map_smul'', ← h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ, sup_comm,
    hNN'] at this
  rw [this, sup_comm]
  -- 🎉 no goals
#align submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson Submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson

/-- *Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem smul_sup_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N ⊔ N' ≤ N ⊔ I • N') : I • N' ≤ N := by
  rw [← sup_eq_left, smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul,
    sup_bot_eq]
#align submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot Submodule.smul_sup_le_of_le_smul_of_le_jacobson_bot

end Submodule
