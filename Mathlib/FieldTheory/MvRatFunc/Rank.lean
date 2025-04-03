/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.MvPolynomial

/-!
# Rank of multivariate rational function field
-/

noncomputable section

universe u v

open Cardinal in
theorem MvRatFunc.rank_eq_max_lift
    {σ : Type u} {F : Type v} [Field F] [Nonempty σ] :
    Module.rank F (FractionRing (MvPolynomial σ F)) = lift.{u} #F ⊔ lift.{v} #σ ⊔ ℵ₀ := by
  let R := MvPolynomial σ F
  let K := FractionRing R
  refine ((rank_le_card _ _).trans ?_).antisymm ?_
  · rw [FractionRing.cardinalMk, MvPolynomial.cardinalMk_eq_max_lift]
  have hinj := IsFractionRing.injective R K
  have h1 := (IsScalarTower.toAlgHom F R K).toLinearMap.rank_le_of_injective hinj
  rw [MvPolynomial.rank_eq_lift, mk_finsupp_nat, lift_max, lift_aleph0, max_le_iff] at h1
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hx : Transcendental F (algebraMap R K (MvPolynomial.X i)) :=
    (transcendental_algebraMap_iff hinj).2 (MvPolynomial.transcendental_X F i)
  have h2 := hx.linearIndependent_sub_inv.cardinal_lift_le_rank
  rw [lift_id'.{v, u}, lift_umax.{v, u}] at h2
  exact max_le (max_le h2 h1.1) h1.2
