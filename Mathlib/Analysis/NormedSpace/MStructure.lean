/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module analysis.normed_space.M_structure
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Analysis.Normed.Group.Basic

/-!
# M-structure

A projection P on a normed space X is said to be an L-projection (`is_Lprojection`) if, for all `x`
in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

A projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

The L-projections on `X` form a Boolean algebra (`is_Lprojection.subtype.boolean_algebra`).

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`measure_theory.measurable_space`.

Instead of using `P : X →L[𝕜] X` to represent projections, we use an arbitrary ring `M` with a
faithful action on `X`. `continuous_linear_map.apply_module` can be used to recover the `X →L[𝕜] X`
special case.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

universe u

variable (X : Type u) [NormedAddCommGroup X]

variable {M : Type} [Ring M] [Module M X]

/-- A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
structure IsLprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Lnorm : ∀ x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖
#align is_Lprojection IsLprojection

/-- A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
structure IsMprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Mnorm : ∀ x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖
#align is_Mprojection IsMprojection

variable {X}

namespace IsLprojection

theorem lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm, sub_sub_cancel]
    exact h.Lnorm x⟩
#align is_Lprojection.Lcomplement IsLprojection.lcomplement

theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨lcomplement, fun h => sub_sub_cancel 1 P ▸ h.lcomplement⟩
#align is_Lprojection.Lcomplement_iff IsLprojection.Lcomplement_iff

theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    Commute P Q := by
  have PR_eq_RPR : ∀ R : M, IsLprojection X R → P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ =
              ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
                (‖(R * R) • x - R • P • R • x‖ + ‖(1 - R) • (1 - P) • R • x‖) :=
            by
            rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) • R • x), sub_smul 1 P, one_smul, smul_sub,
              mul_smul]
          _ =
              ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
                (‖R • x - R • P • R • x‖ + ‖((1 - R) * R) • x - (1 - R) • P • R • x‖) :=
            by rw [h₃.proj.eq, sub_smul 1 P, one_smul, smul_sub, mul_smul]
          _ =
              ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
                (‖R • x - R • P • R • x‖ + ‖(1 - R) • P • R • x‖) :=
            by rw [sub_mul, h₃.proj.eq, one_mul, sub_self, zero_smul, zero_sub, norm_neg]
          _ = ‖R • P • R • x‖ + ‖R • x - R • P • R • x‖ + 2 • ‖(1 - R) • P • R • x‖ := by abel
          _ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
            by
            rw [GE.ge]
            have :=
              add_le_add_right (norm_le_insert' (R • x) (R • P • R • x)) (2 • ‖(1 - R) • P • R • x‖)
            simpa only [mul_smul, sub_smul, one_smul] using this

      rw [GE.ge] at e1
      nth_rewrite 2 [← add_zero ‖R • x‖]  at e1
      rw [add_le_add_iff_left, two_smul, ← two_mul] at e1
      rw [le_antisymm_iff]
      refine' ⟨_, norm_nonneg _⟩
      rwa [← MulZeroClass.mul_zero (2 : ℝ), mul_le_mul_left (show (0 : ℝ) < 2 by norm_num)] at e1
  have QP_eq_QPQ : Q * P = Q * P * Q :=
    by
    have e1 : P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
      calc
        P * (1 - Q) = (1 - Q) * P * (1 - Q) := by rw [PR_eq_RPR (1 - Q) h₂.lcomplement]
        _ = 1 * (P * (1 - Q)) - Q * (P * (1 - Q)) := by rw [mul_assoc, sub_mul]
        _ = P * (1 - Q) - Q * (P * (1 - Q)) := by rw [one_mul]
        _ = P * (1 - Q) - Q * (P - P * Q) := by rw [mul_sub, mul_one]
        _ = P * (1 - Q) - (Q * P - Q * P * Q) := by rw [mul_sub Q, mul_assoc]
    rwa [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1
  show P * Q = Q * P
  · rw [QP_eq_QPQ, PR_eq_RPR Q h₂]
#align is_Lprojection.commute IsLprojection.commute

theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine' ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, _⟩
  intro x
  refine' le_antisymm _ _
  ·
    calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel'_right ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]

  ·
    calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]

#align is_Lprojection.mul IsLprojection.mul

theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert (Lcomplement_iff _).mp (h₁.lcomplement.mul h₂.lcomplement) using 1
  rw [sub_mul, one_mul, sub_sub, sub_sub_self, mul_sub, mul_one, add_sub, add_comm]
#align is_Lprojection.join IsLprojection.join

instance : HasCompl { f : M // IsLprojection X f } :=
  ⟨fun P => ⟨1 - P, P.prop.lcomplement⟩⟩


instance : HasCompl { f : M // IsLprojection X f } :=
  ⟨fun P => ⟨1 - P, P.prop.lcomplement⟩⟩

instance [FaithfulSMul M X] : Inf { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]
theorem coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊓ Q) = (↑P : M) * ↑Q :=
  rfl
#align is_Lprojection.coe_inf IsLprojection.coe_inf

instance [FaithfulSMul M X] : Sup { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]
theorem coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊔ Q) = (↑P : M) + ↑Q - ↑P * ↑Q :=
  rfl
#align is_Lprojection.coe_sup IsLprojection.coe_sup

instance [FaithfulSMul M X] : SDiff { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.lcomplement⟩⟩

@[simp]
theorem coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P \ Q) = (↑P : M) * (1 - ↑Q) :=
  rfl
#align is_Lprojection.coe_sdiff IsLprojection.coe_sdiff

instance [FaithfulSMul M X] : PartialOrder { P : M // IsLprojection X P }
    where
  le P Q := (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂⊢
    rw [h₁, mul_assoc, ← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.eq (by convert (P.prop.commute Q.prop).eq)

theorem le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    P ≤ Q ↔ (P : M) = ↑(P ⊓ Q) :=
  Iff.rfl
#align is_Lprojection.le_def IsLprojection.le_def

instance : Zero { P : M // IsLprojection X P } :=
  ⟨⟨0,
      ⟨by rw [IsIdempotentElem, MulZeroClass.zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]
theorem coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl
#align is_Lprojection.coe_zero IsLprojection.coe_zero

instance : One { P : M // IsLprojection X P } :=
  ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.lcomplement⟩⟩

@[simp]
theorem coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
#align is_Lprojection.coe_one IsLprojection.coe_one

instance [FaithfulSMul M X] : BoundedOrder { P : M // IsLprojection X P }
    where
  top := 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (MulZeroClass.zero_mul (P : M)).symm

@[simp]
theorem coe_bot [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderBot.toBot.bot : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl
#align is_Lprojection.coe_bot IsLprojection.coe_bot

@[simp]
theorem coe_top [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderTop.toTop.top : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
#align is_Lprojection.coe_top IsLprojection.coe_top

theorem compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑(Pᶜ) * Q = Q - ↑P * Q := by
  rw [coe_compl, sub_mul, one_mul]
#align is_Lprojection.compl_mul IsLprojection.compl_mul

theorem mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑(Pᶜ) = 0 := by
  rw [coe_compl, mul_sub, mul_one, P.prop.proj.eq, sub_self]
#align is_Lprojection.mul_compl_self IsLprojection.mul_compl_self

theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }} :
    ((↑P : M) + ↑(Pᶜ) * R) * (↑P + ↑Q * ↑R * ↑(Pᶜ)) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
  rw [add_mul, mul_add, mul_add, mul_assoc (↑(Pᶜ)) (↑R) (↑Q * ↑R * ↑(Pᶜ)), ←
    mul_assoc (↑R) (↑Q * ↑R) ↑(Pᶜ), ← coe_inf Q, (Pᶜ.Prop.Commute R.prop).Eq,
    ((Q ⊓ R).Prop.Commute Pᶜ.Prop).Eq, (R.prop.commute (Q ⊓ R).Prop).Eq, coe_inf Q, mul_assoc ↑Q, ←
    mul_assoc, mul_assoc ↑R, (Pᶜ.Prop.Commute P.prop).Eq, mul_compl_self, MulZeroClass.zero_mul,
    MulZeroClass.mul_zero, zero_add, add_zero, ← mul_assoc, P.prop.proj.eq, R.prop.proj.eq, ←
    coe_inf Q, mul_assoc, ((Q ⊓ R).Prop.Commute Pᶜ.Prop).Eq, ← mul_assoc, Pᶜ.Prop.proj.Eq]
#align is_Lprojection.distrib_lattice_lemma IsLprojection.distrib_lattice_lemma



instance [FaithfulSMul M X] : DistribLattice { P : M // IsLprojection X P } :=
  { is_Lprojection.Subtype.hasInf, is_Lprojection.Subtype.hasSup,
    IsLprojection.Subtype.partialOrder with
    le_sup_left := fun P Q => by
      rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, ← mul_assoc, P.prop.proj.eq,
        sub_self, add_zero]
    le_sup_right := fun P Q => by
      rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, Commute.eq (Commute P.prop Q.prop),
        ← mul_assoc, Q.prop.proj.eq, add_sub_cancel'_right]
    sup_le := fun P Q R =>
      by
      rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_sup, coe_inf, coe_sup, ← add_sub, add_mul,
        sub_mul, mul_assoc]
      intro h₁ h₂
      rw [← h₂, ← h₁]
    inf_le_left := fun P Q => by
      rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, (Q.prop.commute P.prop).Eq, ← mul_assoc,
        P.prop.proj.eq]
    inf_le_right := fun P Q => by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq]
    le_inf := fun P Q R =>
      by
      rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_inf, coe_inf, ← mul_assoc]
      intro h₁ h₂
      rw [← h₁, ← h₂]
    le_sup_inf := fun P Q R =>
      by
      have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
        rw [coe_inf, coe_sup, coe_sup, ← add_sub, ← add_sub, ← compl_mul, ← compl_mul, add_mul,
          mul_add, (Pᶜ.Prop.Commute Q.prop).Eq, mul_add, ← mul_assoc, mul_assoc ↑Q,
          (Pᶜ.Prop.Commute P.prop).Eq, mul_compl_self, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
          zero_add, add_zero, ← mul_assoc, mul_assoc ↑Q, P.prop.proj.eq, Pᶜ.Prop.proj.Eq, mul_assoc,
          (Pᶜ.Prop.Commute R.prop).Eq, ← mul_assoc]
      have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
        rw [coe_inf, coe_sup, coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, ← compl_mul, ←
          compl_mul, ← compl_mul, (Pᶜ.Prop.Commute (Q ⊓ R).Prop).Eq, coe_inf, mul_assoc,
          distrib_lattice_lemma, (Q.prop.commute R.prop).Eq, distrib_lattice_lemma]
      rw [le_def, e₁, coe_inf, e₂] }



#check IsLprojection.instHasComplSubtypeIsLprojection.{u}

instance [FaithfulSMul M X] : BooleanAlgebra { P : M // IsLprojection X P } :=
  { IsLprojection.instHasComplSubtypeIsLprojection.{u},
    IsLprojection.Subtype.hasSdiff,
    IsLprojection.Subtype.boundedOrder,
    IsLprojection.Subtype.distribLattice with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
          (by
            rw [coe_top, coe_sup, coe_compl, add_sub_cancel'_right, ← coe_compl, mul_compl_self,
              sub_zero])).le
    sdiff_eq := fun P Q => Subtype.ext <| by rw [coe_sdiff, ← coe_compl, coe_inf] }

end IsLprojection
