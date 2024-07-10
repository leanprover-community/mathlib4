/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.WeakDual
import Mathlib.Analysis.Convex.Normed

#align_import analysis.normed_space.M_structure from "leanprover-community/mathlib"@"d11893b411025250c8e61ff2f12ccbd7ee35ab15"

/-!
# M-structure

A projection P on a normed space X is said to be an L-projection (`IsLprojection`) if, for all `x`
in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

A projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

The L-projections on `X` form a Boolean algebra (`IsLprojection.Subtype.BooleanAlgebra`).

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
`MeasureTheory.MeasurableSpace`.

Instead of using `P : X →L[𝕜] X` to represent projections, we use an arbitrary ring `M` with a
faithful action on `X`. `ContinuousLinearMap.apply_module` can be used to recover the `X →L[𝕜] X`
special case.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

variable (X : Type*) [NormedAddCommGroup X]
variable {M : Type*} [Ring M] [Module M X]

set_option linter.uppercaseLean3 false

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

-- Porting note: The literature always uses uppercase 'L' for L-projections
theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm, sub_sub_cancel]
    exact h.Lnorm x⟩
#align is_Lprojection.Lcomplement IsLprojection.Lcomplement

theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩
#align is_Lprojection.Lcomplement_iff IsLprojection.Lcomplement_iff

theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    Commute P Q := by
  have PR_eq_RPR : ∀ R : M, IsLprojection X R → P * R = R * P * R := fun R h₃ => by
    -- Porting note: Needed to fix function, which changes indent of following lines
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖(R * R) • x - R • P • R • x‖ + ‖(1 - R) • (1 - P) • R • x‖) := by
            rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) • R • x), sub_smul 1 P, one_smul, smul_sub,
              mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖((1 - R) * R) • x - (1 - R) • P • R • x‖) := by
            rw [h₃.proj.eq, sub_smul 1 P, one_smul, smul_sub, mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖(1 - R) • P • R • x‖) := by
            rw [sub_mul, h₃.proj.eq, one_mul, sub_self, zero_smul, zero_sub, norm_neg]
          _ = ‖R • P • R • x‖ + ‖R • x - R • P • R • x‖ + 2 • ‖(1 - R) • P • R • x‖ := by abel
          _ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ := by
            rw [GE.ge]
            have :=
              add_le_add_right (norm_le_insert' (R • x) (R • P • R • x)) (2 • ‖(1 - R) • P • R • x‖)
            simpa only [mul_smul, sub_smul, one_smul] using this

      rw [GE.ge] at e1
      -- Porting note: Bump index in nth_rewrite
      nth_rewrite 2 [← add_zero ‖R • x‖] at e1
      rw [add_le_add_iff_left, two_smul, ← two_mul] at e1
      rw [le_antisymm_iff]
      refine ⟨?_, norm_nonneg _⟩
      rwa [← mul_zero (2 : ℝ), mul_le_mul_left (show (0 : ℝ) < 2 by norm_num)] at e1
  have QP_eq_QPQ : Q * P = Q * P * Q := by
    have e1 : P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
      calc
        P * (1 - Q) = (1 - Q) * P * (1 - Q) := by rw [PR_eq_RPR (1 - Q) h₂.Lcomplement]
        _ = P * (1 - Q) - (Q * P - Q * P * Q) := by noncomm_ring
    rwa [eq_sub_iff_add_eq, add_right_eq_self, sub_eq_zero] at e1
  show P * Q = Q * P
  rw [QP_eq_QPQ, PR_eq_RPR Q h₂]
#align is_Lprojection.commute IsLprojection.commute

theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]
#align is_Lprojection.mul IsLprojection.mul

theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring
#align is_Lprojection.join IsLprojection.join

-- Porting note: Advice is to explicitly name instances
-- https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#some-common-fixes
instance Subtype.hasCompl : HasCompl { f : M // IsLprojection X f } :=
  ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]
theorem coe_compl (P : { P : M // IsLprojection X P }) : ↑Pᶜ = (1 : M) - ↑P :=
  rfl
#align is_Lprojection.coe_compl IsLprojection.coe_compl

instance Subtype.inf [FaithfulSMul M X] : Inf { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]
theorem coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊓ Q) = (↑P : M) * ↑Q :=
  rfl
#align is_Lprojection.coe_inf IsLprojection.coe_inf

instance Subtype.sup [FaithfulSMul M X] : Sup { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]
theorem coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊔ Q) = (↑P : M) + ↑Q - ↑P * ↑Q :=
  rfl
#align is_Lprojection.coe_sup IsLprojection.coe_sup

instance Subtype.sdiff [FaithfulSMul M X] : SDiff { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]
theorem coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P \ Q) = (↑P : M) * (1 - ↑Q) :=
  rfl
#align is_Lprojection.coe_sdiff IsLprojection.coe_sdiff

instance Subtype.partialOrder [FaithfulSMul M X] :
    PartialOrder { P : M // IsLprojection X P } where
  le P Q := (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁, mul_assoc, ← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.eq (by convert (P.prop.commute Q.prop).eq)

theorem le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    P ≤ Q ↔ (P : M) = ↑(P ⊓ Q) :=
  Iff.rfl
#align is_Lprojection.le_def IsLprojection.le_def

instance Subtype.zero : Zero { P : M // IsLprojection X P } :=
  ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]
theorem coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl
#align is_Lprojection.coe_zero IsLprojection.coe_zero

instance Subtype.one : One { P : M // IsLprojection X P } :=
  ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.Lcomplement⟩⟩

@[simp]
theorem coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
#align is_Lprojection.coe_one IsLprojection.coe_one

instance Subtype.boundedOrder [FaithfulSMul M X] :
    BoundedOrder { P : M // IsLprojection X P } where
  top := 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]
theorem coe_bot [FaithfulSMul M X] :
    -- Porting note: Manual correction of name required here
    ↑(BoundedOrder.toOrderBot.toBot.bot : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl
#align is_Lprojection.coe_bot IsLprojection.coe_bot

@[simp]
theorem coe_top [FaithfulSMul M X] :
    -- Porting note: Manual correction of name required here
    ↑(BoundedOrder.toOrderTop.toTop.top : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl
#align is_Lprojection.coe_top IsLprojection.coe_top

theorem compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑Pᶜ * Q = Q - ↑P * Q := by
  rw [coe_compl, sub_mul, one_mul]
#align is_Lprojection.compl_mul IsLprojection.compl_mul

theorem mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑Pᶜ = 0 := by
  rw [coe_compl, mul_sub, mul_one, P.prop.proj.eq, sub_self]
#align is_Lprojection.mul_compl_self IsLprojection.mul_compl_self

theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }} :
    ((↑P : M) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = ↑P + ↑Q * ↑R * ↑Pᶜ := by
  rw [add_mul, mul_add, mul_add, (mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ)),
    ← mul_assoc (R : M) (↑Q * ↑R) _, ← coe_inf Q, (Pᶜ.prop.commute R.prop).eq,
    ((Q ⊓ R).prop.commute Pᶜ.prop).eq, (R.prop.commute (Q ⊓ R).prop).eq, coe_inf Q,
    mul_assoc (Q : M), ← mul_assoc, mul_assoc (R : M), (Pᶜ.prop.commute P.prop).eq, mul_compl_self,
    zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc, P.prop.proj.eq,
    R.prop.proj.eq, ← coe_inf Q, mul_assoc, ((Q ⊓ R).prop.commute Pᶜ.prop).eq, ← mul_assoc,
    Pᶜ.prop.proj.eq]
#align is_Lprojection.distrib_lattice_lemma IsLprojection.distrib_lattice_lemma

-- Porting note: In mathlib3 we were able to directly show that `{ P : M // IsLprojection X P }` was
--  an instance of a `DistribLattice`. Trying to do that in mathlib4 fails with "error:
-- (deterministic) timeout at 'whnf', maximum number of heartbeats (800000) has been reached"
-- My workaround is to show instance Lattice first
instance [FaithfulSMul M X] : Lattice { P : M // IsLprojection X P } where
  le_sup_left P Q := by
    rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, ← mul_assoc, P.prop.proj.eq,
      sub_self, add_zero]
  le_sup_right P Q := by
    rw [le_def, coe_inf, coe_sup, ← add_sub, mul_add, mul_sub, (P.prop.commute Q.prop).eq,
      ← mul_assoc, Q.prop.proj.eq, add_sub_cancel]
  sup_le P Q R := by
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_sup, coe_inf, coe_sup, ← add_sub, add_mul,
      sub_mul, mul_assoc]
    intro h₁ h₂
    rw [← h₂, ← h₁]
  inf_le_left P Q := by
    rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, (Q.prop.commute P.prop).eq, ← mul_assoc,
      P.prop.proj.eq]
  inf_le_right P Q := by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq]
  le_inf P Q R := by
    rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_inf, coe_inf, ← mul_assoc]
    intro h₁ h₂
    rw [← h₁, ← h₂]

instance Subtype.distribLattice [FaithfulSMul M X] :
    DistribLattice { P : M // IsLprojection X P } where
  le_sup_inf P Q R := by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, ← add_sub, ← add_sub, ← compl_mul, ← compl_mul, add_mul,
        mul_add, (Pᶜ.prop.commute Q.prop).eq, mul_add, ← mul_assoc, mul_assoc (Q: M),
        (Pᶜ.prop.commute P.prop).eq, mul_compl_self, zero_mul, mul_zero,
        zero_add, add_zero, ← mul_assoc, mul_assoc (Q : M), P.prop.proj.eq, Pᶜ.prop.proj.eq,
        mul_assoc, (Pᶜ.prop.commute R.prop).eq, ← mul_assoc]
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = (P : M) + ↑Q * ↑R * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, ← compl_mul, ←
        compl_mul, ← compl_mul, (Pᶜ.prop.commute (Q ⊓ R).prop).eq, coe_inf, mul_assoc,
        distrib_lattice_lemma, (Q.prop.commute R.prop).eq, distrib_lattice_lemma]
    rw [le_def, e₁, coe_inf, e₂]

instance Subtype.BooleanAlgebra [FaithfulSMul M X] :
    BooleanAlgebra { P : M // IsLprojection X P } :=
-- Porting note: use explicitly specified instance names
  { IsLprojection.Subtype.hasCompl,
    IsLprojection.Subtype.sdiff,
    IsLprojection.Subtype.boundedOrder with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
        (by
          rw [coe_top, coe_sup, coe_compl, add_sub_cancel, ← coe_compl, mul_compl_self,
            sub_zero])).le
    sdiff_eq := fun P Q => Subtype.ext <| by rw [coe_sdiff, ← coe_compl, coe_inf] }

end IsLprojection

variable {𝕜 A F : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup A]
variable [Module 𝕜 X] [NormedSpace 𝕜 A]

lemma range_prod_of_commute {P Q : (NormedSpace.Dual 𝕜 A) →L[𝕜] (NormedSpace.Dual 𝕜 A)}
    (h : Commute P Q) : Set.range (P * Q) ⊆ Set.range P ∩ Set.range Q := by
  · simp only [Set.le_eq_subset, Set.subset_inter_iff]
    constructor
    · exact Set.range_comp_subset_range ⇑Q ⇑P
    · rw [commute_iff_eq] at h
      rw [h]
      exact Set.range_comp_subset_range ⇑P ⇑Q

lemma proj_apply (P : (NormedSpace.Dual 𝕜 A) →L[𝕜] (NormedSpace.Dual 𝕜 A)) (hP : IsIdempotentElem P)
    (a : (NormedSpace.Dual 𝕜 A)) (ha: a ∈ Set.range P) : P a = a := by
  cases' ha with c hc
  rw [← hc]
  have e2 : P (P c) = (P * P) c := rfl
  rw [e2]
  rw [hP.eq]

lemma IsIdempotentElem.range_prod__of_commute
    {P Q : (NormedSpace.Dual 𝕜 A) →L[𝕜] (NormedSpace.Dual 𝕜 A)} (hPQ : Commute P Q)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Set.range (P * Q) = Set.range P ∩ Set.range Q := by
  rw [le_antisymm_iff]
  constructor
  · simp only [Set.le_eq_subset]
    exact range_prod_of_commute hPQ
  · intro a ha
    simp only [ContinuousLinearMap.coe_mul, Set.mem_range, Function.comp_apply]
    use a
    rw [proj_apply Q hQ]
    rw [proj_apply P hP]
    apply ha.1
    apply ha.2

lemma IsLprojection.range_inter (P Q : { P : (NormedSpace.Dual 𝕜 A) →L[𝕜]
    (NormedSpace.Dual 𝕜 A) // IsLprojection (NormedSpace.Dual 𝕜 A) P }) :
    Set.range P.val ∩ Set.range Q.val = Set.range (P ⊓ Q).val := by
  rw [← IsIdempotentElem.range_prod__of_commute (IsLprojection.commute P.prop Q.prop)
    P.prop.1 Q.prop.1]
  rfl

lemma IsLprojection.range_sum (P Q : { P : (NormedSpace.Dual 𝕜 A) →L[𝕜]
    (NormedSpace.Dual 𝕜 A) // IsLprojection (NormedSpace.Dual 𝕜 A) P }) :
    LinearMap.range P.val + LinearMap.range Q.val = LinearMap.range (P ⊔ Q).val := by
  rw [le_antisymm_iff]
  constructor
  · intro z hz
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hz
    simp only [LinearMap.mem_range, exists_exists_eq_and] at hz
    cases' hz with x hx
    cases' hx with y hxy
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply, Function.comp_apply]
    use z
    rw [← hxy]
    simp only [map_add]
    rw [← Function.comp_apply (f := P.val), ← ContinuousLinearMap.coe_mul, P.prop.proj]
    rw [← Function.comp_apply (f := Q.val) (g := Q.val), ← ContinuousLinearMap.coe_mul, Q.prop.proj]
    rw [← Function.comp_apply (f := Q.val) (g := P.val), ← ContinuousLinearMap.coe_mul]
    rw [IsLprojection.commute Q.prop P.prop]
    rw [← Function.comp_apply (f := P.val) (g := (P.val * Q.val)), ← ContinuousLinearMap.coe_mul]
    rw [← mul_assoc]
    rw [P.prop.proj]
    abel
  · intro z hz
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply,
      Function.comp_apply] at hz
    cases' hz with x hx
    have e1 : z = P.val (x - Q.val x) + Q.val x := by
      rw [map_sub, ← hx]
      abel
    rw [e1]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _ )

/--
A closed subspace of a Banach space is said to be an M-ideal if the topological annihilator is the
range of an L-projection.
-/
structure IsMideal (m : Submodule 𝕜 A) : Prop where
  Closed: IsClosed (m : Set A)
  Lproj:  ∃ (P : (NormedSpace.Dual 𝕜 A) →L[𝕜] (NormedSpace.Dual 𝕜 A)),
    IsLprojection (NormedSpace.Dual 𝕜 A) P ∧
      (LinearMap.range P) = NormedSpace.polarSubmodule (E := A) 𝕜 m.toSubMulAction

open NormedSpace in
open Metric in
open Submodule in
open scoped ComplexOrder in
lemma unit_ball_conv (m₁ m₂ : Submodule 𝕜 A) (h₁ : IsMideal m₁) (h₂ : IsMideal m₂) :
    ↑(polarSubmodule 𝕜 m₁.toSubMulAction + polarSubmodule 𝕜 m₂.toSubMulAction) ∩ closedBall 0 1 =
    convexHull ℝ (polar 𝕜 m₁ ∩ closedBall 0 1 ∪ polar 𝕜 m₂ ∩ closedBall (0 : Dual 𝕜 A) 1) := by
  rw [le_antisymm_iff]
  constructor
  · cases' h₁.Lproj with E₁ hE₁
    cases' h₂.Lproj with E₂ hE₂
    --rw [(polarSubmodule_eq_polar 𝕜 m₁.toSubMulAction)]
    rw [ ← hE₁.2, ← hE₂.2 ]
    rw [ (IsLprojection.range_sum ⟨E₁,hE₁.1⟩ ⟨E₂,hE₂.1⟩)]
    intro x' hx'
    simp at hx'
    cases' hx'.1 with x hx
    --rw [← hx]
    let y := E₁ x
    let z := E₂ ((1 - E₁) x)
    have e1 : y ∈ polar 𝕜 ↑m₁ ∩ closedBall 0 1 := by
      simp only [Set.mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · have e : polar 𝕜 ↑m₁ = SetLike.coe (LinearMap.range E₁) := by
          rw [hE₁.2]
          rfl
        rw [e]
        simp only [SetLike.mem_coe, LinearMap.mem_range, exists_apply_eq_apply]
    have e3 : x' = y + z := calc
      x' = E₁ x + E₂ x - E₁ (E₂ x) := by rw [hx]
      _ = E₁ x + E₂ x - (E₁ ∘ E₂) x := rfl
      _ = E₁ x + E₂ x - (E₁ * E₂) x := rfl
      _ = E₁ x + E₂ x - (E₂ * E₁) x := by rw [IsLprojection.commute hE₁.1 hE₂.1]
      _ = E₁ x + E₂ x - E₂ (E₁ x) := rfl
      _ = E₁ x + (E₂ x - E₂ (E₁ x)) := by exact add_sub_assoc (E₁ x) (E₂ x) (E₂ (E₁ x))
      _ = E₁ x + E₂ (x - E₁ x) := by rw [map_sub]
      _ = y + z := rfl
      --rw  [← hx]
      --sorry
      --rw [← (LinearMap.comp_apply x)]


    --rw [convexHull]
    sorry
  · simp only [Submodule.add_eq_sup, Set.le_eq_subset, Set.subset_inter_iff]
    constructor
    · apply convexHull_min _
      exact fun _ hx _ hy _ _ _ _ _ => add_mem (smul_of_tower_mem _ _ hx) (smul_of_tower_mem _ _ hy)
      simp only [Set.union_subset_iff]
      exact ⟨subset_trans
          (Set.inter_subset_left (s := SetLike.coe (polarSubmodule 𝕜 m₁.toSubMulAction)))
          (SetLike.coe_subset_coe.mpr le_sup_left),
        subset_trans
          (Set.inter_subset_left (s := SetLike.coe (polarSubmodule 𝕜 m₂.toSubMulAction)))
          (SetLike.coe_subset_coe.mpr le_sup_right)⟩
    · apply convexHull_min
      rw [← Set.union_inter_distrib_right]
      exact Set.inter_subset_right
      exact convex_closedBall _ _



/-
lemma IsMideal.inter (m₁ m₂ : Submodule 𝕜 A) (h₁ : IsMideal m₁) (h₂ : IsMideal m₂) :
    WeakDual.polar 𝕜 (m₁ ⊓ m₂) = closure (WeakDual.polar 𝕜 m₁ + WeakDual.polar (E := A) 𝕜 m₂) :=
    sorry
-/

/- The M-ideals are a sub-lattice of the lattice of submodules -/
/-
lemma IsMideal.isSublattice : IsSublattice {m : Submodule 𝕜 A | IsMideal m } where
  supClosed m₁ hm₁ m₂ hm₂ := by
    rw [Set.mem_setOf_eq] at *
    constructor
    · sorry
    · sorry
  infClosed m₁ hm₁ m₂ hm₂ := by
    rw [Set.mem_setOf_eq] at *
    constructor
    · sorry
    · sorry
-/
