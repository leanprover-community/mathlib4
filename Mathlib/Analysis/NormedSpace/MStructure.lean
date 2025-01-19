/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Analysis.Normed.Lp.ProdLp

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

section Lsummands

variable (G : Type*) [NormedAddCommGroup G]

#check CompleteBooleanAlgebra

lemma unique_Lcomplement (L K : AddSubgroup G) (h₁ : L ⊔ K = ⊤)
    (h₂ : ∀ x ∈ L, ∀ y ∈ K, ‖x‖ + ‖y‖ = ‖x + y‖) : K = {y | ∀ x ∈ L, ‖x + y‖ = ‖x‖ + ‖y‖} := by
  ext y
  constructor
  · intro hy x hx
    rw [(h₂ x hx y hy)]
  · intro h
    have hy1 : y ∈ L ⊔ K := by
      rw [h₁]
      exact AddSubgroup.mem_top y
    obtain ⟨x₁,⟨hx₁,⟨y₁,⟨hy₁,hx₁y₁y⟩⟩⟩⟩ := AddSubgroup.mem_sup.mp hy1
    have e2 : ‖y₁‖ = ‖x₁‖ + ‖y‖ := by
      rw [← norm_neg x₁, ← (h _ (AddSubgroup.neg_mem L hx₁)), ← hx₁y₁y, neg_add_cancel_left]
    rw [← hx₁y₁y, ← (h₂ _ hx₁ _ hy₁), ← add_assoc, ← two_smul ℕ] at e2
    simp only [nsmul_eq_mul, Nat.cast_ofNat, self_eq_add_left, mul_eq_zero, OfNat.ofNat_ne_zero,
      norm_eq_zero, false_or] at e2
    rw [e2, zero_add] at hx₁y₁y
    rw [← hx₁y₁y]
    exact hy₁

structure IsLsummand  (L : AddSubgroup G) : Prop where
  compl' : ∃ (K : AddSubgroup G), L ⊔ K = ⊤ ∧ ∀ x ∈ L, ∀ y ∈ K, ‖x‖ + ‖y‖ = ‖x + y‖

def IsLsummand.compl {L : AddSubgroup G} (h : IsLsummand G L) : AddSubgroup G where
  carrier := {y : G | ∀ x ∈ L, ‖x + y‖ = ‖x‖ + ‖y‖}
  add_mem' := by
    obtain ⟨K, ⟨hK₁, hK₂⟩⟩ := h.compl'
    rw [← unique_Lcomplement G L K hK₁ hK₂]
    intro a b ha hb
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, add_zero, norm_zero, implies_true]
  neg_mem' := by
    simp only [Set.mem_setOf_eq, norm_neg, sub_neg_eq_add]
    intro z hz y hy
    rw [← norm_neg, neg_add, neg_neg, (hz _ (AddSubgroup.neg_mem L hy)), norm_neg]

lemma IsLsummand.Lnorm {L : AddSubgroup G} (h : IsLsummand G L)
    {x y : G} (hx : x ∈ L) (hy : y ∈ h.compl) : ‖x‖ + ‖y‖ = ‖x + y‖ := by
  rw [hy x hx]

lemma IsLsummand.sup_top {L : AddSubgroup G} (h : IsLsummand G L) : L ⊔ h.compl = ⊤ := by
  obtain ⟨K, ⟨hK₁, hK₂⟩⟩ := h.compl'
  rw [compl]
  simp_rw [← unique_Lcomplement G L K hK₁ hK₂]
  exact hK₁

/-- A shorthand for the type of L-projections. -/
abbrev Lsummands : Type _ := { f : AddSubgroup G // IsLsummand G f }

instance Subtype.hasCompl : HasCompl (Lsummands G) :=
  ⟨fun L => {
    val := L.prop.compl
    property := by
      use L
      obtain ⟨K, ⟨hK₁, hK₂⟩⟩ := L.prop.compl'
      have e1 : K = {y | ∀ x ∈ L.val, ‖x + y‖ = ‖x‖ + ‖y‖} := by
        rw [unique_Lcomplement G L K hK₁ hK₂]
      have e2 : L.prop.compl = K := by
        apply SetLike.coe_injective'
        rw [unique_Lcomplement G L K hK₁ hK₂]
        rfl
      constructor
      · rw [sup_comm, e2, hK₁]
      · intro x hx
        rw [e2] at hx
        intro y hy
        rw [add_comm, (hK₂ _ hy _ hx), add_comm]}⟩

instance : PartialOrder (Lsummands G) := Subtype.partialOrder fun f ↦ IsLsummand G f

instance : Bot (Lsummands G) where
  bot := ⟨⊥,⟨⟨⊤,by simp_all⟩⟩⟩

instance : Top (Lsummands G) where
  top := ⟨⊤,⟨⟨⊥,by simp_all⟩⟩⟩

lemma Lsummand.IsCompl {L : AddSubgroup G} (h : IsLsummand G L) : IsCompl L h.compl where
  disjoint := by
    rw [Disjoint]
    intro K hKL hK
    intro x hx
    simp
    have e1 : ‖x + (-x)‖ = ‖x‖ + ‖-x‖ := by
      rw [h.Lnorm]
      exact hKL hx
      exact AddSubgroup.neg_mem (IsLsummand.compl G h) (hK hx)
    have e2 : ‖x‖ + ‖-x‖ = 0 := by
      rw [← e1, add_neg_cancel, norm_zero]
    have e3 : 2•‖x‖ = 0 := calc
      2•‖x‖ = ‖x‖ + ‖-x‖ := by rw [two_smul, ← norm_neg]
      _ = 0 := by rw [← e1, add_neg_cancel, norm_zero]
    simp at e3
    exact e3
  codisjoint := by
    rw [Codisjoint]
    intro K hKL hK
    rw [← h.sup_top]
    simp_all only [sup_le_iff, and_self]

variable {L : AddSubgroup G} (h : IsLsummand G L)

#check WithLp 1 (L × h.compl)


lemma WithLp.prod_norm_eq_of_1 (x : WithLp 1 (L × h.compl)) :
    ‖x‖ = ‖(WithLp.equiv 1 _ x).fst‖ + ‖(WithLp.equiv 1 _ x).snd‖ := by
  rw [WithLp.prod_norm_eq_of_nat 1 Nat.cast_one.symm, pow_one, pow_one, WithLp.equiv_fst,
    WithLp.equiv_snd, Nat.cast_one, (div_self one_ne_zero), Real.rpow_one]

def l1map : WithLp 1 (L × h.compl) →+ G where
  toFun := fun a => a.1 +a.2
  map_add' x y := by
    simp only [WithLp.add_fst, AddSubgroup.coe_add, WithLp.add_snd]
    abel
  map_zero' := by
    simp? [Prod.fst_zero, ZeroMemClass.coe_zero, Prod.snd_zero, add_zero]

lemma surjective : Function.Surjective (l1map G h) := by
  intro y
  have hy1 : y ∈ L ⊔ h.compl := by
    rw [h.sup_top]
    trivial
  obtain ⟨x₁,⟨hx₁,⟨y₁,⟨hy₁,hx₁y₁y⟩⟩⟩⟩ := AddSubgroup.mem_sup.mp hy1
  exact ⟨(⟨x₁,hx₁⟩,⟨y₁,hy₁⟩), hx₁y₁y⟩


-- There is `LinearIsometry` - but that is for module homomorphisms

--lemma li (x : WithLp 1 (L × h.compl)) : l1map G h →ₗᵢ[R] where

lemma l1map_isometry : Isometry (l1map G h) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro x
  rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk, l1map, ← (h.Lnorm G x.1.prop x.2.prop),
    WithLp.prod_norm_eq_of_1]
  rfl

lemma bijection : Function.Bijective (l1map G h) := ⟨(l1map_isometry G h).injective, surjective G h⟩

def prodEquivₗᵢ : WithLp 1 (L × h.compl) ≃+ G where
  toFun a := a.1 +a.2
  invFun y := by
      have hy1 : y ∈ L ⊔ h.compl := by
        rw [h.sup_top]
        trivial
      obtain ⟨x₁,⟨hx₁,⟨y₁,⟨hy₁,hx₁y₁y⟩⟩⟩⟩ := AddSubgroup.mem_sup.mp hy1

  map_add' _f _g := rfl
  --norm_map' := prod_norm_equiv

@[simp] theorem prod_nnnorm_equiv (f : WithLp 1 (L × h.compl)) : ‖WithLp.equiv ⊤ _ f‖₊ = ‖f‖₊ := by
  rw [prod_nnnorm_eq_add, Prod.nnnorm_def', WithLp.equiv_fst, WithLp.equiv_snd]




lemma L1_norm_inr (x : G) : ‖(WithLp.equiv 1 (L × h.compl)).symm x‖ = ‖x‖ := by
  simp [unitization_norm_def]

--#check WithLp.instUnitizationNormedAddCommGroup

-- See Mathlib/Analysis/Normed/Algebra/Unitization.lean

lemma Lsummand.IsClosed {L : AddSubgroup G} (h : IsLsummand G L) : IsClosed L := by


-- This is almost what we want...
--#check Submodule.linearProjOfClosedCompl

end Lsummands

variable {M : Type*} [Ring M]
variable (X : Type*) [NormedAddCommGroup X] [Module M X]

/-- A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
structure IsLprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Lnorm : ∀ x : X, ‖P • x‖ + ‖(1 - P) • x‖ = ‖x‖

variable (M) in
/-- A shorthand for the type of L-projections. -/
abbrev Lprojections : Type _ := { f : M // IsLprojection X f }

notation "ℙᴸ[" M "](" X ")" => Lprojections M X

/-- A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

Note that we write `P • x` instead of `P x` for reasons described in the module docstring.
-/
structure IsMprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Mnorm : ∀ x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖

variable (M) in
/-- A shorthand for the type of L-projections. -/
abbrev Mprojections : Type _ := { f : M // IsMprojection X f }

notation "ℙᴹ[" M "](" X ")" => Mprojections M X

variable {X}

namespace IsLprojection

-- Porting note: The literature always uses uppercase 'L' for L-projections
theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm, sub_sub_cancel]
    exact h.Lnorm x⟩

theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

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
            rw [← h₁.Lnorm, h₃.Lnorm, ← h₃.Lnorm ((1 - P) • R • x), sub_smul 1 P, one_smul,
              smul_sub, mul_smul]
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

theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [← h₂.Lnorm x, ← h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]

theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring



-- Porting note: Advice is to explicitly name instances
-- https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#some-common-fixes
instance Subtype.hasCompl : HasCompl ℙᴸ[M](X) :=
  ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]
theorem coe_compl (P : ℙᴸ[M](X)) : ↑Pᶜ = (1 : M) - ↑P :=
  rfl

instance Subtype.inf [FaithfulSMul M X] : Min ℙᴸ[M](X) :=
  ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]
theorem coe_inf [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    ↑(P ⊓ Q) = (↑P : M) * ↑Q :=
  rfl

instance Subtype.sup [FaithfulSMul M X] : Max ℙᴸ[M](X) :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]
theorem coe_sup [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    ↑(P ⊔ Q) = (↑P : M) + ↑Q - ↑P * ↑Q :=
  rfl

instance Subtype.sdiff [FaithfulSMul M X] : SDiff ℙᴸ[M](X) :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]
theorem coe_sdiff [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    ↑(P \ Q) = (↑P : M) * (1 - ↑Q) :=
  rfl

instance Subtype.partialOrder [FaithfulSMul M X] : PartialOrder ℙᴸ[M](X) where
  le P Q := (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁, mul_assoc, ← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.eq (by convert (P.prop.commute Q.prop).eq)

theorem le_def [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    P ≤ Q ↔ (P : M) = ↑(P ⊓ Q) :=
  Iff.rfl

instance Subtype.zero : Zero ℙᴸ[M](X) :=
  ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]
theorem coe_zero : ↑(0 : ℙᴸ[M](X)) = (0 : M) :=
  rfl

instance Subtype.one : One ℙᴸ[M](X) :=
  ⟨⟨1, sub_zero (1 : M) ▸ (0 : ℙᴸ[M](X)).prop.Lcomplement⟩⟩

@[simp]
theorem coe_one : ↑(1 : ℙᴸ[M](X)) = (1 : M) :=
  rfl

instance Subtype.boundedOrder [FaithfulSMul M X] : BoundedOrder ℙᴸ[M](X) where
  top := 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]
theorem coe_bot [FaithfulSMul M X] :
    -- Porting note: Manual correction of name required here
    ↑(BoundedOrder.toOrderBot.toBot.bot : ℙᴸ[M](X)) = (0 : M) :=
  rfl

@[simp]
theorem coe_top [FaithfulSMul M X] :
    -- Porting note: Manual correction of name required here
    ↑(BoundedOrder.toOrderTop.toTop.top : ℙᴸ[M](X)) = (1 : M) :=
  rfl

theorem compl_mul {P : ℙᴸ[M](X)} {Q : M} : ↑Pᶜ * Q = Q - ↑P * Q := by
  rw [coe_compl, sub_mul, one_mul]

theorem mul_compl_self {P : ℙᴸ[M](X)} : (↑P : M) * ↑Pᶜ = 0 := by
  rw [coe_compl, P.prop.proj.mul_one_sub_self]

theorem compl_mul_self {P : ℙᴸ[M](X)} : ↑Pᶜ * (↑P : M) = 0 := by
  rw [coe_compl, sub_mul, one_mul, P.prop.proj.eq, sub_self]

theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : ℙᴸ[M](X)} :
    ((↑P : M) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = ↑P + ↑Q * ↑R * ↑Pᶜ := by
  rw [add_mul, mul_add, mul_add, (mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ)),
    ← mul_assoc (R : M) (↑Q * ↑R) _, ← coe_inf Q, (Pᶜ.prop.commute R.prop).eq,
    ((Q ⊓ R).prop.commute Pᶜ.prop).eq, (R.prop.commute (Q ⊓ R).prop).eq, coe_inf Q,
    mul_assoc (Q : M), ← mul_assoc, mul_assoc (R : M), (Pᶜ.prop.commute P.prop).eq, mul_compl_self,
    zero_mul, mul_zero, zero_add, add_zero, ← mul_assoc, P.prop.proj.eq,
    R.prop.proj.eq, ← coe_inf Q, mul_assoc, ((Q ⊓ R).prop.commute Pᶜ.prop).eq, ← mul_assoc,
    Pᶜ.prop.proj.eq]

-- Porting note: In mathlib3 we were able to directly show that `{ P : M // IsLprojection X P }` was
--  an instance of a `DistribLattice`. Trying to do that in mathlib4 fails with "error:
-- (deterministic) timeout at 'whnf', maximum number of heartbeats (800000) has been reached"
-- My workaround is to show instance Lattice first
instance [FaithfulSMul M X] : Lattice ℙᴸ[M](X) where
  sup := max
  inf := min
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

instance Subtype.distribLattice [FaithfulSMul M X] : DistribLattice ℙᴸ[M](X) where
  le_sup_inf P Q R := by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, ← add_sub, ← add_sub, ← compl_mul, ← compl_mul, add_mul,
        mul_add, (Pᶜ.prop.commute Q.prop).eq, mul_add, ← mul_assoc, mul_assoc (Q : M),
        (Pᶜ.prop.commute P.prop).eq, mul_compl_self, zero_mul, mul_zero,
        zero_add, add_zero, ← mul_assoc, mul_assoc (Q : M), P.prop.proj.eq, Pᶜ.prop.proj.eq,
        mul_assoc, (Pᶜ.prop.commute R.prop).eq, ← mul_assoc]
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = (P : M) + ↑Q * ↑R * ↑Pᶜ := by
      rw [coe_inf, coe_sup, coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, ← compl_mul, ←
        compl_mul, ← compl_mul, (Pᶜ.prop.commute (Q ⊓ R).prop).eq, coe_inf, mul_assoc,
        distrib_lattice_lemma, (Q.prop.commute R.prop).eq, distrib_lattice_lemma]
    rw [le_def, e₁, coe_inf, e₂]

instance Subtype.BooleanAlgebra [FaithfulSMul M X] : BooleanAlgebra ℙᴸ[M](X) :=
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

theorem contractive {P : M} (h : IsLprojection X P) (x : X) : ‖P • x‖ ≤ ‖x‖ := by
  simp only [← (h.Lnorm x), le_add_iff_nonneg_right, norm_nonneg]

/-
instance : FunLike ℙᴸ[M](X) X X where
  coe f := fun x => f.val • x
  coe_injective' P Q h := Subtype.eq (by
    simp at h
    apply DFunLike.coe_fn_eq.mp
  ) --(DFunLike.coe_fn_eq.mp h)
-/

theorem _root_.Lprojections.Lnorm (P : ℙᴸ[M](X)) (x : X) : ‖P.val • x‖  + ‖Pᶜ.val • x‖ = ‖x‖ := by
  rw [coe_compl, P.prop.Lnorm]


open Pointwise
lemma _root_.IsIdempotentElem.mem_range_iff_self_smul {P : M} (h : IsIdempotentElem P) (x : X) :
    (x ∈ (P • (⊤ : AddSubgroup X) )) ↔ (P • x = x) := by
  constructor
  · intro h
    obtain ⟨y,⟨_,hy⟩⟩ := h
    simp at hy
    rw [← hy]
    rw [← smul_assoc, smul_eq_mul]
    rw [h.eq]
  · intro h
    rw [← h]
    apply AddSubgroup.smul_mem_pointwise_smul
    trivial


def _root_.Lprojections.range (P : ℙᴸ[M](X)) : IsLsummand X (P.val • ⊤) where
  compl' := by
    use (Pᶜ.val • ⊤)
    constructor
    · ext x
      constructor
      · intro h
        trivial
      · intro h
        rw [AddSubgroup.mem_sup]
        use P.val • x
        constructor
        · apply AddSubgroup.smul_mem_pointwise_smul
          exact h
        · use Pᶜ.val • x
          constructor
          · apply AddSubgroup.smul_mem_pointwise_smul
            exact h
          · simp only [coe_compl, smul_add_one_sub_smul]
    · intro x hx y hy
      rw [P.prop.proj.mem_range_iff_self_smul] at hx
      rw [Pᶜ.prop.proj.mem_range_iff_self_smul] at hy
      rw [← P.Lnorm (x+y)]
      apply congr_arg₂
      · rw [smul_add, hx]
        apply congr_arg
        rw [self_eq_add_right, ← hy, ← smul_assoc, smul_eq_mul, mul_compl_self, zero_smul]
      · rw [smul_add, hy]
        apply congr_arg
        rw [self_eq_add_left, ← hx, ← smul_assoc, smul_eq_mul, compl_mul_self, zero_smul]
















/-
instance : FunLike { P : M // IsLprojection X P } X X where
  coe f := fun x => f.val • x
  coe_injective' _ _ h := Subtype.eq (by aesop?)--(DFunLike.coe_fn_eq.mp h)

variables (P Q : { P : M // IsLprojection X P })

open Pointwise
#check P.val • (Set.univ)
-/


open Pointwise
lemma range_inter [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    (P.val • ⊤) ⊓ (Q.val • ⊤) = ((P ⊓ Q).val • (⊤ : AddSubgroup X)) := by
  have h1 : Commute P.val Q.val := P.prop.commute Q.prop
  rw [← (IsIdempotentElem.range_prod_of_commute P.prop.1 Q.prop.1 h1)]
  rfl

#check Subgroup.smul_sup

/-
instance _root_.Lsummands.Subtype.sup [FaithfulSMul M X] : Max (Lsummands X) :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩
-/

lemma range_sum [FaithfulSMul M X] (P Q : ℙᴸ[M](X)) :
    (↑P.range : AddSubgroup X) ⊔ Q.range = (P ⊔ Q).range := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hz
    simp only [LinearMap.mem_range, exists_exists_eq_and] at hz
    obtain ⟨x,⟨y,hxy⟩⟩ := hz
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply, Function.comp_apply]
    use z
    rw [← hxy]
    simp only [map_add]
    simp only [LinearMap.sub_apply, LinearMap.add_apply] --, LinearMap.mul_apply]
    rw [← LinearMap.mul_apply, P.prop.proj]
    --rw [← Function.comp_apply (f := P.val)] --, P.prop.proj]
    --simp only [Function.comp_apply, LinearMap.mul_apply]
    rw [← LinearMap.mul_apply (f := Q.val) (g := Q.val), Q.prop.proj]
    --rw [← Function.mul_apply (f := Q.val) (g := P.val)]
    rw [← Q.prop.commute P.prop]
    --rw [← Function.mul_apply (f := P.val) (g := (P.val * Q.val)), ← ContinuousLinearMap.coe_mul]
    rw [← LinearMap.mul_apply (f := (Q.val * P.val))]
    rw [mul_assoc]
    rw [P.prop.proj]
    rw [← LinearMap.mul_apply]
    rw [← LinearMap.mul_apply]
    rw [← LinearMap.mul_apply]
    rw [Q.prop.commute P.prop]
    rw [mul_assoc]
    rw [Q.prop.proj]
    abel
  · intro z hz
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply,
      Function.comp_apply] at hz
    obtain ⟨x,hx⟩ := hz
    have e1 : z = P.val (x - Q.val x) + Q.val x := by
      rw [map_sub, ← hx]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.mul_apply]
      abel
    rw [e1]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _ )


end IsLprojection

variable {𝕜 A F : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup A] [NormedSpace 𝕜 A]

theorem IsLprojection.contractive2 {P : A →L[𝕜] A} (h : IsLprojection A P) : ‖P‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_le_iff (zero_le_one' ℝ)).mpr
    (fun x => by simp only [(h.Lnorm x), ContinuousLinearMap.smul_def, ContinuousLinearMap.coe_sub',
      Pi.sub_apply, ContinuousLinearMap.one_apply, one_mul, le_add_iff_nonneg_right, norm_nonneg])

/-
/-- The subtype of L-projections -/
--notation "Pₗ[" 𝕜 "](" A ")" => { P : A →L[𝕜] A // IsLprojection A P }
--notation "Pₗ[" 𝕜 "](" A ")" => { P : Module.End 𝕜 A // IsLprojection A P }
-/

variable (P : Pₗ[𝕜](A))

instance : FunLike Pₗ[𝕜](A) A A where
  coe f := f.val
  coe_injective' _ _ h := Subtype.eq (DFunLike.coe_fn_eq.mp h)


/-
lemma commute {P Q : A →L[𝕜] A} : Commute P Q ↔ Commute (P : (Module.End 𝕜 A)) ↑Q := by
  constructor
  · intro h
    ext x
    simp only [LinearMap.mul_apply, ContinuousLinearMap.coe_coe]
    calc
      P (Q x) = (P * Q) x := rfl
      _ = (Q * P) x := congrFun (congrArg DFunLike.coe h) x
      _ = Q (P x) := rfl
  · intro h
    ext x
    --rw [Commute, SemiconjBy] at h
    simp_all only [ContinuousLinearMap.coe_mul, Function.comp_apply]
    calc
      P (Q x) = (P : (Module.End 𝕜 A)) (Q x) := rfl
      _ = ((P : (Module.End 𝕜 A)) * Q) x := rfl
      _ = (Q * (P : (Module.End 𝕜 A))) x := by rw [h]
      _ = Q (P x) := rfl
-/

lemma IsLprojection.range_sum (P Q : Pₗ[𝕜](NormedSpace.Dual 𝕜 A)) :
    LinearMap.range P.val + LinearMap.range Q.val = LinearMap.range (P ⊔ Q).val := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hz
    simp only [LinearMap.mem_range, exists_exists_eq_and] at hz
    obtain ⟨x,⟨y,hxy⟩⟩ := hz
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply, Function.comp_apply]
    use z
    rw [← hxy]
    simp only [map_add]
    simp only [LinearMap.sub_apply, LinearMap.add_apply] --, LinearMap.mul_apply]
    rw [← LinearMap.mul_apply, P.prop.proj]
    --rw [← Function.comp_apply (f := P.val)] --, P.prop.proj]
    --simp only [Function.comp_apply, LinearMap.mul_apply]
    rw [← LinearMap.mul_apply (f := Q.val) (g := Q.val), Q.prop.proj]
    --rw [← Function.mul_apply (f := Q.val) (g := P.val)]
    rw [← Q.prop.commute P.prop]
    --rw [← Function.mul_apply (f := P.val) (g := (P.val * Q.val)), ← ContinuousLinearMap.coe_mul]
    rw [← LinearMap.mul_apply (f := (Q.val * P.val))]
    rw [mul_assoc]
    rw [P.prop.proj]
    rw [← LinearMap.mul_apply]
    rw [← LinearMap.mul_apply]
    rw [← LinearMap.mul_apply]
    rw [Q.prop.commute P.prop]
    rw [mul_assoc]
    rw [Q.prop.proj]
    abel
  · intro z hz
    simp only [coe_sup, LinearMap.mem_range, ContinuousLinearMap.coe_sub',
      ContinuousLinearMap.coe_mul, Pi.sub_apply, ContinuousLinearMap.add_apply,
      Function.comp_apply] at hz
    obtain ⟨x,hx⟩ := hz
    have e1 : z = P.val (x - Q.val x) + Q.val x := by
      rw [map_sub, ← hx]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.mul_apply]
      abel
    rw [e1]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _ )

/--
A closed subspace of a Banach space is said to be an M-ideal if the topological annihilator is the
range of an L-projection.
-/
structure IsMideal (m : Submodule 𝕜 A) : Prop where
  Closed: IsClosed (m : Set A)
  Lproj:  ∃ (P : Pₗ[𝕜](NormedSpace.Dual 𝕜 A)),
    (LinearMap.range P.val) = NormedSpace.polarSubmodule (E := A) 𝕜 m

set_option maxHeartbeats 400000
open NormedSpace in
open Metric in
open Submodule in
open scoped ComplexOrder in
lemma unit_ball_conv (m₁ m₂ : Submodule 𝕜 A) (h₁ : IsMideal m₁) (h₂ : IsMideal m₂) :
    ↑(polarSubmodule 𝕜 m₁ + polarSubmodule 𝕜 m₂) ∩ closedBall 0 1 =
    convexHull ℝ (polar 𝕜 m₁ ∩ closedBall 0 1 ∪ polar 𝕜 m₂ ∩ closedBall (0 : Dual 𝕜 A) 1) :=
  le_antisymm
  ( by
    obtain ⟨P₁,hE₁⟩ := h₁.Lproj
    obtain ⟨P₂,hE₂⟩ := h₂.Lproj
    let E := P₁ ⊔ P₂
    rw [ ← hE₁, ← hE₂, (IsLprojection.range_sum P₁ P₂)]
    intro x hx
    let E₁ := P₁.val
    let E₂ := P₂.val
    let y := E₁ x
    let z := E₂ ((1 - E₁) x)
    have e3 : x = y + z := calc
      x = E x := (Set.proj_apply2 _ E.prop.proj x (Set.mem_of_mem_inter_left hx)).symm
      _ = E₁ x + E₂ x - (E₁ * E₂) x := rfl
      _ = E₁ x + E₂ x - (E₂ * E₁) x := by rw [P₁.prop.commute P₂.prop]
      _ = E₁ x + E₂ x - E₂ (E₁ x) := rfl
      _ = E₁ x + (E₂ x - E₂ (E₁ x)) := add_sub_assoc (E₁ x) (E₂ x) (E₂ (E₁ x))
      _ = E₁ x + E₂ (x - E₁ x) := by rw [map_sub]
      _ = y + z := rfl
    have e4 :  ‖y‖ + ‖z‖ = ‖x‖ := le_antisymm
      (calc
        ‖y‖ + ‖z‖ = ‖E₁ x‖ + ‖E₂ ((1 - E₁) x)‖ := rfl
        _ ≤ ‖E₁ x‖ + ‖(E₂.val)‖ * ‖(1 - E₁) x‖ :=  by
          rw [add_le_add_iff_left]; exact ContinuousLinearMap.le_opNorm E₂ ((1 - E₁) x)
        _ ≤ ‖E₁ x‖ + 1 * ‖(1 - E₁) x‖ := by
          rw [add_le_add_iff_left]
          exact mul_le_mul_of_nonneg_right P₂.prop.contractive
            (ContinuousLinearMap.opNorm_nonneg ((1 - E₁) x))
        _ ≤ ‖E₁ x‖ + ‖(1 - E₁) x‖ := by rw [one_mul]
        _ ≤ ‖E₁ • x‖ + ‖(1 - E₁) • x‖ := Preorder.le_refl (‖E₁ x‖ + ‖(1 - E₁) x‖)
        _ = ‖x‖ := by rw [← P₁.prop.Lnorm])
      (by rw [e3]; exact ContinuousLinearMap.opNorm_add_le y z)
    simp at hx
    have e1 : y ∈ polar 𝕜 ↑m₁ ∩ closedBall 0 1 := by
      simp only [Set.mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · have e : polar 𝕜 ↑m₁ = SetLike.coe (LinearMap.range E₁) := by
          rw [hE₁]
          rfl
        rw [e]
        simp only [SetLike.mem_coe, LinearMap.mem_range, exists_apply_eq_apply]
      · apply le_trans _ hx.2
        rw [← e4]
        exact ((le_add_iff_nonneg_right ‖y‖).mpr (norm_nonneg _))
    have e2 : z ∈ polar 𝕜 ↑m₂ ∩ closedBall 0 1 := by
      simp only [Set.mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · have e : polar 𝕜 ↑m₂ = SetLike.coe (LinearMap.range E₂) := by
          rw [hE₂]
          rfl
        rw [e]
        simp only [SetLike.mem_coe, LinearMap.mem_range, exists_apply_eq_apply]
      · apply le_trans _ hx.2
        rw [← e4]
        exact ((le_add_iff_nonneg_left ‖z‖).mpr (norm_nonneg _))
    rcases eq_or_ne ‖x‖ 0 with (hxz | hxnz)
    · rw [norm_eq_zero] at hxz
      rw [hxz]
      apply subset_convexHull
      simp only [Set.mem_union, Set.mem_inter_iff, mem_closedBall, dist_self, zero_le_one, and_true]
      exact Or.intro_left _ (LinearMap.zero_mem_polar (dualPairing 𝕜 A).flip ↑m₁)
    · rcases eq_or_ne ‖y‖ 0 with (hyz | hynz)
      · rw [norm_eq_zero] at hyz
        rw [e3, hyz, zero_add]
        exact subset_convexHull _ _ (Set.mem_union_right (polar 𝕜 ↑m₁ ∩ closedBall 0 1) e2)
      · rcases eq_or_ne ‖z‖ 0 with (hzz | hznz)
        · rw [norm_eq_zero] at hzz
          rw [e3, hzz, add_zero]
          exact subset_convexHull _ _ (Set.mem_union_left (polar 𝕜 ↑m₂ ∩ closedBall 0 1) e1)
        · let y₁ := (‖x‖/‖y‖) • y
          let z₁ := (‖x‖/‖z‖) • z
          have t₁ : y₁ ∈ polar 𝕜 ↑m₁ ∩ closedBall 0 1 ∪ polar 𝕜 ↑m₂ ∩ closedBall 0 1 := by
            apply Set.mem_union_left
            simp only [Set.mem_inter_iff, mem_closedBall, dist_zero_right]
            constructor
            · have e : polar 𝕜 ↑m₁ = SetLike.coe (LinearMap.range E₁) := by
                rw [hE₁]
                rfl
              rw [e]
              simp only [SetLike.mem_coe, LinearMap.mem_range]
              use y₁
              calc
              E₁ y₁ = E₁ ((‖x‖/‖y‖) • y) := rfl
              _ = (‖x‖/‖y‖) • E₁  y := ContinuousLinearMap.map_smul_of_tower E₁ (‖x‖ / ‖y‖) y
              _ = (‖x‖/‖y‖) • y := by
                rw [proj_apply E₁ P₁.prop.proj _ _]
                exact Set.mem_range_self x
              _ = y₁ := rfl
            · calc
              ‖y₁‖ = ‖(‖x‖/‖y‖) • y‖ := rfl
              --_ = |1 := by
              _ = ‖‖x‖/‖y‖‖ * ‖y‖ := norm_smul (‖x‖ / ‖y‖) y
              _ = ‖x‖/‖y‖ * ‖y‖ := by simp only [norm_div, norm_norm]
              _ = ‖x‖ := div_mul_cancel₀ ‖x‖ hynz
              _ ≤ 1 := hx.2
          have t₂ : z₁ ∈ polar 𝕜 ↑m₁ ∩ closedBall 0 1 ∪ polar 𝕜 ↑m₂ ∩ closedBall 0 1 := by
            apply Set.mem_union_right
            simp only [Set.mem_inter_iff, mem_closedBall, dist_zero_right]
            constructor
            · have e : polar 𝕜 ↑m₂ = SetLike.coe (LinearMap.range E₂) := by
                rw [hE₂]
                rfl
              rw [e]
              simp only [SetLike.mem_coe, LinearMap.mem_range]
              use z₁
              calc
              E₂ z₁ = E₂ ((‖x‖/‖z‖) • z) := rfl
              _ = (‖x‖/‖z‖) • E₂  z := ContinuousLinearMap.map_smul_of_tower E₂ (‖x‖ / ‖z‖) z
              _ = (‖x‖/‖z‖) • z := by
                rw [proj_apply E₂ P₂.prop.proj _ _]
                exact Set.mem_range_self ((1 - E₁) x)
              _ = z₁ := rfl
            · calc
              ‖z₁‖ = ‖(‖x‖/‖z‖) • z‖ := rfl
              _ = ‖‖x‖/‖z‖‖ * ‖z‖ := norm_smul (‖x‖ / ‖z‖) z
              _ = ‖x‖/‖z‖ * ‖z‖ := by simp only [norm_div, norm_norm]
              _ = ‖x‖ := div_mul_cancel₀ ‖x‖ hznz
              _ ≤ 1 := hx.2
          apply segment_subset_convexHull t₁ t₂
          rw [segment]
          simp only [exists_and_left, Set.mem_setOf_eq]
          use ‖y‖/‖x‖
          constructor
          · exact div_nonneg (ContinuousLinearMap.opNorm_nonneg y)
              (ContinuousLinearMap.opNorm_nonneg x)
          · use ‖z‖/‖x‖
            constructor
            · exact div_nonneg (ContinuousLinearMap.opNorm_nonneg z)
                (ContinuousLinearMap.opNorm_nonneg x)
            · constructor
              · calc
                ‖y‖ / ‖x‖ + ‖z‖ / ‖x‖ = (‖y‖ + ‖z‖) / ‖x‖ := div_add_div_same ‖y‖ ‖z‖ ‖x‖
                _ = 1 := (div_eq_one_iff_eq hxnz).mpr e4
              · calc
                (‖y‖ / ‖x‖) • y₁ + (‖z‖ / ‖x‖) • z₁ =
                  (‖y‖ / ‖x‖) • ((‖x‖/‖y‖) • y) + (‖z‖ / ‖x‖) • ((‖x‖/‖z‖) • z) := rfl
                _ = ((‖y‖ / ‖x‖) • (‖x‖/‖y‖)) • y + ((‖z‖ / ‖x‖) • (‖x‖/‖z‖)) • z := by
                  rw [← smul_assoc, ← smul_assoc]
                _ = ((‖y‖ / ‖x‖) * (‖x‖/‖y‖)) • y + ((‖z‖ / ‖x‖) * (‖x‖/‖z‖)) • z := by
                  simp only [smul_eq_mul]
                _ = ((‖y‖ / ‖x‖) * (‖y‖ / ‖x‖)⁻¹) • y + ((‖z‖ / ‖x‖) * (‖z‖ / ‖x‖)⁻¹) • z := by
                  rw [inv_div, inv_div]
                _ = y + ((‖z‖ / ‖x‖) * (‖z‖ / ‖x‖)⁻¹) • z := by
                  rw [CommGroupWithZero.mul_inv_cancel, one_smul, inv_div]
                  exact div_ne_zero hynz hxnz
                _ = y + z := by
                  rw [CommGroupWithZero.mul_inv_cancel, one_smul]
                  exact div_ne_zero hznz hxnz
                _ = x := by rw [e3])
  ( by
    simp only [Submodule.add_eq_sup, Set.le_eq_subset, Set.subset_inter_iff]
    exact ⟨convexHull_min (Set.union_subset_iff.mpr ⟨subset_trans
          (Set.inter_subset_left (s := SetLike.coe (polarSubmodule 𝕜 m₁)))
          (SetLike.coe_subset_coe.mpr le_sup_left),
        subset_trans
          (Set.inter_subset_left (s := SetLike.coe (polarSubmodule 𝕜 m₂)))
          (SetLike.coe_subset_coe.mpr le_sup_right)⟩)
        (fun _ hx _ hy _ _ _ _ _ => add_mem (smul_of_tower_mem _ _ hx) (smul_of_tower_mem _ _ hy)),
      convexHull_min (Set.union_subset_iff.mpr
        ⟨Set.inter_subset_right, Set.inter_subset_right⟩) (convex_closedBall _ _)⟩)

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
