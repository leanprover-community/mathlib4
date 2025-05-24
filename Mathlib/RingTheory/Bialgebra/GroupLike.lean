/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Flat.Domain

/-!
# Group-like elements in a bialgebra

This file defines group-like elements in a bialgebra, ie units `a` such that `Δ a = a ⊗ₜ a`.

The motivating example is the group ring `R[G]`. For a domain `R`, group-like elements of `R[G]` are
exactly the image of `G` inside `R[G]`. We note two things: these group-like elements form a group
and are linearly independent.

In an arbitrary bialgebra, group-like elements always form a group, and are linearly independent if
the base ring is a domain.

## Main declarations

* `Bialgebra.IsGroupLikeElem`: Predicate for an element in a bialgebra to be group-like.
* `Bialgebra.GroupLike`: Subgroup of group-like elements.
* `Bialgebra.linearIndepOn_isGroupLikeElem`: Group-like elements are linearly independent.
-/

open Coalgebra Function TensorProduct

variable {F R A B : Type*}

namespace Bialgebra
section Semiring
variable [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A]
  [Bialgebra R B] {a b : A}

variable (R) in
/-- A group-like element in a coalgebra is a unit `a` such that `Δ a = a ⊗ₜ a`. -/
structure IsGroupLikeElem (a : A) where
  isUnit : IsUnit a
  comul_eq_tmul_self : comul (R := R) a = a ⊗ₜ a

lemma IsGroupLikeElem.ne_zero [Nontrivial A] (ha : IsGroupLikeElem R a) : a ≠ 0 := ha.isUnit.ne_zero

/-- The image of a group-like element under the counit is `1`. -/
lemma IsGroupLikeElem.counit_eq_one (ha : IsGroupLikeElem R a) : counit a = (1 : R) :=
  algebraMap_injective A <| by
    simpa [ha.comul_eq_tmul_self, Ring.inverse_mul_cancel _ ha.isUnit, Algebra.smul_def] using
      congr(Algebra.TensorProduct.lid R A (((1 : R) ⊗ₜ[R] (Ring.inverse a)) *
        $(rTensor_counit_comul (R := R) a)))

/-- A bialgebra hom sends group-like elements to group-like elements. -/
lemma IsGroupLikeElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  isUnit := ha.isUnit.map f
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

/-- A bialgebra equivalence preserves group-like elements. -/
@[simp] lemma isGroupLikeElem_map [EquivLike F A B] [BialgEquivClass F R A B] (f : F) :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a where
  mp ha := by
    rw [← (BialgEquivClass.toBialgEquiv f).symm_apply_apply a]
    exact ha.map (BialgEquivClass.toBialgEquiv f).symm
  mpr := .map f

/-- In a bialgebra, `1` is a group-like element. -/
lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  isUnit := isUnit_one
  comul_eq_tmul_self := by rw [comul_one, Algebra.TensorProduct.one_def]

/-- Group-like elements in a bialgebra are stable under multiplication. -/
lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  isUnit := ha.isUnit.mul hb.isUnit
  comul_eq_tmul_self := by rw [comul_mul, ha.comul_eq_tmul_self, hb.comul_eq_tmul_self,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Group-like elements in a bialgebra are stable under inverses. -/
lemma IsGroupLikeElem.unitsInv {u : Aˣ} (ha : IsGroupLikeElem R u.val) :
    IsGroupLikeElem R u⁻¹.val where
  isUnit := u⁻¹.isUnit
  comul_eq_tmul_self := calc
          (u⁻¹.map (comulAlgHom R A)).val
      _ = (u.map (comulAlgHom R A))⁻¹.val := by simp
      _ = u⁻¹.val ⊗ₜ[R] u⁻¹.val := Units.inv_eq_of_mul_eq_one_left <| by
        simp [ha.comul_eq_tmul_self, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.one_def]

/-- Group-like elements in a bialgebra are stable under inverses. -/
lemma IsGroupLikeElem.ringInverse (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R (Ring.inverse a) := by
  simpa [← Ring.inverse_of_isUnit] using ha.unitsInv (u := ha.isUnit.unit)

variable (R A) in
/-- The group of group-like elements in a bialgebra. -/
abbrev GroupLike : Type _ := ({
  carrier := {u | IsGroupLikeElem R (u : A)}
  mul_mem' := .mul
  one_mem' := .one
  inv_mem' := .unitsInv
} : Subgroup Aˣ)

end Semiring

section CommRing
variable [CommRing R] [IsDomain R] [Ring A] [Bialgebra R A] [NoZeroSMulDivisors R A] [Nontrivial A]

open Submodule in
/-- Group-like elements over a domain are linearly independent. -/
lemma linearIndepOn_isGroupLikeElem : LinearIndepOn R id {a : A | IsGroupLikeElem R a} := by
  classical
  -- We show that any finset `s` of group-like elements is linearly independent.
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  -- For this, we do induction on `s`.
  induction s using Finset.cons_induction with
  -- The case `s = ∅` is trivial.
  | empty => simp
  -- Let's deal with the `s ∪ {a}` case.
  | cons a s has ih =>
  simp only [Finset.cons_eq_insert, Finset.coe_insert, Set.subset_def, Set.mem_insert_iff,
    Finset.mem_coe, Set.mem_setOf_eq, forall_eq_or_imp] at hs
  obtain ⟨ha, hs⟩ := hs
  specialize ih hs
  -- Assume that there is some `c : A → R` such that `∑ x ∈ s, c x • x = -c a • a`.
  -- We want to prove `c a = 0` and `∀ x ∈ s, c x = 0`.
  simp only [linearIndepOn_finset_iff, id, Finset.sum_cons, Finset.mem_cons, forall_eq_or_imp,
    add_eq_zero_iff_eq_neg', ← neg_smul]
  rintro c hc
  -- `x ⊗ y` over `x, y ∈ s` are linearly independent since `s` is linearly independent and
  -- `R` is a domain.
  replace ih := ih.tmul_of_isDomain ih
  simp_rw [← Finset.coe_product, linearIndepOn_finset_iffₛ, id] at ih
  -- Tensoring the equality `∑ x ∈ s, c x • x = -c a • a` with itself, we get by linear independence
  -- that `c x ^ 2 = -c a * c x` and `c x * c y = 0` for `x ≠ y`.
  have key := calc
        ∑ x ∈ s, ∑ y ∈ s, (if x = y then -c a * c x else 0) • x ⊗ₜ[R] y
    _ = -c a • ∑ x ∈ s, c x • x ⊗ₜ[R] x := by simp [Finset.smul_sum, mul_smul]
    _ = -c a • comul (-c a • a) := by rw [← hc]; simp +contextual [(hs _ _).comul_eq_tmul_self]
    _ = (-c a • a) ⊗ₜ (-c a • a) := by simp [ha.comul_eq_tmul_self, smul_tmul, tmul_smul, -neg_smul]
    _ = ∑ x ∈ s, ∑ y ∈ s, (c x * c y) • x ⊗ₜ[R] y := by
      simp_rw [← hc, sum_tmul, smul_tmul, Finset.smul_sum, tmul_sum, tmul_smul, mul_smul]
  simp_rw [← Finset.sum_product'] at key
  apply ih at key
  -- Therefore, `c x = 0` for all `x ∈ s`.
  replace key x (hx : x ∈ s) : c x = 0 := by
    -- Indeed, otherwise we would have `a = x`, contradicting `a ∉ s`.
    contrapose! has
    convert hx
    -- This is since `c y = 0` for all `y ∈ s`, `y ≠ x`, and `c x = c a`, and therefore
    -- `c x • x = ∑ y ∈ s, c y • y = c a • a = c x • a`
    refine smul_right_injective _ has ?_
    calc
          c x • a
      _ = -c a • a := by congr; simpa [hx, has, eq_comm, -neg_mul] using key (x, x)
      _ = ∑ y ∈ s, c y • y := by rw [hc]
      _ = c x • x := by
        rw [Finset.sum_eq_single x _ (by simp [hx])]
        rintro y hys hyx
        have : c y = 0 := by simpa [*] using key (y, x)
        simp [this]
  -- We are now done, since `c a • a = ∑ x ∈ s, c x • x = 0`
  simp_all [ha.ne_zero]

end CommRing
end Bialgebra
