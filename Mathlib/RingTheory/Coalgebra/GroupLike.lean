/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.RingTheory.Flat.Domain

/-!
# Group-like elements in a coalgebra

This file defines group-like elements in a coalgebra, i.e. elements `a` such that `ε a = 1` and
`Δ a = a ⊗ₜ a`.

## Main declarations

* `IsGroupLikeElem`: Predicate for an element in a coalgebra to be group-like.
* `linearIndepOn_isGroupLikeElem`: Group-like elements over a domain are linearly independent.
-/

open Coalgebra Function TensorProduct

variable {F R A B : Type*}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Coalgebra R A]
  [Module R B] [Coalgebra R B] {a b : A}

variable (R) in
/-- A group-like element in a coalgebra is an element `a` such that $\varepsilon(a) = 1$ and
$\Delta(a) = a ⊗ a$. -/
@[mk_iff]
structure IsGroupLikeElem (a : A) where
  counit_eq_one : counit (R := R) a = 1
  comul_eq_tmul_self : comul a = a ⊗ₜ[R] a

attribute [simp] IsGroupLikeElem.counit_eq_one IsGroupLikeElem.comul_eq_tmul_self

@[simp] lemma isGroupLikeElem_self {r : R} : IsGroupLikeElem R r ↔ r = 1 := by
  simp +contextual [isGroupLikeElem_iff]

lemma IsGroupLikeElem.ne_zero [Nontrivial R] (ha : IsGroupLikeElem R a) : a ≠ 0 := by
  rintro rfl; simpa using ha.counit_eq_one

/-- A coalgebra homomorphism sends group-like elements to group-like elements. -/
lemma IsGroupLikeElem.map [FunLike F A B] [CoalgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  counit_eq_one := by rw [CoalgHomClass.counit_comp_apply, ha.counit_eq_one]
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

/-- A coalgebra isomorphism preserves group-like elements. -/
@[simp] lemma isGroupLikeElem_map [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a where
  mp ha := by
    rw [← (CoalgEquivClass.toCoalgEquiv f).symm_apply_apply a]
    exact ha.map (CoalgEquivClass.toCoalgEquiv f).symm
  mpr := .map f

variable (R A) in
/-- The type of group-like elements in a coalgebra. -/
@[ext]
structure GroupLike where
  /-- The underlying element of a group-like element. -/
  val : A
  isGroupLikeElem_val : IsGroupLikeElem R val

namespace GroupLike

attribute [coe] val

instance instCoeOut : CoeOut (GroupLike R A) A where coe := val

attribute [simp] isGroupLikeElem_val

lemma val_injective : Injective (val : GroupLike R A → A) := by rintro ⟨a, ha⟩; congr!

@[simp, norm_cast] lemma val_inj {a b : GroupLike R A} : a.val = b.val ↔ a = b :=
  val_injective.eq_iff

/-- Identity equivalence between `GroupLike R A` and `{a : A | IsGroupLikeElem R a}`. -/
def valEquiv : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A → Prop) where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GroupLike
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A] [Coalgebra R A]
  [NoZeroSMulDivisors R A]

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

/-- Group-like elements over a domain are linearly independent. -/
lemma linearIndep_groupLikeVal : LinearIndependent R (GroupLike.val (R := R) (A := A)) := by
  simpa using (linearIndependent_equiv GroupLike.valEquiv).2 linearIndepOn_isGroupLikeElem

end CommRing
