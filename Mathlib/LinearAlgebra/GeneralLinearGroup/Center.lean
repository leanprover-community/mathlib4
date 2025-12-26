/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Center

/-!
# Center of the group of linear automorphisms

Let `R` be a ring and let `V` be a free `R`-module.
We describe the center of the group of linear automorphisms of `V`.

The group of linear automorphisms can be summoned either as `V ≃ₗ[R] V`,
or as `LinearMap.GeneralLinearGroup R V`, which is a shortcut for `(V →ₗ[R] V)ˣ`.
We provide both descriptions.

There are three possibilities:

* If `V` is trivial, then `V ≃ₗ[R] V` is trivial, and so is its center.

* If `V` has rank one, then any basis with a `Unique` type of index furnishes
a ring equivalence from `V →ₗ[R] V` with `Rᵐᵒᵖ`,
given by right-multiplication on coordinates in the given basis.
(This equivalence depends on the choice of a basis.)
Then `V ≃ₗ[R] V` is mul-equivalent with `(Rᵐᵒᵖ)ˣ`, hence its center is isomorphic
with `Subgroup.center (Rᵐᵒᵖ)ˣ`, or, by commutativity, with `Subgroup.center Rˣ`.

* Otherwise, the center of `V ≃ₗ[R] V` consists of homotheties with central ratio,
furnishing a group isomorphism from `Subgroup.center (V ≃ₗ[R] V)` with
`(Subgroup.center R)ˣ`.

When `R` is commutative and `V` is nontrivial, the last two cases give the same
answer and the center of `V ≃ₗ[R] V` is isomorphic with `Rˣ`.

-/

@[expose] public section

open Module LinearMap LinearEquiv Set

variable {R V : Type*}

theorem Set.map_mem_center_of_surjective
    {G H : Type*} [Monoid G] [Monoid H] {e : G →* H} {g : G}
    (he : Function.Surjective e) (hg : g ∈ Set.center G) :
    e g ∈ Set.center H := by
  rw [Semigroup.mem_center_iff] at hg ⊢
  intro h
  obtain ⟨k, rfl⟩ := he h
  simp only [← map_mul, hg]

theorem Set.map_mem_center_iff
    {G H : Type*} [Monoid G] [Monoid H] (e : G ≃* H) (g : G) :
    g ∈ Set.center G ↔ e g ∈ Set.center H := by
  constructor
  · intro hg
    rw [← MulEquiv.coe_toMonoidHom]
    exact Set.map_mem_center_of_surjective e.surjective hg
  · intro hg
    rw [show g = e.symm.toMonoidHom (e g) from by simp]
    exact Set.map_mem_center_of_surjective e.symm.surjective hg

-- Mathlib.Algebra.Central.End
theorem Module.End.mem_subsemiringCenter_iff
    [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] {f : End R V} :
    f ∈ Subsemiring.center (End R V) ↔
      ∃ α ∈ Subsemiring.center R, ∀ x : V, f x = α • x :=
  sorry

theorem Module.Basis.index_nontrivial_iff
    {R : Type*} [Semiring R] [StrongRankCondition R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Nontrivial M]
    {ι : Type*} (b : Basis ι R M) :
    Nontrivial ι ↔ finrank R M ≠ 1 := by
  simp [← not_iff_not, ne_eq, not_nontrivial_iff_subsingleton,
    Module.finrank_eq_nat_card_basis b, Nat.card_eq_one_iff_unique,
    b.index_nonempty]

namespace LinearEquiv

section

variable [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] [Nontrivial V]

theorem isUnit_ratio {f : V ≃ₗ[R] V} {a : R} (hfa : ∀ x, f x = a • x) :
    IsUnit a := by
  rw [isUnit_iff_exists]
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  have _ : Nonempty ι := inferInstance
  let i : ι := Classical.ofNonempty
  use b.coord i (f⁻¹ (b i))
  have hfa (r : R) : f (r • b i) = (a * r) • b i := by
    simpa [mul_smul] using hfa (r • b i)
  have isLeftRegular : IsLeftRegular a := by
    intro r s hrs
    replace hrs : (a * r) • b i = (a * s) • b i := by simp [hrs]
    simp only [← hfa, f.injective.eq_iff] at hrs
    simpa using congr(b.coord i $hrs)
  suffices _ by
    refine ⟨this, ?_⟩
    apply isLeftRegular
    simp only [← mul_assoc, this, one_mul, mul_one]
  have :  a • f⁻¹ (b i) = b i := by
    rw [← LinearEquiv.map_smul, coe_inv, LinearEquiv.symm_apply_eq]
    simpa using (hfa 1).symm
  simpa using congr(b.coord i $((this)))

end

variable [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*}

/-- A linear automorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio. -/
theorem commute_transvections_iff_of_basis [Nontrivial ι]
    (b : Basis ι R V) {f : V ≃ₗ[R] V}
    (hcomm : ∀ i j (r : R) (hij : i ≠ j),
      Commute f (LinearEquiv.transvection (f := b.coord i) (v := r • b j) (by
      simp [Finsupp.single_eq_of_ne hij]))) :
    ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x, f x = a • x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, by simp, fun x ↦ Subsingleton.allEq _ _⟩
  have _ : Free R V := Free.of_basis b
  obtain ⟨a, hfa⟩ :=
    LinearMap.commute_transvections_iff_of_basis b (f := f.toLinearMap)
      (fun i j r hij ↦ by
        simpa [← toLinearMap_inj, commute_iff_eq] using hcomm i j r hij)
  refine ⟨a, hfa.1, ?_, fun x ↦ by simpa using hfa.2 x⟩
  apply isUnit_ratio (f := f) (fun x ↦ by simpa using hfa.2 x)

/-- A linear automorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central invertible ratio. -/
theorem commute_transvections_iff [StrongRankCondition R] [Free R V]
    (hV : finrank R V ≠ 1) {f : V ≃ₗ[R] V}
    (hcomm : ∀ (l : Dual R V) (v : V) (hlv : l v = 0), Commute f (LinearEquiv.transvection hlv)) :
    ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x, f x = a • x := by
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial V
  · refine ⟨1, by simp, by simp, fun x ↦ Subsingleton.allEq _ _⟩
  rw [← b.index_nontrivial_iff] at hV
  exact commute_transvections_iff_of_basis b (fun _ _ _ _ ↦ hcomm _ ..)

/-- The center of linear automorphisms of a free module of rank ≠ 1
consists of homotheties with central ratio.

This version requires a basis with a nontrivial type of indices.
Under `StrongRankCondition R`, use `LinearEquiv.mem_center_iff`. -/
theorem mem_center_iff_of_basis [Nontrivial ι]
    (b : Basis ι R V) {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x : V, f x = a • x  := by
  constructor
  · intro hf
    apply commute_transvections_iff_of_basis b
    intro i j r hij
    rw [Subgroup.mem_center_iff] at hf
    rw [commute_iff_eq, hf]
  · rintro ⟨a, _, hfa⟩
    rw [Subgroup.mem_center_iff]
    intro g
    ext x
    simp [hfa]

/-- The center of linear automorphisms of a free module of rank ≠ 1
consists of homotheties with central ratio.

This version requires `StrongRankCondition R`.
Otherwise, use `LinearEquiv.mem_center_iff_of_basis`. -/
theorem mem_center_iff [StrongRankCondition R] [Free R V]
    (hV : finrank R V ≠ 1) {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x : V, f x = a • x  := by
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial V
  · constructor
    · intro hf
      refine ⟨1, by simp, by simp, fun x ↦ Subsingleton.allEq _ _⟩
    · rintro ⟨a, hcomm, hunt, hf⟩
      simp only [Subgroup.mem_center_iff]
      intro; ext; simp [hf]
  rw [← b.index_nontrivial_iff] at hV
  exact mem_center_iff_of_basis b

section Unique

open Units LinearMap.GeneralLinearGroup

variable [Unique ι]

/-- Given a basis with a unique index, the ring equivalence
from `Rᵐᵒᵖ` to `End R V` given by right multiplication in the basis. -/
noncomputable def _root_.Module.Basis.mulOppositeEquivEnd
    (b : Basis ι R V) : Rᵐᵒᵖ ≃+* End R V where
  toFun a := {
    toFun x := b.coord default x • MulOpposite.unop a • b default
    map_add' x y := by simp [add_smul]
    map_smul' r x := by simp [mul_smul] }
  invFun f := MulOpposite.op (b.coord default (f (b default)))
  left_inv a := by simp
  right_inv f := b.ext <| fun i ↦ by
    rw [Subsingleton.allEq i default]
    conv_rhs => rw [← b.linearCombination_repr (f (b default)), Finsupp.linearCombination_apply]
    simp only [Basis.coord_apply, MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk,
      Basis.repr_self, Finsupp.single_eq_same, one_smul]
    rw [Finsupp.sum_eq_single default]
    · intro j
      simp [Subsingleton.allEq j default]
    · simp
  map_add' a b := by ext x; simp [add_smul]
  map_mul' a b := by ext x; simp [mul_smul]

theorem _root_.Module.Basis.mulOppositeEquivEnd_apply_apply
    (b : Basis ι R V) (a : Rᵐᵒᵖ) (x : V) :
    b.mulOppositeEquivEnd a x = b.coord default x • a.unop • b default :=
  rfl

theorem _root_.Module.Basis.mulOppositeEquivEnd_symm_apply
    (b : Basis ι R V) (f : End R V) :
    b.mulOppositeEquivEnd.symm f = MulOpposite.op (b.coord default (f (b default))) :=
  rfl

/-- Multiplicative anti-equivalence of units with the group
of linearr automorphisms of a rank one module -/
noncomputable def _root_.Module.Basis.mulOppositeUnitsEquiv (b : Basis ι R V) :
    (Rˣ)ᵐᵒᵖ ≃* (V ≃ₗ[R] V) :=
  opEquiv.symm.trans ((mapEquiv b.mulOppositeEquivEnd.toMulEquiv).trans (generalLinearEquiv R V))

/-- Multiplicative anti-equivalence of units with the general linear group of a rank one module -/
noncomputable def _root_.Module.Basis.mulOppositeUnitsEquiv' (b : Basis ι R V) :
    Rᵐᵒᵖˣ ≃* GeneralLinearGroup R V :=
  mapEquiv b.mulOppositeEquivEnd.toMulEquiv

theorem mem_center_iff_of_unique_basis
    (b : Basis ι R V) {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subgroup.center Rˣ, ∀ x : V, f x = a.val • x := by
  rw [← SetLike.mem_coe, Subgroup.coe_center]
  rw [Set.map_mem_center_iff (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm f]
  rw [Set.map_mem_center_iff (mapEquiv b.mulOppositeEquivEnd.toMulEquiv).symm]
  -- rw [← Subgroup.coe_center, SetLike.mem_coe, Subgroup.mem_center_iff]
  constructor
  · intro hf
    let a := (mapEquiv b.mulOppositeEquivEnd.toMulEquiv).symm
      ((generalLinearEquiv R V).symm f)
    use a.opEquiv.unop
    have ha (x : V) : f x = (b.coord default x) • a.val.unop • b default := sorry
    suffices _ by
      refine ⟨this, fun x ↦ ?_⟩
      rw [ha]
      have : x = (b.coord default x) • b default := sorry
      conv_rhs => rw [this]
      simp only [Basis.coord_apply, smul_smul, coe_unop_opEquiv]
      apply congr_arg₂ _ _ rfl
      rw [← Subgroup.coe_center, SetLike.mem_coe, Subgroup.mem_center_iff] at hf
      sorry

    rw [Subgroup.mem_center_iff]
    intro u
    sorry


  rw [← Subgroup.coe_center,  SetLike.mem_coe]
  sorry

end Unique

/-- The center of linear automorphisms of a free module of rank 1
consists of homotheties with ratio which is central within units.

This version requires `StrongRankCondition R`.
Otherwise, use `LinearEquiv.mem_center_of_unique_basis`. -/
theorem mem_center_iff_of_finrank_one [StrongRankCondition R] [Free R V]
    (hV : finrank R V = 1) {f : V ≃ₗ[R] V} :
    f ∈ Subgroup.center (V ≃ₗ[R] V) ↔
      ∃ a ∈ Subgroup.center Rˣ, ∀ x : V, f x = a.val • x := by
  let b := Module.basisUnique Unit hV
  rw [← SetLike.mem_coe, Subgroup.coe_center]
  rw [Set.map_mem_center_iff (LinearMap.GeneralLinearGroup.generalLinearEquiv R V).symm]
  rw [← Subgroup.coe_center,  SetLike.mem_coe]
  sorry
end LinearEquiv

namespace LinearMap.GeneralLinearGroup

theorem isUnit_ratio
    [Semiring R] [AddCommMonoid V] [Module R V] [Free R V] [Nontrivial V]
    {f : GeneralLinearGroup R V} {a : R} (hfa : ∀ x, f.val x = a • x) :
    IsUnit a := by
  apply LinearEquiv.isUnit_ratio (f := f.toLinearEquiv)
  aesop

variable [Ring R] [AddCommGroup V] [Module R V]

/-- The center of linear endomorphisms of a free module
consists of homotheties with central ratio. -/
theorem mem_center_iff [StrongRankCondition R] [Free R V]
    {f : GeneralLinearGroup R V} (hV : finrank R V ≠ 1) :
    f ∈ Subgroup.center (GeneralLinearGroup R V) ↔
      ∃ a ∈ Subring.center R, IsUnit a ∧ ∀ x : V, f.val x = a • x  := by
  rw [← SetLike.mem_coe, Subgroup.coe_center]
  rw [Set.map_mem_center_iff (generalLinearEquiv R V) f]
  rw [← Subgroup.coe_center,  SetLike.mem_coe]
  rw [LinearEquiv.mem_center_iff hV]
  simp

end LinearMap.GeneralLinearGroup
