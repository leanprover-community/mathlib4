/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.Ray
import Mathlib.LinearAlgebra.Determinant

#align_import linear_algebra.orientation from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `Orientation` is a type synonym for `Module.Ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `Module.Oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`Orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `Fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/


noncomputable section

open BigOperators

section OrderedCommSemiring

variable (R : Type*) [StrictOrderedCommSemiring R]

variable (M : Type*) [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (ι : Type*)

/-- An orientation of a module, intended to be used when `ι` is a `Fintype` with the same
cardinality as a basis. -/
abbrev Orientation := Module.Ray R (AlternatingMap R M R ι)
#align orientation Orientation

/-- A type class fixing an orientation of a module. -/
class Module.Oriented where
  /-- Fix a positive orientation. -/
  positiveOrientation : Orientation R M ι
#align module.oriented Module.Oriented

export Module.Oriented (positiveOrientation)

variable {R M}

/-- An equivalence between modules implies an equivalence between orientations. -/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e
#align orientation.map Orientation.map

@[simp]
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : AlternatingMap R M R ι) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.compLinearEquiv_eq_zero_iff e.symm).mp hv) :=
  rfl
#align orientation.map_apply Orientation.map_apply

@[simp]
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map, AlternatingMap.domLCongr_refl, Module.Ray.map_refl]
  -- 🎉 no goals
#align orientation.map_refl Orientation.map_refl

@[simp]
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm := rfl
#align orientation.map_symm Orientation.map_symm

/-- A module is canonically oriented with respect to an empty index type. -/
instance (priority := 100) IsEmpty.oriented [Nontrivial R] [IsEmpty ι] : Module.Oriented R M ι
    where positiveOrientation :=
    rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1) <|
      AlternatingMap.constLinearEquivOfIsEmpty.injective.ne (by exact one_ne_zero)
                                                                -- 🎉 no goals
#align is_empty.oriented IsEmpty.oriented

@[simp]
theorem Orientation.map_positiveOrientation_of_isEmpty [Nontrivial R] [IsEmpty ι] (f : M ≃ₗ[R] N) :
    Orientation.map ι f positiveOrientation = positiveOrientation := rfl
#align orientation.map_positive_orientation_of_is_empty Orientation.map_positiveOrientation_of_isEmpty

@[simp]
theorem Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x := by
  induction' x using Module.Ray.ind with g hg
  -- ⊢ ↑(map ι f) (rayOfNeZero R g hg) = rayOfNeZero R g hg
  rw [Orientation.map_apply]
  -- ⊢ rayOfNeZero R (AlternatingMap.compLinearMap g ↑(LinearEquiv.symm f)) (_ : ¬A …
  congr
  -- ⊢ AlternatingMap.compLinearMap g ↑(LinearEquiv.symm f) = g
  ext i
  -- ⊢ ↑(AlternatingMap.compLinearMap g ↑(LinearEquiv.symm f)) i = ↑g i
  rw [AlternatingMap.compLinearMap_apply]
  -- ⊢ (↑g fun i_1 => ↑↑(LinearEquiv.symm f) (i i_1)) = ↑g i
  congr
  -- ⊢ (fun i_1 => ↑↑(LinearEquiv.symm f) (i i_1)) = i
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]
  -- 🎉 no goals
#align orientation.map_of_is_empty Orientation.map_of_isEmpty

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type*} [StrictOrderedCommRing R]

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

@[simp]
protected theorem Orientation.map_neg {ι : Type*} (f : M ≃ₗ[R] N) (x : Orientation R M ι) :
    Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x
#align orientation.map_neg Orientation.map_neg

namespace Basis

variable {ι : Type*}

/-- The value of `Orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x := by
  cases nonempty_fintype ι
  -- ⊢ ↑(Orientation.map ι f) x = (↑LinearEquiv.det f)⁻¹ • x
  letI := Classical.decEq ι
  -- ⊢ ↑(Orientation.map ι f) x = (↑LinearEquiv.det f)⁻¹ • x
  induction' x using Module.Ray.ind with g hg
  -- ⊢ ↑(Orientation.map ι f) (rayOfNeZero R g hg) = (↑LinearEquiv.det f)⁻¹ • rayOf …
  rw [Orientation.map_apply, smul_rayOfNeZero, ray_eq_iff, Units.smul_def,
    (g.compLinearMap f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply,
    show (fun i ↦ (LinearEquiv.symm f).toLinearMap (e i)) = (LinearEquiv.symm f).toLinearMap ∘ e
    by rfl, Basis.det_comp, Basis.det_self, mul_one, smul_eq_mul, mul_comm, mul_smul,
    LinearEquiv.coe_inv_det]
#align basis.map_orientation_eq_det_inv_smul Basis.map_orientation_eq_det_inv_smul

variable [Fintype ι] [DecidableEq ι]

/-- The orientation given by a basis. -/
protected def orientation [Nontrivial R] (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
#align basis.orientation Basis.orientation

theorem orientation_map [Nontrivial R] (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).orientation = Orientation.map ι f e.orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']
  -- 🎉 no goals
#align basis.orientation_map Basis.orientation_map

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
theorem orientation_unitsSMul [Nontrivial R] (e : Basis ι R M) (w : ι → Units R) :
    (e.unitsSMul w).orientation = (∏ i, w i)⁻¹ • e.orientation := by
  rw [Basis.orientation, Basis.orientation, smul_rayOfNeZero, ray_eq_iff,
    e.det.eq_smul_basis_det (e.unitsSMul w), det_unitsSMul_self, Units.smul_def, smul_smul]
  norm_cast
  -- ⊢ SameRay R (det (unitsSMul e w)) (↑((∏ i : ι, w i)⁻¹ * ∏ i : ι, w i) • det (u …
  simp
  -- ⊢ SameRay R (det (unitsSMul e w)) (det (unitsSMul e w))
  exact SameRay.rfl
  -- 🎉 no goals
#align basis.orientation_units_smul Basis.orientation_unitsSMul

@[simp]
theorem orientation_isEmpty [Nontrivial R] [IsEmpty ι] (b : Basis ι R M) :
    b.orientation = positiveOrientation := by
  rw [Basis.orientation]
  -- ⊢ rayOfNeZero R (det b) (_ : det b ≠ 0) = positiveOrientation
  congr
  -- ⊢ det b = ↑AlternatingMap.constLinearEquivOfIsEmpty 1
  exact b.det_isEmpty
  -- 🎉 no goals
#align basis.orientation_is_empty Basis.orientation_isEmpty

end Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [LinearOrderedCommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {ι : Type*}

namespace Orientation

/-- A module `M` over a linearly ordered commutative ring has precisely two "orientations" with
respect to an empty index type. (Note that these are only orientations of `M` of in the conventional
mathematical sense if `M` is zero-dimensional.) -/
theorem eq_or_eq_neg_of_isEmpty [Nontrivial R] [IsEmpty ι] (o : Orientation R M ι) :
    o = positiveOrientation ∨ o = -positiveOrientation := by
  induction' o using Module.Ray.ind with x hx
  -- ⊢ rayOfNeZero R x hx = positiveOrientation ∨ rayOfNeZero R x hx = -positiveOri …
  dsimp [positiveOrientation]
  -- ⊢ rayOfNeZero R x hx = rayOfNeZero R (AlternatingMap.constOfIsEmpty R M ι 1) ( …
  simp only [ray_eq_iff, sameRay_neg_swap]
  -- ⊢ SameRay R x (AlternatingMap.constOfIsEmpty R M ι 1) ∨ SameRay R x (-Alternat …
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  -- ⊢ ¬LinearIndependent R ![x, AlternatingMap.constOfIsEmpty R M ι 1]
  intro h
  -- ⊢ False
  set f : AlternatingMap R M R ι ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  -- ⊢ False
  have H : LinearIndependent R ![f x, 1] := by
    convert h.map' f.toLinearMap f.ker
    ext i
    fin_cases i <;> simp
  rw [linearIndependent_iff'] at H
  -- ⊢ False
  simpa using H Finset.univ ![1, -f x] (by simp [Fin.sum_univ_succ]) 0 (by simp)
  -- 🎉 no goals
#align orientation.eq_or_eq_neg_of_is_empty Orientation.eq_or_eq_neg_of_isEmpty

end Orientation

namespace Basis

variable [Fintype ι] [DecidableEq ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
                                                    -- 🎉 no goals
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero

#align basis.orientation_eq_iff_det_pos Basis.orientation_eq_iff_det_pos

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.orientation ∨ x = -e.orientation := by
  induction' x using Module.Ray.ind with x hx
  -- ⊢ rayOfNeZero R x hx = Basis.orientation e ∨ rayOfNeZero R x hx = -Basis.orien …
  rw [← x.map_basis_ne_zero_iff e] at hx
  -- ⊢ rayOfNeZero R x hx✝ = Basis.orientation e ∨ rayOfNeZero R x hx✝ = -Basis.ori …
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_iff_ne, ne_comm]
#align basis.orientation_eq_or_eq_neg Basis.orientation_eq_or_eq_neg

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x ≠ e.orientation ↔ x = -e.orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩
#align basis.orientation_ne_iff_eq_neg Basis.orientation_ne_iff_eq_neg

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
theorem orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = e.orientation ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]
#align basis.orientation_comp_linear_equiv_eq_iff_det_pos Basis.orientation_comp_linearEquiv_eq_iff_det_pos

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = -e.orientation ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
    LinearEquiv.coe_det]
#align basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
theorem orientation_neg_single [Nontrivial R] (e : Basis ι R M) (i : ι) :
    (e.unitsSMul (Function.update 1 i (-1))).orientation = -e.orientation := by
  rw [orientation_unitsSMul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  -- ⊢ (-1 * ∏ x in Finset.univ \ {i}, OfNat.ofNat 1 x)⁻¹ • Basis.orientation e = - …
  simp
  -- 🎉 no goals
#align basis.orientation_neg_single Basis.orientation_neg_single

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))
#align basis.adjust_to_orientation Basis.adjustToOrientation

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
theorem orientation_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).orientation = x := by
  rw [adjustToOrientation]
  -- ⊢ Basis.orientation (if Basis.orientation e = x then e else unitsSMul e (Funct …
  split_ifs with h
  -- ⊢ Basis.orientation e = x
  · exact h
    -- 🎉 no goals
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    -- ⊢ Basis.orientation e ≠ x
    exact h
    -- 🎉 no goals
#align basis.orientation_adjust_to_orientation Basis.orientation_adjustToOrientation

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem adjustToOrientation_apply_eq_or_eq_neg [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  rw [adjustToOrientation]
  -- ⊢ ↑(if Basis.orientation e = x then e else unitsSMul e (Function.update 1 (Cla …
  split_ifs with h
  -- ⊢ ↑e i = ↑e i ∨ ↑e i = -↑e i
  · simp
    -- 🎉 no goals
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]
    -- ⊢ ↑(unitsSMul e (Function.update 1 (Classical.arbitrary ι) (-1))) i = ↑e i ∨ ↑ …
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align basis.adjust_to_orientation_apply_eq_or_eq_neg Basis.adjustToOrientation_apply_eq_or_eq_neg

theorem det_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det := by
  dsimp [Basis.adjustToOrientation]
  -- ⊢ det (if Basis.orientation e = x then e else unitsSMul e (Function.update 1 ( …
  split_ifs
  -- ⊢ det e = det e ∨ det e = -det e
  · left
    -- ⊢ det e = det e
    rfl
    -- 🎉 no goals
  · right
    -- ⊢ det (unitsSMul e (Function.update 1 (Classical.arbitrary ι) (-1))) = -det e
    simp [e.det_unitsSMul, ← Units.coe_prod, Finset.prod_update_of_mem]
    -- ⊢ -1 • det e = -det e
    ext
    -- ⊢ ↑(-1 • det e) x✝ = ↑(-det e) x✝
    simp
    -- 🎉 no goals
#align basis.det_adjust_to_orientation Basis.det_adjustToOrientation

@[simp]
theorem abs_det_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι → M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  cases' e.det_adjustToOrientation x with h h <;> simp [h]
  -- ⊢ |↑(det (adjustToOrientation e x)) v| = |↑(det e) v|
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align basis.abs_det_adjust_to_orientation Basis.abs_det_adjustToOrientation

end Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type*} [LinearOrderedField R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {ι : Type*}

namespace Orientation

variable [Fintype ι] [_i : FiniteDimensional R M]

open FiniteDimensional

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
theorem eq_or_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  -- ⊢ x₁ = x₂ ∨ x₁ = -x₂
  letI := Classical.decEq ι
  -- ⊢ x₁ = x₂ ∨ x₁ = -x₂
  -- Porting note: this needs to be made explicit for the simp below
  have orientation_neg_neg :
    ∀ f : Basis ι R M, - -Basis.orientation f = Basis.orientation f := by simp
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
  -- ⊢ x₁ = x₂ ∨ x₁ = -x₂
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂, orientation_neg_neg]
    -- ⊢ x₁ = x₂ ∨ x₁ = -x₂
    -- ⊢ x₁ = x₂ ∨ x₁ = -x₂
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
#align orientation.eq_or_eq_neg Orientation.eq_or_eq_neg

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
theorem ne_iff_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩
#align orientation.ne_iff_eq_neg Orientation.ne_iff_eq_neg

/-- The value of `Orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
theorem map_eq_det_inv_smul (x : Orientation R M ι) (f : M ≃ₗ[R] M)
  (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x :=
  haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f
#align orientation.map_eq_det_inv_smul Orientation.map_eq_det_inv_smul

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
theorem map_eq_iff_det_pos (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  cases isEmpty_or_nonempty ι
  -- ⊢ ↑(map ι f) x = x ↔ 0 < ↑LinearMap.det ↑f
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert @Fintype.card_of_isEmpty ι _
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
    -- 🎉 no goals
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]
  -- 🎉 no goals
#align orientation.map_eq_iff_det_pos Orientation.map_eq_iff_det_pos

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  cases isEmpty_or_nonempty ι
  -- ⊢ ↑(map ι f) x = -x ↔ ↑LinearMap.det ↑f < 0
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert @Fintype.card_of_isEmpty ι _
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
    -- 🎉 no goals
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := finiteDimensional_of_finrank H
  -- ⊢ ↑(map ι f) x = -x ↔ ↑LinearMap.det ↑f < 0
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]
  -- 🎉 no goals
#align orientation.map_eq_neg_iff_det_neg Orientation.map_eq_neg_iff_det_neg

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def someBasis [Nonempty ι] [DecidableEq ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x
#align orientation.some_basis Orientation.someBasis

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
theorem someBasis_orientation [Nonempty ι] [DecidableEq ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : (x.someBasis h).orientation = x :=
  Basis.orientation_adjustToOrientation _ _
#align orientation.some_basis_orientation Orientation.someBasis_orientation

end Orientation

end LinearOrderedField
