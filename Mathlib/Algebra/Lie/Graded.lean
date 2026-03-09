/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Lie.Basic

/-!
# Graded Lie algebras
This file defines typeclasses `GBracket` and `GLieRing`, for working with Lie algebras that are
graded by a collection of modules `A : ι → Type*`. The additivity of degree with respect to the
bracket product is encoded by a `Prop` so we can avoid the usual difficulties of adding elements of
`A (i + j)` to elements of `A (j + i)`.
## Main definitions
* `GBracket` : A typeclass for a graded bracket
* `GLieRing` : A typeclass for a graded bracket to have a Lie ring structure.
## TODO
* `GLieAlgebra` : Graded Lie algebra structure
* Internal direct sums
* Derivation from scalar multiplication by a linear map applied to degree.
## Tags
graded Lie algebra
-/

@[expose] public section

open DirectSum

variable {ι R L : Type*}

section GradedLieRing

variable (A : ι → Type*)
/-- A graded version of `Bracket`. Grades are combined additively, like
`AddMonoidAlgebra`. -/
class GBracket [Add ι] where
  /-- The homogeneous multiplication map `bracket`. We do not use `A i → A j → A (i + j)` because
    the `leibniz_lie` rule for graded Lie algebras would then require a cast. -/
  bracket {i j k} (h : i + j = k) : A i → A j → A k

/-- A graded version of `LieRing`. -/
class GLieRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GBracket A where
  /-- A graded Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ {i j k} (h : i + j = k) (x y : A i) (z : A j),
    bracket h (x + y) z = bracket h x z + bracket h y z
  /-- A graded Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ {i j k} (h : i + j = k) (x : A i) (y z : A j),
    bracket h x (y + z) = bracket h x y + bracket h x z
  /-- A graded Lie ring bracket vanishes on the diagonal in each graded piece. -/
  protected lie_self : ∀ {i j} (h : i + i = j) (x : A i), bracket h x x = 0
  /-- Homogeneous symmetric sums of graded Lie ring brackets vanish. -/
  protected lie_antisymm : ∀ {i j k} (hij : i + j = k) (hji : j + i = k) (x : A i) (y : A j),
    bracket hij x y + bracket hji y x = 0
  /-- A graded Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ {i j k ij ik jk ijk} (hij : i + j = ij) (hik : i + k = ik)
      (hjk : j + k = jk) (hi : i + jk = ijk) (hk : ij + k = ijk) (hj : j + ik = ijk) (x : A i)
      (y : A j) (z : A k),
      bracket hi x (bracket hjk y z) =
        bracket hk (bracket hij x y) z + bracket hj y (bracket hik x z)

namespace GLieRing

/-- The piecewise multiplication from the `GLieRing` instance, as a bundled homomorphism. -/
@[simps]
def gBracketHom [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] {i j k} (h : i + j = k) :
    A i →+ A j →+ A k where
  toFun a :=
    { toFun := fun b => GBracket.bracket h a b
      map_zero' := by
        have := rfl (a := GBracket.bracket h a (0 : A j))
        nth_rw 1 [← add_zero 0] at this
        rwa [GLieRing.lie_add, add_eq_left] at this
      map_add' x y := by rw [GLieRing.lie_add] }
  map_zero' := by
    ext b
    have := rfl (a := GBracket.bracket h (0 : A i) b)
    nth_rw 1 [← add_zero 0] at this
    rwa [GLieRing.add_lie, add_eq_left] at this
  map_add' _ _ := by
    ext b
    simp [GLieRing.add_lie]

/-- The multiplication from the `GLieRing` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
def bracketHom [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gBracketHom A rfl

instance [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    Bracket (⨁ i, A i)  (⨁ i, A i) where
  bracket a b := bracketHom A a b

@[simp]
lemma bracketHom_apply [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    (a b : ⨁ i, A i) :
    bracketHom A a b = ⁅a, b⁆ := rfl

lemma rec_bracket [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j k l} (a : A i) (b : A j) (hk : i + j = k) (hl : i + j = l) (hkl : k = l) :
    Eq.rec (GBracket.bracket hk a b) hkl = GBracket.bracket hl a b := by
  grind

@[simp]
lemma bracket_of_of [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j} (a : A i) (b : A j) :
    ⁅of A i a, of A j b⁆ = of A (i + j) (GBracket.bracket rfl a b) := by
  simp [← bracketHom_apply]

/-- `GLieRing` implies a Lie ring structure. -/
instance toLieRing [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [GLieRing A] :
    LieRing (⨁ i, A i) :=
  { (inferInstance : AddCommGroup _) with
    bracket x y := ⁅x, y⁆
    add_lie _ _ _ := by simp [← bracketHom_apply]
    lie_add _ _ _ := by simp [← bracketHom_apply]
    lie_self x := by
      have hsum (i : ι) (a : A i) (f : (⨁ i, A i)) : ⁅(of A i a), f⁆ + ⁅f, (of A i a)⁆ = 0 := by
        induction f using DirectSum.induction_of with
        | h0 => simp [← bracketHom_apply]
        | ha j b f hj _ h =>
          simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at h ⊢
          rw [add_rotate, add_left_comm, h, add_zero]
          ext k
          by_cases h : i + j = k
          · simp [of_apply, h, add_comm i j ▸ h, rec_bracket, GLieRing.lie_antisymm]
          · simp [of_apply, h, add_comm i j ▸ h]
      induction x using DirectSum.induction_of with
      | h0 => simp [← bracketHom_apply]
      | ha j b f hj _ h =>
        simp only [← bracketHom_apply] at h hsum
        rw [← bracketHom_apply, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h,
          add_zero, add_assoc, add_comm (((bracketHom A) f) ((of A j) b)), hsum]
        simp [GLieRing.lie_self]
    leibniz_lie x y z := by
      have hboo (i j : ι) (a : A i) (b : A j) :
          ⁅of A i a, ⁅of A j b, z⁆⁆ = ⁅of A j b, ⁅of A i a, z⁆⁆ + ⁅⁅of A i a, of A j b⁆, z⁆ := by
        induction z using DirectSum.induction_of with
        | h0 => simp [← bracketHom_apply]
        | ha k c f _ _ ih =>
          simp only [← bracketHom_apply, map_add] at ih ⊢
          rw [ih]
          simp only [bracketHom_apply, ← add_assoc]
          rw [add_right_cancel_iff, add_right_comm, add_right_cancel_iff]
          ext l
          by_cases h : i + j + k = l
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h, rec_bracket,
              GLieRing.leibniz_lie, add_comm (GBracket.bracket _ (GBracket.bracket _ a b) c)]
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h]
      have hbo (i : ι) (a : A i) :
          ⁅of A i a, ⁅y, z⁆⁆ = ⁅y, ⁅of A i a, z⁆⁆ + ⁅⁅of A i a, y⁆, z⁆ := by
        induction y using DirectSum.induction_of with
        | h0 => simp [← bracketHom_apply]
        | ha j b f _ _ ih =>
          simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at ih ⊢
          rw [ih]
          simp only [bracketHom_apply, ← add_assoc]
          rw [add_right_cancel_iff, add_right_comm, add_right_cancel_iff]
          exact hboo i j a b
      induction x using DirectSum.induction_of with
      | h0 => simp [← bracketHom_apply]
      | ha i a f _ _ ih =>
        simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at ih ⊢
        rw [ih]
        simp only [bracketHom_apply, ← add_assoc]
        rw [add_right_cancel_iff, ← add_rotate, add_right_cancel_iff]
        exact hbo i a }

end GLieRing
