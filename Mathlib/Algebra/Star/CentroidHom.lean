/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.CentroidHom
public import Mathlib.Algebra.Star.StarRingHom
public import Mathlib.Algebra.Star.Subsemiring
public import Mathlib.Algebra.Star.Basic

/-!
# Centroid homomorphisms on Star Rings

When a (nonunital, non-associative) semiring is equipped with an involutive automorphism the
center of the centroid becomes a star ring in a natural way and the natural mapping of the centre of
the semiring into the centre of the centroid becomes a *-homomorphism.

## Tags

centroid
-/

@[expose] public section

variable {α : Type*}

namespace CentroidHom

section NonUnitalNonAssocStarSemiring

variable [NonUnitalNonAssocSemiring α] [StarRing α]

instance : Star (CentroidHom α) where
  star f :=
  { toFun a := star (f (star a))
    map_zero' := by simp
    map_add' _ _ := by simp
    map_mul_left' _ _ := by simp [map_mul_right]
    map_mul_right' _ _ := by simp [map_mul_left] }

@[simp] lemma star_apply (f : CentroidHom α) (a : α) : (star f) a = star (f (star a)) := rfl

instance instStarAddMonoid : StarAddMonoid (CentroidHom α) where
  star_involutive f := ext (by simp)
  star_add _ _ := ext fun _ => star_add _ _

instance : Star (Subsemiring.center (CentroidHom α)) where
  star f := ⟨star (f : CentroidHom α), Subsemiring.mem_center_iff.mpr (fun g => ext (fun a =>
    calc
      g (star (f (star a))) = star (star g (f (star a))) := by rw [star_apply, star_star]
      _ = star ((star g * f) (star a)) := rfl
      _ = star ((f * star g) (star a)) := by rw [f.property.comm]
      _ = star (f (star (g a))) := by simpa using by rfl))⟩

instance instStarAddMonoidCenter : StarAddMonoid (Subsemiring.center (CentroidHom α)) where
  star_involutive f := SetCoe.ext (star_involutive f.val)
  star_add f g := SetCoe.ext (star_add f.val g.val)

set_option backward.isDefEq.respectTransparency false in
instance : StarRing (Subsemiring.center (CentroidHom α)) where
  __ := instStarAddMonoidCenter
  star_mul f g := by
    ext a
    calc
      star (f * g) a = star (g * f) a := by rw [mul_comm]
      _ = star (g (f (star a))) := rfl
      _ = star (g (star (star (f (star a))))) := by rw [star_star]
      _ = (star g * star f) a := rfl

/-- The canonical *-homomorphism embedding the center of `CentroidHom α` into `CentroidHom α`. -/
def centerStarEmbedding : Subsemiring.center (CentroidHom α) →⋆ₙ+* CentroidHom α where
  toNonUnitalRingHom :=
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
  map_star' _ := rfl

theorem star_centerToCentroidCenter (z : NonUnitalStarSubsemiring.center α) :
    star (centerToCentroidCenter z) =
      (centerToCentroidCenter (star z : NonUnitalStarSubsemiring.center α)) := by
  ext a
  calc
      (star (centerToCentroidCenter z)) a = star (z * star a) := rfl
      _ = a * star z := by simp
      _ = (star z) * a := by rw [(star z).property.comm]
      _ = (centerToCentroidCenter ((star z) : NonUnitalStarSubsemiring.center α)) a := rfl

/-- The canonical *-homomorphism from the center of a non-unital, non-associative *-semiring into
the center of its centroid. -/
def starCenterToCentroidCenter :
    NonUnitalStarSubsemiring.center α →⋆ₙ+* Subsemiring.center (CentroidHom α) where
  toNonUnitalRingHom := centerToCentroidCenter
  map_star' _ := (star_centerToCentroidCenter _).symm

/-- The canonical homomorphism from the center into the centroid -/
def starCenterToCentroid : NonUnitalStarSubsemiring.center α →⋆ₙ+* CentroidHom α :=
  NonUnitalStarRingHom.comp (centerStarEmbedding) (starCenterToCentroidCenter)

lemma starCenterToCentroid_apply (z : NonUnitalStarSubsemiring.center α) (a : α) :
    (starCenterToCentroid z) a = z * a := rfl

/--
Let `α` be a star ring with commutative centroid. Then the centroid is a star ring.
-/
@[reducible]
def starRingOfCommCentroidHom (mul_comm : IsMulCommutative (CentroidHom α)) :
    StarRing (CentroidHom α) where
  __ := instStarAddMonoid
  star_mul _ _ := ext (by simp [mul_comm.comm])

end NonUnitalNonAssocStarSemiring

section NonAssocStarSemiring

variable [NonAssocSemiring α] [StarRing α]

/-- The canonical isomorphism from the center of a (non-associative) semiring onto its centroid. -/
def starCenterIsoCentroid : StarSubsemiring.center α ≃⋆+* CentroidHom α where
  __ := starCenterToCentroid
  invFun T := ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
  left_inv z := Subtype.ext (by simp [starCenterToCentroid_apply])
  right_inv T := ext (by simp [starCenterToCentroid_apply, ← map_mul_right])

@[simp]
lemma starCenterIsoCentroid_apply (a : ↥(NonUnitalStarSubsemiring.center α)) :
    starCenterIsoCentroid a = starCenterToCentroid a := rfl

@[simp]
lemma starCenterIsoCentroid_symm_apply_coe (T : CentroidHom α) :
    ↑(starCenterIsoCentroid.symm T) = T 1 := rfl

end NonAssocStarSemiring

end CentroidHom
