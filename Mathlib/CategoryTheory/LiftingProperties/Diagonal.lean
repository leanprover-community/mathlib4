/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Unique lifting via the codiagonal and the diagonal

For `i : A ⟶ B` and `p : X ⟶ Y`, uniqueness of lifts of squares from `i` to `p` is equivalent
to the ordinary (non-unique) lifting property of `i` against the diagonal
`X ⟶ X ×_Y X` (`pullback.diagonal p`), and also to that of the codiagonal
`B ⊔_A B ⟶ B` (`pushout.codiagonal i`) against `p`: a pair of lifts of a square from `i` to `p`
corresponds to a lift of a square built from the (co)diagonal. Consequently the unique lifting
property is the conjunction of two ordinary lifting properties.

## Main declarations

* `hasAtMostOneLiftingProperty_iff_codiagonal`, `hasAtMostOneLiftingProperty_iff_diagonal`;
* `hasUniqueLiftingProperty_iff_lifting_and_codiagonal`,
  `hasUniqueLiftingProperty_iff_lifting_and_diagonal`.
-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

section Codiagonal

variable [HasPushout i i]

/-- Lifts against `i` are unique if and only if lifts against the codiagonal of
`i` exist. -/
theorem hasAtMostOneLiftingProperty_iff_codiagonal :
    HasAtMostOneLiftingProperty i p ↔ HasLiftingProperty (pushout.codiagonal i) p := by
  constructor
  · intro h
    refine ⟨fun {f g} sq => ?_⟩
    -- the two legs of `f` are lifts of the same square under `i`, hence agree
    have hl : pushout.inl i i ≫ f = pushout.inr i i ≫ f :=
      CommSq.lift_eq_of_hasAtMostOneLiftingProperty i p
        (sq := ⟨by rw [assoc, assoc, sq.w, pushout.inl_codiagonal_assoc]⟩)
        rfl (by rw [assoc, sq.w, pushout.inl_codiagonal_assoc])
        (pushout.condition_assoc f).symm (by rw [assoc, sq.w, pushout.inr_codiagonal_assoc])
    exact CommSq.HasLift.mk'
      { l := pushout.inl i i ≫ f
        fac_left := pushout.hom_ext (by rw [pushout.inl_codiagonal_assoc])
          (by rw [pushout.inr_codiagonal_assoc, hl])
        fac_right := by rw [assoc, sq.w, pushout.inl_codiagonal_assoc] }
  · intro h
    refine ⟨fun {f g} sq => ⟨fun l₁ l₂ => ?_⟩⟩
    -- glue the two lifts to a square under the codiagonal; both are legs of its lift
    have sq' : CommSq (pushout.desc l₁.l l₂.l (l₁.fac_left.trans l₂.fac_left.symm))
        (pushout.codiagonal i) p g :=
      ⟨pushout.hom_ext
        (by rw [pushout.inl_desc_assoc, l₁.fac_right, pushout.inl_codiagonal_assoc])
        (by rw [pushout.inr_desc_assoc, l₂.fac_right, pushout.inr_codiagonal_assoc])⟩
    apply CommSq.LiftStruct.ext
    calc l₁.l = pushout.inl i i ≫ pushout.codiagonal i ≫ sq'.lift := by
            rw [sq'.fac_left, pushout.inl_desc]
      _ = pushout.inr i i ≫ pushout.codiagonal i ≫ sq'.lift := by
            rw [pushout.inl_codiagonal_assoc, pushout.inr_codiagonal_assoc]
      _ = l₂.l := by rw [sq'.fac_left, pushout.inr_desc]

/-- Lifts against `i` exist uniquely if and only if ordinary lifts exist against
both `i` and its codiagonal. -/
theorem hasUniqueLiftingProperty_iff_lifting_and_codiagonal :
    HasUniqueLiftingProperty i p ↔
      HasLiftingProperty i p ∧ HasLiftingProperty (pushout.codiagonal i) p :=
  ⟨fun h => ⟨h.toHasLiftingProperty,
    (hasAtMostOneLiftingProperty_iff_codiagonal i p).mp h.toHasAtMostOneLiftingProperty⟩,
   fun ⟨hi, hc⟩ => { hi, (hasAtMostOneLiftingProperty_iff_codiagonal i p).mpr hc with }⟩

end Codiagonal

section Diagonal

variable [HasPullback p p]

/-- Lifts against `p` are unique if and only if lifts against the diagonal of
`p` exist. -/
theorem hasAtMostOneLiftingProperty_iff_diagonal :
    HasAtMostOneLiftingProperty i p ↔ HasLiftingProperty i (pullback.diagonal p) := by
  constructor
  · intro h
    refine ⟨fun {f g} sq => ?_⟩
    -- the two legs of `g` are lifts of the same square under `i`, hence agree
    have h₁ : i ≫ g ≫ pullback.fst p p = f := by
      rw [← assoc, ← sq.w, assoc, pullback.diagonal_fst, comp_id]
    have h₂ : i ≫ g ≫ pullback.snd p p = f := by
      rw [← assoc, ← sq.w, assoc, pullback.diagonal_snd, comp_id]
    have sq₀ : CommSq f i p (g ≫ pullback.fst p p ≫ p) :=
      ⟨by rw [← assoc, ← sq.w, assoc, pullback.diagonal_fst_assoc]⟩
    have hl : g ≫ pullback.fst p p = g ≫ pullback.snd p p :=
      CommSq.lift_eq_of_hasAtMostOneLiftingProperty i p (sq := sq₀)
        h₁ (assoc _ _ _) h₂ (by rw [assoc, ← pullback.condition])
    exact CommSq.HasLift.mk'
      { l := g ≫ pullback.fst p p
        fac_left := h₁
        fac_right := pullback.hom_ext
          (by rw [assoc, assoc, pullback.diagonal_fst, comp_id])
          (by rw [assoc, assoc, pullback.diagonal_snd, comp_id, hl]) }
  · intro h
    refine ⟨fun {f g} sq => ⟨fun l₁ l₂ => ?_⟩⟩
    -- glue the two lifts to a square over the diagonal; both are legs of its lift
    have sq' : CommSq f i (pullback.diagonal p)
        (pullback.lift l₁.l l₂.l (l₁.fac_right.trans l₂.fac_right.symm)) :=
      ⟨pullback.hom_ext
        (by rw [assoc, assoc, pullback.diagonal_fst, pullback.lift_fst, comp_id, l₁.fac_left])
        (by rw [assoc, assoc, pullback.diagonal_snd, pullback.lift_snd, comp_id, l₂.fac_left])⟩
    apply CommSq.LiftStruct.ext
    calc l₁.l = (sq'.lift ≫ pullback.diagonal p) ≫ pullback.fst p p := by
            rw [sq'.fac_right, pullback.lift_fst]
      _ = (sq'.lift ≫ pullback.diagonal p) ≫ pullback.snd p p := by
            rw [assoc, assoc, pullback.diagonal_fst, pullback.diagonal_snd]
      _ = l₂.l := by rw [sq'.fac_right, pullback.lift_snd]

/-- Lifts against `p` exist uniquely if and only if ordinary lifts exist against
both `p` and its diagonal. -/
theorem hasUniqueLiftingProperty_iff_lifting_and_diagonal :
    HasUniqueLiftingProperty i p ↔
      HasLiftingProperty i p ∧ HasLiftingProperty i (pullback.diagonal p) :=
  ⟨fun h => ⟨h.toHasLiftingProperty,
    (hasAtMostOneLiftingProperty_iff_diagonal i p).mp h.toHasAtMostOneLiftingProperty⟩,
   fun ⟨hp, hd⟩ => { hp, (hasAtMostOneLiftingProperty_iff_diagonal i p).mpr hd with }⟩

end Diagonal

end CategoryTheory
