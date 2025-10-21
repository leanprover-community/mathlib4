/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Final

/-!
# Action of an initial functor on sections

Given `F : C ⥤ D` and `P : D ⥤ Type w`, we define a map
`sectionsPrecomp F : P.sections → (F ⋙ P).sections` and
show that it is a bijection when `F` is initial.
As `Functor.sections` identify to limits of functors to types
(at least under suitable universe assumptions), this could
be deduced from general results about limits and
initial functors, but we provide a more down to earth proof.

-/

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- When `F : C ⥤ D` and `P : D ⥤ Type _`, this is the obvious map
`P.section → (F ⋙ P).sections`. -/
@[simps]
def sectionsPrecomp (F : C ⥤ D) {P : D ⥤ Type w} (x : P.sections) :
    (F ⋙ P).sections where
  val _ := x.val _
  property _ := x.property _

lemma bijective_sectionsPrecomp (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial] :
    Function.Bijective (F.sectionsPrecomp (P := P)) := by
  refine ⟨fun s₁ s₂ h ↦ ?_, fun t ↦ ?_⟩
  · ext Y
    let X : CostructuredArrow F Y := Classical.arbitrary _
    have := congr_fun (congr_arg Subtype.val h) X.left
    have h₁ := s₁.property X.hom
    have h₂ := s₂.property X.hom
    dsimp at this h₁ h₂
    rw [← h₁, this, h₂]
  · let X (Y : D) : CostructuredArrow F Y := Classical.arbitrary _
    let val (Y : D) : P.obj Y := P.map (X Y).hom (t.val (X Y).left)
    have h (Y : D) (Z : CostructuredArrow F Y) :
        val Y = P.map Z.hom (t.val Z.left) :=
      constant_of_preserves_morphisms (α := P.obj Y)
        (fun (Z : CostructuredArrow F Y) ↦ P.map Z.hom (t.val Z.left)) (by
          intro Z₁ Z₂ φ
          dsimp
          rw [← t.property φ.left]
          dsimp
          rw [← FunctorToTypes.map_comp_apply, CostructuredArrow.w]) _ _
    refine ⟨⟨val, fun {Y₁ Y₂} f ↦ ?_⟩, ?_⟩
    · rw [h Y₁ (X Y₁), h Y₂ ((CostructuredArrow.map f).obj (X Y₁))]
      simp
    · ext X : 2
      simpa using h (F.obj X) (CostructuredArrow.mk (𝟙 _))

end Functor

end CategoryTheory
