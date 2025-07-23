/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Topos.Classifier
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/


universe u v

open CategoryTheory Category Functor Limits MonoidalCategory Opposite

variable {ℰ : Type u} [Category.{v} ℰ] [CartesianMonoidalCategory ℰ]

/-- The covariant functor `B ⊗ [] ⟶ C` from `ℰᵒᵖ` to `Type`. -/
def WhiskeredHom (B C : ℰ) : ℰᵒᵖ ⥤ Type v :=
  ⟨ ⟨ fun A ↦ B ⊗ unop A ⟶ C, fun f g ↦ (B ◁ unop f) ≫ g ⟩,
    fun A ↦ by
      have : unop (𝟙 A) = 𝟙 (unop A) := by rfl
      ext; simp[this],
    fun f f' ↦ by
      have : B ◁ unop (f ≫ f') = B ◁ unop f' ≫ B ◁ unop f := by aesop_cat
      ext; simp[this] ⟩

/-- `P` is a power object of `B` if it represents the functor `WhiskeredHom B hc.Ω`. -/
def IsPowerObjectOf (hc : Classifier ℰ (𝟙_ ℰ)) (B P : ℰ) :=
  RepresentableBy (WhiskeredHom B hc.Ω) P

variable (ℰ)

/-- An elementary topos is a category with a fixed subobject classifier and power objects. -/
class ElementaryTopos [HasPullbacks ℰ] where
  /-- A fixed choice of subobject classifier in `ℰ`. -/
  hc : Classifier ℰ (𝟙_ ℰ)
  /-- Every `B` has a power object `P B`. -/
  P (B : ℰ) : ℰ
  /-- `P B` is a power object of `B`. -/
  hP (B : ℰ) : IsPowerObjectOf hc B (P B)

namespace ElementaryTopos

variable {ℰ} [HasPullbacks ℰ] [ElementaryTopos ℰ]

/-- The P-transpose of a morphism `g : A ⟶ P B`. -/
def hat {A : ℰ} (B : ℰ) (g : A ⟶ P B) : B ⊗ A ⟶ hc.Ω :=
  (hP B).homEquiv.toFun g

/-- The P-transpose of a morphism `f : B × A ⟶ Ω`. -/
def unhat {A B : ℰ} (f : B ⊗ A ⟶ hc.Ω) : (A ⟶ P B) :=
  (hP B).homEquiv.invFun f

@[simp]
lemma hat_unhat {A B : ℰ} (f : B ⊗ A ⟶ hc.Ω) :
  hat B (unhat f) = f := (hP B).homEquiv.apply_symm_apply f

@[simp]
lemma unhat_hat {A B : ℰ} (g : A ⟶ P B) :
  unhat (hat B g) = g := (hP B).homEquiv.symm_apply_apply g

/-- The element relation as a subobject of `B ⨯ (P B)`. -/
def ε_ (B : ℰ) : B ⊗ (P B) ⟶ hc.Ω :=
  (hP B).homEquiv.toFun (𝟙 (P B))

def comm {A B : ℰ} (f : B ⊗ A ⟶ hc.Ω) : f = (B ◁ (unhat f)) ≫ (ε_ B) := sorry

end ElementaryTopos
