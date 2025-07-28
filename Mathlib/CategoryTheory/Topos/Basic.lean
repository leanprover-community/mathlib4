/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Closed.PowerObjects
import Mathlib.CategoryTheory.Topos.Classifier
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and its direct consequences,
ideally up to the proof of existence of exponential objects and colimits.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v

open CategoryTheory Category Functor Limits MonoidalCategory PowerObject

variable (ℰ : Type u) [Category.{v} ℰ] [CartesianMonoidalCategory ℰ]

/-- An elementary topos is a category with a fixed subobject classifier and power objects. -/
class ElementaryTopos [HasPullbacks ℰ] where
  /-- A fixed choice of subobject classifier in `ℰ`. -/
  sc : Classifier ℰ (𝟙_ ℰ)
  /-- Assignment of power objects. -/
  P (B : ℰ) : ℰ
  /-- `P` actually assigns power objects. -/
  hP (B : ℰ) : IsPowerObjectOf sc B (P B)

namespace ElementaryTopos

variable {ℰ} [HasPullbacks ℰ] [ElementaryTopos ℰ]

/-- The P-transpose of a morphism `g : A ⟶ P B`. -/
def hat {A B : ℰ} (g : A ⟶ (P B)) : B ⊗ A ⟶ sc.Ω := (hP B).homEquiv.toFun g

/-- The P-transpose of a morphism `f : B × A ⟶ Ω`. -/
def unhat {A B : ℰ} (f : B ⊗ A ⟶ sc.Ω) : (A ⟶ (P B)) := (hP B).homEquiv.invFun f

@[simp]
lemma hat_unhat {A B : ℰ} (f : B ⊗ A ⟶ sc.Ω) : hat (unhat f) = f :=
  PowerObject.hat_unhat (hP B) f

@[simp]
lemma unhat_hat {A B : ℰ} (g : A ⟶ (P B)) : unhat (hat g) = g :=
  PowerObject.unhat_hat (hP B) g

/-- The element relation as a subobject of `B ⨯ (P B)`. -/
def ε (B : ℰ) : B ⊗ (P B) ⟶ sc.Ω := (hP B).homEquiv.toFun (𝟙 (P B))

lemma hatAsComp {A B : ℰ} (g : A ⟶ (P B)) : hat g = B ◁ g ≫ ε B :=
  PowerObject.hatAsComp (hP B) g

@[simp]
lemma P_comm {A B : ℰ} (f : B ⊗ A ⟶ sc.Ω) : B ◁ (unhat f) ≫ ε B = f :=
  PowerObject.comm (hP B) f

lemma P_uniq {A B : ℰ} (f : B ⊗ A ⟶ sc.Ω) (g : A ⟶ P B)
    (h : f = B ◁ g ≫ ε B) : g = unhat f := PowerObject.uniq (hP B) f g h

/-- The morphism `map h` is the functorial action on a morphism `h : B ⟶ C`,
    defined as the P-transpose of `εC ∘ (h ⨯ 𝟙)`. -/
def P_map {B C : ℰ} (h : B ⟶ C) : (P C) ⟶ (P B) :=
  PowerObject.map (hP B) (hP C) h

lemma P_dinaturality {B C : ℰ} (h : B ⟶ C) : h ▷ (P C) ≫ ε C = B ◁ P_map h ≫ ε B :=
  PowerObject.dinaturality (hP B) (hP C) h

lemma P_compose {B C D : ℰ} (h : B ⟶ C) (h' : C ⟶ D) : P_map (h ≫ h') = P_map h' ≫ P_map h :=
  PowerObject.compose (hP B) (hP C) (hP D) h h'

/-- The power object functor -/
def P_functor : ℰᵒᵖ ⥤ ℰ := PowerObject.functor P hP

end ElementaryTopos
