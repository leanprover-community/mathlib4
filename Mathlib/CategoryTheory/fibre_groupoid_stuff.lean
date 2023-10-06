import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.CommSq


universe u₁ v₁ u₂ v₂ w

open CategoryTheory Functor

variable {S : Type u₁} {C : Type u₂} [Category S] [Category C]

def ObjLift (p : S ⥤ C) (U : C) (x : S) : Prop := p.obj x = U

lemma ObjLift_image (p : S ⥤ C) (x : S) : ObjLift p (p.obj x) x := rfl

lemma eq_of_ObjLift {p : S ⥤ C} {U : C} {x : S} (h : ObjLift p U x) : p.obj x = U := h

--lemma eqToHom (U V : C) (h : U = V) : U ≅ V := by rw [h]

def HomLift (p : S ⥤ C) {x y : S} {U V : C} (f : U ⟶ V) (φ : x ⟶ y) (h₁ : ObjLift p U x)
  (h₂ : ObjLift p V y): Prop := CommSq (p.map φ) (eqToHom (eq_of_ObjLift h₁))
     (eqToHom (eq_of_ObjLift h₂)) f

def IsFibredInGroupoids (p : S ⥤ C) : Prop :=
  (∀ (X Y : C) (f : X ⟶ Y) (y : S) (hy : ObjLift p Y y), ∃ (x : S) (φ : x ⟶ y)
    (hx : ObjLift p X x), HomLift p f φ hx hy) ∧
  (∀ (x y z : S) (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y), (f ≫ p.map φ = p.map ψ) →
    ∃! (χ : z ⟶ y), HomLift p f χ (ObjLift_image p z) (ObjLift_image p y))

def IsCofibredInGroupoids (p : S ⥤ C) : Prop := IsFibredInGroupoids p.op

--lemma IsFibredInGroupoids_iff (p : S ⥤ C) : IsFibredInGroupoids p ↔

--instance test (p : S ⥤ C) (u : C) : Category (set.preimage p.obj u) := sorry


