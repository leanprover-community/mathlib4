/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Functor.Const

/-!

# Fibers of functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴`, the fiber categories `Fiber p S` for every
`S : 𝒮` as follows
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

For any category `C` equipped with a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at `S`,
we define a functor `inducedFunctor : C ⥤ Fiber p S` that `F` factors through.
-/

@[expose] public section


universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

open IsHomLift

namespace Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- `Fiber p S` is the type of elements of `𝒳` mapping to `S` via `p`. -/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := { a : 𝒳 // p.obj a = S }

namespace Fiber

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

/-- `Fiber p S` has the structure of a category with morphisms being those lying over `𝟙 S`. -/
instance fiberCategory : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩

/-- The functor including `Fiber p S` into `𝒳`. -/
def fiberInclusion : Fiber p S ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance {a b : Fiber p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) (fiberInclusion.map φ) := φ.2

@[ext]
lemma hom_ext {a b : Fiber p S} {φ ψ : a ⟶ b}
    (h : fiberInclusion.map φ = fiberInclusion.map ψ) : φ = ψ :=
  Subtype.ext h

instance : (fiberInclusion : Fiber p S ⥤ _).Faithful where

lemma fiberInclusion_obj_inj : (fiberInclusion : Fiber p S ⥤ _).obj.Injective :=
  fun _ _ f ↦ Subtype.val_inj.1 f

set_option backward.defeqAttrib.useBackward true in
/-- For fixed `S : 𝒮` this is the natural isomorphism between `fiberInclusion ⋙ p` and the constant
function valued at `S`. -/
@[simps!]
def fiberInclusionCompIsoConst : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S :=
  NatIso.ofComponents (fun X ↦ eqToIso X.2)
    (fun φ ↦ by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])

lemma fiberInclusion_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).obj S :=
  Functor.ext_of_iso fiberInclusionCompIsoConst (fun x ↦ x.2)

/-- The object of the fiber over `S` corresponding to a `a : 𝒳` such that `p(a) = S`. -/
def mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

@[simp]
lemma fiberInclusion_mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    fiberInclusion.obj (mk ha) = a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism in the fiber over `S` corresponding to a morphism in `𝒳` lifting `𝟙 S`. -/
def homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    mk (domain_eq p (𝟙 S) φ) ⟶ mk (codomain_eq p (𝟙 S) φ) :=
  ⟨φ, inferInstance⟩

@[simp]
lemma fiberInclusion_homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    fiberInclusion.map (homMk p S φ) = φ :=
  rfl

@[simp]
lemma homMk_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] :
    homMk p S (𝟙 a) = 𝟙 (mk (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

@[simp]
lemma homMk_comp {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : homMk p S φ ≫ homMk p S ψ = homMk p S (φ ≫ ψ) :=
  rfl

section

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)

set_option backward.defeqAttrib.useBackward true in
/-- Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get an induced functor `C ⥤ Fiber p S` that `F` factors through. -/
def inducedFunctor : C ⥤ Fiber p S where
  obj x := ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
  map φ := ⟨F.map φ, of_commsq _ _ _ (congr_obj hF _) (congr_obj hF _) <|
    by simpa using (eqToIso hF).hom.naturality φ⟩

/-- Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get a natural isomorphism between `inducedFunctor _ ⋙ fiberInclusion` and `F`. -/
@[simps!]
def inducedFunctorCompIsoSelf : (inducedFunctor hF) ⋙ fiberInclusion ≅ F := .refl _

lemma inducedFunctor_comp : (inducedFunctor hF) ⋙ fiberInclusion = F := rfl

@[simp]
lemma inducedFunctor_comp_obj (X : C) :
    fiberInclusion.obj ((inducedFunctor hF).obj X) = F.obj X := rfl

@[simp]
lemma inducedFunctor_comp_map {X Y : C} (f : X ⟶ Y) :
    fiberInclusion.map ((inducedFunctor hF).map f) = F.map f := rfl

end

end Fiber

end Functor

end CategoryTheory
