/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.Functor.Const

/-!

# Fibers of a functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴` the fiber categories `Fiber p S` for every
`S : 𝒮` as follows:
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Fiber p S is the type of elements of 𝒳 mapping to S via p  -/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

namespace Fiber

def Hom {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (a b : Fiber p S) := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}

instance {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (a b : Fiber p S) (φ : Hom a b) : IsHomLift p (𝟙 S) φ.1 := φ.2

/-- `Fiber p S` has the structure of a category with morphisms being those lying over `𝟙 S`. -/
@[simps]
instance FiberCategory {p : 𝒳 ⥤ 𝒮} {S : 𝒮} : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, inferInstance⟩

/-- The object of the fiber over `S` corresponding to a `a : 𝒳` such that `p(a) = S`. -/
@[simps]
def mk_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

@[ext]
lemma hom_ext {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : Fiber p S} (φ ψ : a ⟶ b) : φ.1 = ψ.1 → φ = ψ :=
  Subtype.ext

/-- The morphism in the fiber over `S` corresponding to a morphism in `𝒳` lifting `𝟙 S`. -/
@[simps]
def mk_map (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    mk_obj (domain_eq p (𝟙 S) φ) ⟶ mk_obj (codomain_eq p (𝟙 S) φ) :=
  ⟨φ, inferInstance⟩

@[simp]
lemma mk_map_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] :
    mk_map p S (𝟙 a) = 𝟙 (mk_obj (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

@[simp]
lemma val_comp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : Fiber p S} (φ : a ⟶ b) (ψ : b ⟶ c) :
    (φ ≫ ψ).1 = φ.1 ≫ ψ.1 :=
  rfl

@[simp]
lemma mk_map_comp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : mk_map p S φ ≫ mk_map p S ψ = mk_map p S (φ ≫ ψ) :=
  rfl

section

variable (p : 𝒳 ⥤ 𝒮) (S : 𝒮)

/-- The functor including `Fiber p S` into `𝒳` -/
@[simps]
def FiberInclusion : (Fiber p S) ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusion.Faithful : Functor.Faithful (FiberInclusion p S) where
  map_injective := Subtype.val_inj.1

lemma FiberInclusion.comp_const : (FiberInclusion p S) ⋙ p = (const (Fiber p S)).obj S :=
  Functor.ext (fun x ↦ x.2) (fun x y f ↦ by apply fac' p (𝟙 S) f.1)

end

section

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)

/-- Given a functor F : C ⥤ 𝒳 mapping constantly to some S in the base,
  we get an induced functor C ⥤ Fiber p S -/
@[simps]
def FiberInducedFunctor : C ⥤ Fiber p S where
  obj := fun x ↦ ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
  map := fun φ ↦ ⟨F.map φ, of_commsq _ _ _ _ _ <| by simpa using (eqToIso hF).hom.naturality φ⟩

-- /-- The natural transformation between F : C ⥤ 𝒳 and .... -/
-- def FiberInducedFunctorNat : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) where
--   hom := { app := fun a ↦ 𝟙 (F.obj a) }
--   inv := { app := fun a ↦ 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion p S).obj a) }

lemma fiberInducedFunctor_comp : (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) = F :=
  Functor.ext (fun x ↦ rfl) (by simp)
  -- Functor.ext_of_iso (FiberInducedFunctorNat hF) (fun _ ↦ rfl) (fun _ ↦ rfl)

end

end Fiber
