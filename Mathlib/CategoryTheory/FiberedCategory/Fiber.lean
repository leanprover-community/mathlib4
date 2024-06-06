/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

-- TODO: fix imports
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Functor.Const

/-!

# Fibers of a functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴` the fiber categories `Fiber p S` for every
`S : 𝒮` as follows:
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

-/

-- TODO: u, v should be flipped here?
universe u₁ v₁ u₂ v₂ u₃ v₃ w

open CategoryTheory Functor Category IsCartesian IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Fiber p S is the type of elements of 𝒳 mapping to S via p  -/
-- TODO: coe?
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

namespace Fiber

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

def Hom (a b : Fiber p S) := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}

instance (a b : Fiber p S) (φ : Hom a b) : IsHomLift p (𝟙 S) φ.1 := φ.2

/-- Fiber p S has the structure of a category by taking the morphisms to be those lying over 𝟙 S -/
@[simps]
instance FiberCategory : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, inferInstance⟩

/-- The object .... -/
@[simps]
def mk_obj {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

/-- The object ... -/
@[simps]
def mk_map {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
  mk_obj (domain_eq p (𝟙 S) φ) ⟶ mk_obj (codomain_eq p (𝟙 S) φ) := ⟨φ, inferInstance⟩

@[simp]
lemma mk_map_id {a : 𝒳} [IsHomLift p (𝟙 S) (𝟙 a)] :
    mk_map (𝟙 a) = 𝟙 (mk_obj (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

/-- The functor including Fiber p S into 𝒳 -/
@[simps]
def FiberInclusion (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusionFaithful (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Functor.Faithful (FiberInclusion p S) where
  map_injective := Subtype.val_inj.1

@[ext]
lemma hom_ext {a b : Fiber p S} (φ ψ : a ⟶ b) : φ.1 = ψ.1 → φ = ψ :=
  Subtype.ext

@[simp]
lemma val_comp {a b c : Fiber p S} (φ : a ⟶ b)
    (ψ : b ⟶ c) : (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

lemma mk_map_com {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    -- TODO: mk_map is annoying here, maybe make more variables explicit?
    [IsHomLift p (𝟙 S) ψ] : mk_map (φ ≫ ψ) = mk_map φ ≫ mk_map (p:=p) (S:=S) ψ :=
  rfl

section

-- TODO: which parameters should be explicit here? Also F, S?
variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)

/-- Given a functor F : C ⥤ 𝒳 mapping constantly to some S in the base,
  we get an induced functor C ⥤ Fiber p S -/
@[simps]
def FiberInducedFunctor : C ⥤ Fiber p S where
  obj := fun x ↦ ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
  map := fun φ ↦ ⟨F.map φ, by
    apply IsHomLift.of_commSq
    -- TODO: of_commsq lemma (which applies constructor automatically?)
    constructor; simpa using (eqToIso hF).hom.naturality φ ⟩

/-- The natural transformation between F : C ⥤ 𝒳 and .... -/
def FiberInducedFunctorNat : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) where
  hom := { app := fun a ↦ 𝟙 (F.obj a) }
  inv := { app := fun a ↦ 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion p S).obj a) }

-- TODO: simp lemma? If so should switch sides in the equality
lemma fiberInducedFunctor_comp : F = (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) :=
  Functor.ext_of_iso (FiberInducedFunctorNat hF) (fun _ ↦ rfl) (fun _ ↦ rfl)

end

-- TODO: move earlier in this file?

/-- Now we define the standard/canonical fiber associated to a fibered category.
When the user does not wish to supply specific fiber categories, this will be the default choice. -/
def CompConstNat (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p ≅ (const (Fiber p S)).obj S where
  hom := {
    app := fun x => eqToHom x.prop
    naturality := fun x y φ => by simpa using (commSq p (𝟙 S) φ.val).w}
  inv := {
    app := fun x => eqToHom (x.prop).symm
    naturality := fun x y φ =>  by
      -- TODO: add this have into API?
      have := by simpa [comp_eqToHom_iff] using (commSq p (𝟙 S) φ.val).w
      simp [this] }

lemma comp_const (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p = (const (Fiber p S)).obj S := by
  apply Functor.ext_of_iso (CompConstNat p S)
  all_goals intro x; simp [CompConstNat, x.2]

end Fiber
