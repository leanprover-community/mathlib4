/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Functor.Const

/-!
# Fibers of functors
In this file we develop the theory of fibers of functors. Given a functor `p : 𝒳 ⥤ 𝒮`, we define
the fiber categories `Fiber p S` for every `S : 𝒮` as follows:
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

We also introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

The reason for introducing this typeclass is that in practice, when working with fibered categories
one often already has a collection of categories `Fib S` for every `S` that are equivalent to the
fibers `Fiber p S`. One would then like to use these categories `Fib S` directly, instead of working
through this equivalence of categories. By developing an API for the `HasFibers` typeclass, this
will be possible.For example, we develop the following lemmas:
- `HasFibersEssSurj` any object `a : 𝒳` lying over some `S : 𝒮` is isomorphic to the image of some
  `a' : Fib S`
- `HasFibersPullback` allows one to take pullbacks such that the codomain lies in one of the fibers
  `Fib S`.
- `HasFibersFactorization` (TODO: maybe call it `HasFibersInducedMap`, and the next `HasFibersFactorization`)
- `fiber_factorization` any morphism in `𝒳` can be factored as a morphism in some fiber `Fib S`
  followed by a pullback. (TODO: rename this lemma)

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types
`F : 𝒮ᵒᵖ ⥤ Type _`. The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a`
is an element of `F(S)`. The fiber category `Fiber p S` is then equivalent to the discrete category
`Fib S` with objects `a` in `F(S)`. In this case, the `HasFibers` instance is given by the
categories `F(S)` and the functor `ι` sends `a : F(S)` to `(S, a)` in the fibered category.
See `Presheaf.lean` for more details.
-/

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category IsCartesian IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

-- TODO: should it be this namespace?
namespace Fibered

/-- Fiber p S is the type of elements of 𝒳 mapping to S via p  -/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := {a : 𝒳 // p.obj a = S}

def fiberHom {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (a b : Fiber p S) := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}

instance {p : 𝒳 ⥤ 𝒮} {S : 𝒮} (a b : Fiber p S) (φ : fiberHom a b) : IsHomLift p (𝟙 S) φ.1 := φ.2

/-- Fiber p S has the structure of a category by taking the morphisms to be those lying over 𝟙 S -/
@[simps]
instance FiberCategory (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by apply (comp_id (𝟙 S)) ▸ IsHomLift.comp (p:=p) (𝟙 S) (𝟙 S) φ.1 ψ.1⟩

/-- The object .... -/
--@[simps]
def Fiber.mk_obj {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

/-- The object ... -/
--@[simps]
def Fiber.mk_map {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} (ha : p.obj a = S) (hb : p.obj b = S) (φ : a ⟶ b)
    [IsHomLift p (𝟙 S) φ] : Fiber.mk_obj ha ⟶ Fiber.mk_obj hb := ⟨φ, inferInstance⟩

@[simp]
lemma Fiber.mk_map_id {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} [IsHomLift p (𝟙 S) (𝟙 a)] :
    Fiber.mk_map (domain_eq p (𝟙 S) (𝟙 a)) (domain_eq p (𝟙 S) (𝟙 a)) (𝟙 a) =
      𝟙 (Fiber.mk_obj (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

@[simp]
lemma Fiber.mk_map_coe {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} (ha : p.obj a = S) (hb : p.obj b = S)
    (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] : (Fiber.mk_map ha hb φ).val = φ := rfl

@[simp]
lemma Fiber.mk_obj_coe (p : 𝒳 ⥤ 𝒮) (a : 𝒳) : (Fiber.mk_obj (p:=p) (a:=a) rfl).1 = a := rfl

/-- The functor including Fiber p S into 𝒳 -/
@[simps]
def FiberInclusion (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (Fiber p S) ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance FiberInclusionFaithful (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : Functor.Faithful (FiberInclusion p S) where
  map_injective := Subtype.val_inj.1

@[ext]
lemma Fiber.hom_ext {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : Fiber p S} (φ ψ : a ⟶ b) : φ.1 = ψ.1 → φ = ψ :=
  Subtype.ext

@[simp]
lemma Fiber.val_comp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : Fiber p S} (φ : a ⟶ b)
    (ψ : b ⟶ c) : (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

lemma Fiber.mk_map_com {p :𝒳 ⥤ 𝒮} {S : 𝒮} {a b c : 𝒳}
    -- TODO: these conditions are unecessary
    (ha : p.obj a = S) (hb : p.obj b = S) (hc : p.obj c = S)
    (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : Fiber.mk_map ha hc (φ ≫ ψ) =
    Fiber.mk_map ha hb φ ≫ Fiber.mk_map hb hc ψ := rfl

/-- Given a functor F : C ⥤ 𝒳 mapping constantly to some S in the base,
  we get an induced functor C ⥤ Fiber p S -/
-- TODO: should prove some API for this externally?
@[simps]
def FiberInducedFunctor {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C]
  {F : C ⥤ 𝒳} (hF : F ⋙ p = (const C).obj S) : C ⥤ Fiber p S where
    obj := fun x => ⟨F.obj x, by simp only [←comp_obj, hF, const_obj_obj]⟩
    map := fun φ => ⟨F.map φ, by
      apply IsHomLift.of_commSq
      constructor; simpa using (eqToIso hF).hom.naturality φ ⟩

/-- The natural transformation between F : C ⥤ 𝒳 and .... -/
def FiberInducedFunctorNat {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F ≅ (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) where
    hom := { app := fun a => 𝟙 (F.obj a) }
    inv := { app := fun a => 𝟙 ((FiberInducedFunctor hF ⋙ FiberInclusion p S).obj a) }

lemma FiberInducedFunctorComp {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type _} [Category C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S) : F = (FiberInducedFunctor hF) ⋙ (FiberInclusion p S) :=
  Functor.ext_of_iso (FiberInducedFunctorNat hF) (fun x => by rfl) (fun x => by rfl)

end Fibered
