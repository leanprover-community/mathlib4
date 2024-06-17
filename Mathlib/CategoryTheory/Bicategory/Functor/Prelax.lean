/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic

/-!

# Prelax functors

This file defines lax prefunctors and prelax functors between bicategories. The point of these
definitions is to give some API that will be helpful in both the development of Lax and Oplax
functors.

A lax prefunctor `F` between quivers `B` and `C`, equipped with quiver structures on the hom types,
consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,

A prelax functor is a lax prefunctor such that `map₂` is a functor. Namely, it satisfies
* `F.map₂ (𝟙 f) = 𝟙 (F.map f)`,
* `F.map₂ (η ≫ θ) = F.map₂ η ≫ F.map₂ θ`.

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
variable {C : Type u₂} [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)]
variable {D : Type u₃} [Quiver.{v₃ + 1} D] [∀ a b : D, Quiver.{w₃ + 1} (a ⟶ b)]

/-- A lax prefunctor between bicategories consists of functions between objects,
1-morphisms, and 2-morphisms. This structure will be extended to define `PrelaxFunctor`.
-/
structure LaxPreFunctor (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)]
  (C : Type u₂) [Quiver.{v₂ + 1} C] [∀ a b : C, Quiver.{w₂ + 1} (a ⟶ b)] extends
  Prefunctor B C where
  /-- The action of a prelax functor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
#align category_theory.prelax_functor CategoryTheory.LaxPreFunctor

initialize_simps_projections LaxPreFunctor (+toPrefunctor, -obj, -map)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc LaxPreFunctor.toPrefunctor

namespace LaxPreFunctor

attribute [coe] CategoryTheory.LaxPreFunctor.toPrefunctor

instance hasCoeToPrefunctor : Coe (LaxPreFunctor B C) (Prefunctor B C) :=
  ⟨toPrefunctor⟩
#align category_theory.prelax_functor.has_coe_to_prefunctor CategoryTheory.LaxPreFunctor.hasCoeToPrefunctor

variable (F : LaxPreFunctor B C)

-- Porting note: deleted syntactic tautologies `toPrefunctor_eq_coe : F.toPrefunctor = F`
-- and `to_prefunctor_obj : (F : Prefunctor B C).obj = F.obj`
-- and `to_prefunctor_map`
#noalign category_theory.prelax_functor.to_prefunctor_eq_coe
#noalign category_theory.prelax_functor.to_prefunctor_obj
#noalign category_theory.prelax_functor.to_prefunctor_map

/-- The identity prelax functor. -/
@[simps]
def id (B : Type u₁) [Quiver.{v₁ + 1} B] [∀ a b : B, Quiver.{w₁ + 1} (a ⟶ b)] : LaxPreFunctor B B :=
  { Prefunctor.id B with map₂ := fun η => η }
#align category_theory.prelax_functor.id CategoryTheory.LaxPreFunctor.id

instance : Inhabited (LaxPreFunctor B B) :=
  ⟨LaxPreFunctor.id B⟩

-- Porting note: `by exact` was not necessary in mathlib3
/-- Composition of prelax functors. -/
@[simps]
def comp (F : LaxPreFunctor B C) (G : LaxPreFunctor C D) : LaxPreFunctor B D :=
  { (F : Prefunctor B C).comp ↑G with map₂ := fun η => by exact G.map₂ (F.map₂ η) }
#align category_theory.prelax_functor.comp CategoryTheory.LaxPreFunctor.comp

end LaxPreFunctor

end

/-- A prelax functor between bicategories is a lax prefunctor such that `map₂` is a functor.
This structure will be extended to define `LaxFunctor` and `OplaxFunctor`.
-/
structure PrelaxFunctor (B: Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends LaxPreFunctor B C where
  /-- Prelax functors preserve identity 2-morphisms. -/
  map₂_id : ∀ {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop
  /-- Prelax functors preserve compositions. -/
  map₂_comp :
    ∀ {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    aesop_cat

namespace PrelaxFunctor

attribute [simp] map₂_id
attribute [reassoc (attr := simp)] map₂_comp

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

attribute [coe] CategoryTheory.LaxPreFunctor.toPrefunctor

instance hasCoeToLaxPreFunctor : Coe (PrelaxFunctor B C) (LaxPreFunctor B C) :=
  ⟨toLaxPreFunctor⟩

-- TODO: what simps to include here...?
/-- The identity prelax functor. -/
@[simps!]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : PrelaxFunctor B B where
  toLaxPreFunctor := LaxPreFunctor.id B

instance : Inhabited (LaxPreFunctor B B) :=
  ⟨LaxPreFunctor.id B⟩

variable (F : PrelaxFunctor B C)

/-- Composition of prelax functors. -/
@[simps!]
def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
  toLaxPreFunctor := LaxPreFunctor.comp F.toLaxPreFunctor G.toLaxPreFunctor

/-- Function between 1-morphisms as a functor. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η

section

variable {a b : B}

/-- An oplax functor `F : B ⥤ C` sends 2-isomorphisms `η : f ≅ f` to 2-isomorphisms
`F.map f ≅ F.map g` -/
@[simps!]
abbrev map₂Iso {f g : a ⟶ b} (η : f ≅ g) : F.map f ≅ F.map g :=
  (F.mapFunctor a b).mapIso η

instance map₂_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : IsIso (F.map₂ η) :=
  (F.map₂Iso (asIso η)).isIso_hom

@[simp]
lemma map₂_inv {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : F.map₂ (inv η) = inv (F.map₂ η) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]

@[reassoc]
lemma map₂_hom_inv {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ η ≫ F.map₂ (inv η) = 𝟙 (F.map f) := by
  simp

@[reassoc]
lemma map₂_inv_hom {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ (inv η) ≫ F.map₂ η = 𝟙 (F.map g) := by
  simp

end

end PrelaxFunctor
