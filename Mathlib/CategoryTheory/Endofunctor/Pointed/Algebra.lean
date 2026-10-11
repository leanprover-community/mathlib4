/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Pointed (co)algebras for (co)pointed endofunctors

This file defines (co)algebras of a pointed endofunctor, as a full subcategory of the category
of all algebra.

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {F : C ⥤ C}

namespace Endofunctor.Algebra

/-- The object property `Endofunctor.Algebra.pointed σ` is satisfied by algebras
`A` such that `σ.app A.a ≫ A.str = 𝟙 A.a`, where `σ : 𝟭 C ⟶ F` is a "pointing" of `F`. -/
@[implicit_reducible]
def pointed (σ : 𝟭 C ⟶ F) : ObjectProperty (Endofunctor.Algebra F) := fun A ↦
  σ.app A.a ≫ A.str = 𝟙 A.a

/-- The category of pointed algebras for `σ : 𝟭 C ⟶ F` is the full subcategory of all
algebras `A` such that `σ.app A.a ≫ A.str = 𝟙 A.a`. -/
abbrev Pointed (σ : 𝟭 C ⟶ F) := (pointed σ).FullSubcategory

namespace Pointed

variable {σ : 𝟭 C ⟶ F}

@[simp, grind =] lemma prop (A : Pointed σ) : σ.app A.obj.a ≫ A.obj.str = 𝟙 A.obj.a := A.property

instance (priority := low) (A : Pointed σ) : IsSplitMono (σ.app A.obj.a) := .mk' ⟨A.obj.str, A.prop⟩

instance (priority := low) (A : Pointed σ) : IsSplitEpi (A.obj.str) := .mk' ⟨σ.app A.obj.a, A.prop⟩

variable (A : Pointed σ) in
variable (σ) in
/-- The (fully faithful) inclusion from pointed algebras in the category of all algebras. -/
abbrev ι : Pointed σ ⥤ Algebra F := ObjectProperty.ι ..

@[grind _=_]
lemma nat' {A B : Pointed σ} (f : A ⟶ B) :
    f.hom.f ≫ σ.app B.obj.a = σ.app A.obj.a ≫ F.map f.hom.f := by
  simp [← NatTrans.naturality]

end Pointed

end Endofunctor.Algebra

namespace Endofunctor.Coalgebra

/-- The object property `Endofunctor.Coalgebra.copointed σ` is satisfied by coalgebras
`A` such that `A.str ≫ σ.app A.V = 𝟙 A.V`, where `F ⟶ 𝟭 C` is a "copointing" of `F`. -/
@[implicit_reducible]
def copointed (σ : F ⟶ 𝟭 C) : ObjectProperty (Endofunctor.Coalgebra F) := fun A ↦
  A.str ≫ σ.app A.V = 𝟙 A.V

/-- The category of pointed algebras for `σ : 𝟭 C ⟶ F` is the full subcategory of all
algebras `A` such that `σ.app A.a ≫ A.str = 𝟙 A.a`. -/
abbrev Copointed (σ : F ⟶ 𝟭 C) := (copointed σ).FullSubcategory

namespace Copointed

variable {σ : F ⟶ 𝟭 C}

@[simp, grind =] lemma prop (A : Copointed σ) : A.obj.str ≫ σ.app A.obj.V = 𝟙 A.obj.V := A.property

instance (priority := low) (A : Copointed σ) : IsSplitEpi (σ.app A.obj.V) :=
  .mk' ⟨A.obj.str, A.prop⟩

instance (priority := low) (A : Copointed σ) : IsSplitMono (A.obj.str) :=
  .mk' ⟨σ.app A.obj.V, A.prop⟩

variable (A : Copointed σ) in
variable (σ) in
/-- The (fully faithful) inclusion from copointed coalgebras in the category of all algebras. -/
abbrev ι : Copointed σ ⥤ Coalgebra F := ObjectProperty.ι ..

@[grind _=_]
lemma nat' {A B : Copointed σ} (f : A ⟶ B) :
    F.map f.hom.f ≫ σ.app B.obj.V = σ.app A.obj.V ≫ f.hom.f := by
  simp

end Copointed

end Endofunctor.Coalgebra

end CategoryTheory

