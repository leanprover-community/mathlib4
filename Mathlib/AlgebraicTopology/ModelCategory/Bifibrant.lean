/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

In this file, we introduce the full subcategories `CofibrantObject C`,
`FibrantObject C` and `BifibrantObject C` of a model category `C` which
respectively consist of cofibrant objects, fibrant objects,
and bifibrant objects, where "bifibrant" means both cofibrant and fibrant.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

/-- The property that is satisfied by cofibrant objects. -/
def cofibrantObjects : ObjectProperty C := IsCofibrant

/-- The full subcategory of cofibrant objects. -/
abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

variable {C}

/-- Constructor for `CofibrantObject C`. -/
abbrev CofibrantObject.mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

lemma CofibrantObject.mk_surjective (X : CofibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `CofibrantObject C`. -/
abbrev CofibrantObject.homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma CofibrantObject.homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma CofibrantObject.weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
lemma CofibrantObject.homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma CofibrantObject.homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `CofibrantObject C ⥤ C`. -/
abbrev CofibrantObject.ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι

instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

/-- The property that is satisfied by fibrant objects. -/
def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

/-- The full subcategory of fibrant objects. -/
abbrev FibrantObject : Type u := (fibrantObjects C).FullSubcategory

variable {C}

/-- Constructor for `FibrantObject C`. -/
abbrev FibrantObject.mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩

lemma FibrantObject.mk_surjective (X : FibrantObject C) :
    ∃ (Y : C) (_ : IsFibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `FibrantObject C`. -/
abbrev FibrantObject.homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma FibrantObject.homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma FibrantObject.weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
lemma FibrantObject.homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma FibrantObject.homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `FibrantObject C ⥤ C`. -/
abbrev FibrantObject.ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end Fibrant

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

/-- The property that is satisfied by bifibrant objects, i.e. objects
that are both cofibrant and fibrant. -/
def bifibrantObjects : ObjectProperty C :=
    cofibrantObjects C ⊓ fibrantObjects C

lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C ≤ cofibrantObjects C :=
  fun _ h ↦ h.1

lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C ≤ fibrantObjects C :=
  fun _ h ↦ h.2

/-- The full subcategory of bifibrant objects. -/
abbrev BifibrantObject : Type u := (bifibrantObjects C).FullSubcategory

variable {C}

/-- Constructor for `BifibrantObject C`. -/
abbrev BifibrantObject.mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

lemma BifibrantObject.mk_surjective (X : BifibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y) (_ : IsFibrant Y), X = mk Y :=
  ⟨X.obj, X.property.1, X.property.2, rfl⟩

/-- Constructor for morphisms in `BifibrantObject C`. -/
abbrev BifibrantObject.homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma BifibrantObject.homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma BifibrantObject.homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma BifibrantObject.homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `BifibrantObject C ⥤ C`. -/
abbrev BifibrantObject.ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.obj := X.property.1
instance (X : BifibrantObject C) : IsFibrant X.obj := X.property.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.property.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.property.2

end Bifibrant

end HomotopicalAlgebra
