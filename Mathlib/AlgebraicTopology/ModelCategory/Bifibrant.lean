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

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

variable (C) in
/-- The property that is satisfied by cofibrant objects.
(This is only introduced in order to consider the full subcategory
`CofibrantObject`. Otherwise, the typeclass `IsCofibrant`
is preferred.) -/
def cofibrantObjects : ObjectProperty C := IsCofibrant

variable (C) in
/-- The full subcategory of cofibrant objects. -/
abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

namespace CofibrantObject

/-- Constructor for `CofibrantObject C`. -/
abbrev mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

lemma mk_surjective (X : CofibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `CofibrantObject C`. -/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
lemma homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `CofibrantObject C ⥤ C`. -/
abbrev ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι

instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end CofibrantObject

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by fibrant objects.
(This is only introduced in order to consider the full subcategory
`FibrantObject`. Otherwise, the typeclass `IsFibrant`
is preferred.) -/
def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

variable (C) in
/-- The full subcategory of fibrant objects. -/
abbrev FibrantObject : Type u := (fibrantObjects C).FullSubcategory

namespace FibrantObject

/-- Constructor for `FibrantObject C`. -/
abbrev mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩

lemma mk_surjective (X : FibrantObject C) :
    ∃ (Y : C) (_ : IsFibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `FibrantObject C`. -/
abbrev homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
lemma homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `FibrantObject C ⥤ C`. -/
abbrev ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end FibrantObject

end Fibrant

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by bifibrant objects, i.e. objects
that are both cofibrant and fibrant.
(This is only introduced in order to consider the full subcategory
`BifibrantObject`. Otherwise, the typeclasses `IsCofibrant` and
`IsFibrant` are preferred.) -/
def bifibrantObjects : ObjectProperty C :=
  cofibrantObjects C ⊓ fibrantObjects C

variable (C) in
lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C ≤ cofibrantObjects C :=
  fun _ h ↦ h.1

variable (C) in
lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C ≤ fibrantObjects C :=
  fun _ h ↦ h.2

variable (C) in
/-- The full subcategory of bifibrant objects. -/
abbrev BifibrantObject : Type u := (bifibrantObjects C).FullSubcategory

namespace BifibrantObject

/-- Constructor for `BifibrantObject C`. -/
abbrev mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

lemma mk_surjective (X : BifibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y) (_ : IsFibrant Y), X = mk Y :=
  ⟨X.obj, X.property.1, X.property.2, rfl⟩

/-- Constructor for morphisms in `BifibrantObject C`. -/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
lemma homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `BifibrantObject C ⥤ C`. -/
abbrev ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.obj := X.property.1
instance (X : BifibrantObject C) : IsFibrant X.obj := X.property.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.property.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.property.2

end BifibrantObject

end Bifibrant

end HomotopicalAlgebra
