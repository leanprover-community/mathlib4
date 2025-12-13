/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable (C : Type*) [Category C]

section

variable [CategoryWithCofibrations C] [HasInitial C]

def cofibrantObjects : ObjectProperty C := fun X ↦ IsCofibrant X

abbrev CofibrantObject : Type _ := (cofibrantObjects C).FullSubcategory

variable {C}

abbrev CofibrantObject.mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

abbrev CofibrantObject.homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := f

@[simp]
lemma CofibrantObject.homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma CofibrantObject.homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

abbrev CofibrantObject.ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι

instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end

section

variable [CategoryWithFibrations C] [HasTerminal C]

def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

abbrev FibrantObject : Type _ := (fibrantObjects C).FullSubcategory

variable {C}

abbrev FibrantObject.mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩

abbrev FibrantObject.homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := f

@[simp]
lemma FibrantObject.homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma FibrantObject.homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

abbrev FibrantObject.ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end

section

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

def bifibrantObjects : ObjectProperty C :=
    cofibrantObjects C ⊓ fibrantObjects C

lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C ≤ cofibrantObjects C := fun _ h ↦ h.1

lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C ≤ fibrantObjects C := fun _ h ↦ h.2

abbrev BifibrantObject : Type _ := (bifibrantObjects C).FullSubcategory

variable {C}

abbrev BifibrantObject.mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

abbrev BifibrantObject.homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := f

@[simp]
lemma BifibrantObject.homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
lemma BifibrantObject.homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

abbrev BifibrantObject.ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.1 := X.2.1
instance (X : BifibrantObject C) : IsFibrant X.1 := X.2.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.2.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.2.2

end

end HomotopicalAlgebra
