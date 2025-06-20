/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

-/

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

abbrev FibrantObject.ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end

section

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

def bifibrantObjects : ObjectProperty C :=
    cofibrantObjects C ⊓ fibrantObjects C

abbrev BifibrantObject : Type _ := (bifibrantObjects C).FullSubcategory

variable {C}

abbrev BifibrantObject.mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

abbrev BifibrantObject.ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.1 := X.2.1
instance (X : BifibrantObject C) : IsFibrant X.1 := X.2.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.2.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.2.2

end

end HomotopicalAlgebra
