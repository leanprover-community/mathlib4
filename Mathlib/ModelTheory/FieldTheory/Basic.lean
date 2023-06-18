import Mathlib.ModelTheory.Syntax
import Mathlib.Tactic.DeriveFintype

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

protected def field : Language :=
Language.mk₂ Bool Bool Bool Empty Empty

namespace field

instance : Zero Language.field.Constants := ⟨false⟩

instance : One Language.field.Constants := ⟨true⟩

def addFunction : Language.field.Functions 2 := false

def mulFunction : Language.field.Functions 2 := true

def negFunction : Language.field.Functions 1 := false

def invFunction : Language.field.Functions 1 := true

instance (α : Type _) : Zero (Language.field.Term α) :=
{ zero := Constants.term 0 }

instance (α : Type _) : One (Language.field.Term α) :=
{ one := Constants.term 1 }

instance (α : Type _) : Add (Language.field.Term α) :=
{ add := addFunction.apply₂ }

instance (α : Type _) : Mul (Language.field.Term α) :=
{ mul := mulFunction.apply₂ }

instance (α : Type _) : Neg (Language.field.Term α) :=
{ neg := negFunction.apply₁ }

instance (α : Type _) : Inv (Language.field.Term α) :=
{ inv := invFunction.apply₁ }

open BoundedFormula

def Theory.field : Language.field.Theory :=
{all $ all $ all (equal () _) }

end field

end Language

end FirstOrder
