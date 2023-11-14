import Mathlib.CategoryTheory.Limits.Types

universe u v w

open CategoryTheory Limits Functor

variable {C : Type u} {J : Type w} [Category.{v, u} C] [Category J]

def diagProcoyoneda' (diag : J ⥤ C) (X : C) : J ⥤ Type v where
  obj j := diag.obj j ⟶ X

def diagProcoyoneda (diag : J ⥤ C) : C ⥤ (J ⥤ Type w) where
  obj X := diagProcoyoneda' diag X

def procoyoneda (diag : J ⥤ C) : C ⥤ Type v where
  obj X := colimit (diagProcoyoneda.obj X)

class Procorepresentable (F : C ⥤ Type v) : Prop where
  has_procorepresentation : ∃ (X : J ⥤ C), procoyoneda X ≅ F

--def proyoneda : (J ⥤ C) ⥤ (Cᵒᵖ ⥤ Type v) := sorry
--
--def procoyoneda : (J ⥤ C)ᵒᵖ ⥤ (C ⥤ Type v) := sorry
