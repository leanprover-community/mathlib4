import Mathlib.CategoryTheory.GaloisCategories.Topology
import Mathlib.CategoryTheory.GaloisCategories.Prorepresantability
import Mathlib.Data.Rel

universe u v w

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{u})
  [PreGaloisCategory C] [FibreFunctor F]

instance : EssSurj (H F) := EssSurj.mk <| by
  intro Y
  admit
