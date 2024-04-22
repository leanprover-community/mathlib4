import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.EqToHom

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (F : Pseudofunctor B C)

lemma map₂_eqToHom {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, map₂_id]
