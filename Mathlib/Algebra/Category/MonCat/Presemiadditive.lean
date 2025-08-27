/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Junyan Xu
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Preadditive.Semi

/-!
# The category of additive commutative monoids is pre-semiadditive.
-/

assert_not_exists Submonoid

open CategoryTheory

universe u

namespace AddCommMonCat

variable {M N : AddCommMonCat.{u}}

instance : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

lemma hom_add_apply {P Q : AddCommMonCat} (f g : P ⟶ Q) (x : P) : (f + g) x = f x + g x := rfl

instance : Zero (M ⟶ N) where
  zero := ofHom 0

@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance (P Q : AddCommMonCat) : AddCommMonoid (P ⟶ Q) :=
  Function.Injective.addCommMonoid Hom.hom ConcreteCategory.hom_injective
    rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance : Presemiadditive AddCommMonCat where

/-- `AddCommGrp.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (M →+ N) :=
  { ConcreteCategory.homEquiv (C := AddCommMonCat) with
    map_add' _ _ := rfl }

end AddCommMonCat
