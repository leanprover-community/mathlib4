/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer

! This file was ported from Lean 3 source module category_theory.limits.lattice
! leanprover-community/mathlib commit c3019c79074b0619edb4b27553a91b2e82242395
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Data.Fintype.Lattice
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Limits in lattice categories are given by infimums and supremums.
-/


universe w u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.CompleteLattice

section Semilattice

variable {α : Type u}

variable {J : Type w} [SmallCategory J] [FinCategory J]

/-- The limit cone over any functor from a finite diagram into a `semilattice_inf` with `order_top`.
-/
def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F
    where
  Cone :=
    { pt := Finset.univ.inf F.obj
      π := { app := fun j => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  IsLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }
#align category_theory.limits.complete_lattice.finite_limit_cone CategoryTheory.Limits.CompleteLattice.finiteLimitCone

/--
The colimit cocone over any functor from a finite diagram into a `semilattice_sup` with `order_bot`.
-/
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F
    where
  Cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun i => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  IsColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }
#align category_theory.limits.complete_lattice.finite_colimit_cocone CategoryTheory.Limits.CompleteLattice.finiteColimitCocone

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => { HasLimit := fun F => has_limit.mk (finite_limit_cone F) }⟩
#align category_theory.limits.complete_lattice.has_finite_limits_of_semilattice_inf_order_top CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_orderTop

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α :=
  ⟨fun J 𝒥₁ 𝒥₂ => { HasColimit := fun F => has_colimit.mk (finite_colimit_cocone F) }⟩
#align category_theory.limits.complete_lattice.has_finite_colimits_of_semilattice_sup_order_bot CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSup_orderBot

/-- The limit of a functor from a finite diagram into a `semilattice_inf` with `order_top` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).IsLimit).to_eq
#align category_theory.limits.complete_lattice.finite_limit_eq_finset_univ_inf CategoryTheory.Limits.CompleteLattice.finite_limit_eq_finset_univ_inf

/-- The colimit of a functor from a finite diagram into a `semilattice_sup` with `order_bot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).IsColimit).to_eq
#align category_theory.limits.complete_lattice.finite_colimit_eq_finset_univ_sup CategoryTheory.Limits.CompleteLattice.finite_colimit_eq_finset_univ_sup

/--
A finite product in the category of a `semilattice_inf` with `order_top` is the same as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι → α) : (∏ f) = (Fintype.elems ι).inf f :=
  by
  trans
  exact
    (is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
        (finite_limit_cone (discrete.functor f)).IsLimit).to_eq
  change finset.univ.inf (f ∘ discrete_equiv.to_embedding) = (Fintype.elems ι).inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl
#align category_theory.limits.complete_lattice.finite_product_eq_finset_inf CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf

/-- A finite coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι → α) : (∐ f) = (Fintype.elems ι).sup f :=
  by
  trans
  exact
    (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
        (finite_colimit_cocone (discrete.functor f)).IsColimit).to_eq
  change finset.univ.sup (f ∘ discrete_equiv.to_embedding) = (Fintype.elems ι).sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl
#align category_theory.limits.complete_lattice.finite_coproduct_eq_finset_sup CategoryTheory.Limits.CompleteLattice.finite_coproduct_eq_finset_sup

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α :=
  by
  have : ∀ x y : α, has_limit (pair x y) :=
    by
    letI := hasFiniteLimits_of_hasFiniteLimits_of_size.{u} α
    infer_instance
  apply has_binary_products_of_has_limit_pair

/-- The binary product in the category of a `semilattice_inf` with `order_top` is the same as the
infimum.
-/
@[simp]
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
        _ =
        x ⊓ y :=
      by rw [inf_top_eq]
    
#align category_theory.limits.complete_lattice.prod_eq_inf CategoryTheory.Limits.CompleteLattice.prod_eq_inf

-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α :=
  by
  have : ∀ x y : α, has_colimit (pair x y) :=
    by
    letI := hasFiniteColimits_of_hasFiniteColimits_of_size.{u} α
    infer_instance
  apply has_binary_coproducts_of_has_colimit_pair

/-- The binary coproduct in the category of a `semilattice_sup` with `order_bot` is the same as the
supremum.
-/
@[simp]
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x y = x ⊔ y :=
  calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: finset.sup is realized as a fold, hence the definitional equality
        _ =
        x ⊔ y :=
      by rw [sup_bot_eq]
    
#align category_theory.limits.complete_lattice.coprod_eq_sup CategoryTheory.Limits.CompleteLattice.coprod_eq_sup

/-- The pullback in the category of a `semilattice_inf` with `order_top` is the same as the infimum
over the objects.
-/
@[simp]
theorem pullback_eq_inf [SemilatticeInf α] [OrderTop α] {x y z : α} (f : x ⟶ z) (g : y ⟶ z) :
    pullback f g = x ⊓ y :=
  calc
    pullback f g = limit (cospan f g) := rfl
    _ = Finset.univ.inf (cospan f g).obj := by rw [finite_limit_eq_finset_univ_inf]
    _ = z ⊓ (x ⊓ (y ⊓ ⊤)) := rfl
    _ = z ⊓ (x ⊓ y) := by rw [inf_top_eq]
    _ = x ⊓ y := inf_eq_right.mpr (inf_le_of_left_le f.le)
    
#align category_theory.limits.complete_lattice.pullback_eq_inf CategoryTheory.Limits.CompleteLattice.pullback_eq_inf

/-- The pushout in the category of a `semilattice_sup` with `order_bot` is the same as the supremum
over the objects.
-/
@[simp]
theorem pushout_eq_sup [SemilatticeSup α] [OrderBot α] (x y z : α) (f : z ⟶ x) (g : z ⟶ y) :
    pushout f g = x ⊔ y :=
  calc
    pushout f g = colimit (span f g) := rfl
    _ = Finset.univ.sup (span f g).obj := by rw [finite_colimit_eq_finset_univ_sup]
    _ = z ⊔ (x ⊔ (y ⊔ ⊥)) := rfl
    _ = z ⊔ (x ⊔ y) := by rw [sup_bot_eq]
    _ = x ⊔ y := sup_eq_right.mpr (le_sup_of_le_left f.le)
    
#align category_theory.limits.complete_lattice.pushout_eq_sup CategoryTheory.Limits.CompleteLattice.pushout_eq_sup

end Semilattice

variable {α : Type u} [CompleteLattice α]

variable {J : Type u} [SmallCategory J]

/-- The limit cone over any functor into a complete lattice.
-/
def limitCone (F : J ⥤ α) : LimitCone F
    where
  Cone :=
    { pt := infᵢ F.obj
      π := { app := fun j => homOfLE (CompleteLattice.inf_le _ _ (Set.mem_range_self _)) } }
  IsLimit :=
    {
      lift := fun s =>
        homOfLE (CompleteLattice.le_inf _ _ (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }
#align category_theory.limits.complete_lattice.limit_cone CategoryTheory.Limits.CompleteLattice.limitCone

/-- The colimit cocone over any functor into a complete lattice.
-/
def colimitCocone (F : J ⥤ α) : ColimitCocone F
    where
  Cocone :=
    { pt := supᵢ F.obj
      ι := { app := fun j => homOfLE (CompleteLattice.le_sup _ _ (Set.mem_range_self _)) } }
  IsColimit :=
    {
      desc := fun s =>
        homOfLE (CompleteLattice.sup_le _ _ (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }
#align category_theory.limits.complete_lattice.colimit_cocone CategoryTheory.Limits.CompleteLattice.colimitCocone

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
-- see Note [lower instance priority]
instance (priority := 100) hasLimits_of_completeLattice : HasLimits α
    where HasLimitsOfShape J 𝒥 := { HasLimit := fun F => has_limit.mk (limit_cone F) }
#align category_theory.limits.complete_lattice.has_limits_of_complete_lattice CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice

-- see Note [lower instance priority]
instance (priority := 100) hasColimits_of_completeLattice : HasColimits α
    where HasColimitsOfShape J 𝒥 := { HasColimit := fun F => has_colimit.mk (colimit_cocone F) }
#align category_theory.limits.complete_lattice.has_colimits_of_complete_lattice CategoryTheory.Limits.CompleteLattice.hasColimits_of_completeLattice

/-- The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
theorem limit_eq_infᵢ (F : J ⥤ α) : limit F = infᵢ F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).IsLimit).to_eq
#align category_theory.limits.complete_lattice.limit_eq_infi CategoryTheory.Limits.CompleteLattice.limit_eq_infᵢ

/-- The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
theorem colimit_eq_supᵢ (F : J ⥤ α) : colimit F = supᵢ F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).IsColimit).to_eq
#align category_theory.limits.complete_lattice.colimit_eq_supr CategoryTheory.Limits.CompleteLattice.colimit_eq_supᵢ

end CategoryTheory.Limits.CompleteLattice

