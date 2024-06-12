/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Finset.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

#align_import category_theory.limits.lattice from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

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

/-- The limit cone over any functor from a finite diagram into a `SemilatticeInf` with `OrderTop`.
-/
def finiteLimitCone [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := Finset.univ.inf F.obj
      π := { app := fun j => homOfLE (Finset.inf_le (Fintype.complete _)) } }
  isLimit := { lift := fun s => homOfLE (Finset.le_inf fun j _ => (s.π.app j).down.down) }
#align category_theory.limits.complete_lattice.finite_limit_cone CategoryTheory.Limits.CompleteLattice.finiteLimitCone

/--
The colimit cocone over any functor from a finite diagram into a `SemilatticeSup` with `OrderBot`.
-/
def finiteColimitCocone [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := Finset.univ.sup F.obj
      ι := { app := fun i => homOfLE (Finset.le_sup (Fintype.complete _)) } }
  isColimit := { desc := fun s => homOfLE (Finset.sup_le fun j _ => (s.ι.app j).down.down) }
#align category_theory.limits.complete_lattice.finite_colimit_cocone CategoryTheory.Limits.CompleteLattice.finiteColimitCocone

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteLimits_of_semilatticeInf_orderTop [SemilatticeInf α]
    [OrderTop α] : HasFiniteLimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩
#align category_theory.limits.complete_lattice.has_finite_limits_of_semilattice_inf_order_top CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_orderTop

-- see Note [lower instance priority]
instance (priority := 100) hasFiniteColimits_of_semilatticeSup_orderBot [SemilatticeSup α]
    [OrderBot α] : HasFiniteColimits α := ⟨by
  intro J 𝒥₁ 𝒥₂
  exact { has_colimit := fun F => HasColimit.mk (finiteColimitCocone F) }⟩
#align category_theory.limits.complete_lattice.has_finite_colimits_of_semilattice_sup_order_bot CategoryTheory.Limits.CompleteLattice.hasFiniteColimits_of_semilatticeSup_orderBot

/-- The limit of a functor from a finite diagram into a `SemilatticeInf` with `OrderTop` is the
infimum of the objects in the image.
-/
theorem finite_limit_eq_finset_univ_inf [SemilatticeInf α] [OrderTop α] (F : J ⥤ α) :
    limit F = Finset.univ.inf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (finiteLimitCone F).isLimit).to_eq
#align category_theory.limits.complete_lattice.finite_limit_eq_finset_univ_inf CategoryTheory.Limits.CompleteLattice.finite_limit_eq_finset_univ_inf

/-- The colimit of a functor from a finite diagram into a `SemilatticeSup` with `OrderBot`
is the supremum of the objects in the image.
-/
theorem finite_colimit_eq_finset_univ_sup [SemilatticeSup α] [OrderBot α] (F : J ⥤ α) :
    colimit F = Finset.univ.sup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (finiteColimitCocone F).isColimit).to_eq
#align category_theory.limits.complete_lattice.finite_colimit_eq_finset_univ_sup CategoryTheory.Limits.CompleteLattice.finite_colimit_eq_finset_univ_sup

/--
A finite product in the category of a `SemilatticeInf` with `OrderTop` is the same as the infimum.
-/
theorem finite_product_eq_finset_inf [SemilatticeInf α] [OrderTop α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∏ᶜ f = Fintype.elems.inf f := by
  trans
  · exact
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
          (finiteLimitCone (Discrete.functor f)).isLimit).to_eq
  change Finset.univ.inf (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.inf f
  simp only [← Finset.inf_map, Finset.univ_map_equiv_to_embedding]
  rfl
#align category_theory.limits.complete_lattice.finite_product_eq_finset_inf CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf

/-- A finite coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
theorem finite_coproduct_eq_finset_sup [SemilatticeSup α] [OrderBot α] {ι : Type u} [Fintype ι]
    (f : ι → α) : ∐ f = Fintype.elems.sup f := by
  trans
  · exact
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (finiteColimitCocone (Discrete.functor f)).isColimit).to_eq
  change Finset.univ.sup (f ∘ discreteEquiv.toEmbedding) = Fintype.elems.sup f
  simp only [← Finset.sup_map, Finset.univ_map_equiv_to_embedding]
  rfl
#align category_theory.limits.complete_lattice.finite_coproduct_eq_finset_sup CategoryTheory.Limits.CompleteLattice.finite_coproduct_eq_finset_sup

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeInf α] [OrderTop α] : HasBinaryProducts α := by
  have : ∀ x y : α, HasLimit (pair x y) := by
    letI := hasFiniteLimits_of_hasFiniteLimits_of_size.{u} α
    infer_instance
  apply hasBinaryProducts_of_hasLimit_pair

/-- The binary product in the category of a `SemilatticeInf` with `OrderTop` is the same as the
infimum.
-/
@[simp]
theorem prod_eq_inf [SemilatticeInf α] [OrderTop α] (x y : α) : Limits.prod x y = x ⊓ y :=
  calc
    Limits.prod x y = limit (pair x y) := rfl
    _ = Finset.univ.inf (pair x y).obj := by rw [finite_limit_eq_finset_univ_inf (pair.{u} x y)]
    _ = x ⊓ (y ⊓ ⊤) := rfl
    -- Note: finset.inf is realized as a fold, hence the definitional equality
    _ = x ⊓ y := by rw [inf_top_eq]
#align category_theory.limits.complete_lattice.prod_eq_inf CategoryTheory.Limits.CompleteLattice.prod_eq_inf

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
-- see Note [lower instance priority]
instance (priority := 100) [SemilatticeSup α] [OrderBot α] : HasBinaryCoproducts α := by
  have : ∀ x y : α, HasColimit (pair x y) := by
    letI := hasFiniteColimits_of_hasFiniteColimits_of_size.{u} α
    infer_instance
  apply hasBinaryCoproducts_of_hasColimit_pair

/-- The binary coproduct in the category of a `SemilatticeSup` with `OrderBot` is the same as the
supremum.
-/
@[simp]
theorem coprod_eq_sup [SemilatticeSup α] [OrderBot α] (x y : α) : Limits.coprod x y = x ⊔ y :=
  calc
    Limits.coprod x y = colimit (pair x y) := rfl
    _ = Finset.univ.sup (pair x y).obj := by rw [finite_colimit_eq_finset_univ_sup (pair x y)]
    _ = x ⊔ (y ⊔ ⊥) := rfl
    -- Note: Finset.sup is realized as a fold, hence the definitional equality
    _ = x ⊔ y := by rw [sup_bot_eq]
#align category_theory.limits.complete_lattice.coprod_eq_sup CategoryTheory.Limits.CompleteLattice.coprod_eq_sup

/-- The pullback in the category of a `SemilatticeInf` with `OrderTop` is the same as the infimum
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

/-- The pushout in the category of a `SemilatticeSup` with `OrderBot` is the same as the supremum
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
def limitCone (F : J ⥤ α) : LimitCone F where
  cone :=
    { pt := iInf F.obj
      π := { app := fun j => homOfLE (CompleteLattice.sInf_le _ _ (Set.mem_range_self _)) } }
  isLimit :=
    { lift := fun s =>
        homOfLE (CompleteLattice.le_sInf _ _ (by rintro _ ⟨j, rfl⟩; exact (s.π.app j).le)) }
#align category_theory.limits.complete_lattice.limit_cone CategoryTheory.Limits.CompleteLattice.limitCone

/-- The colimit cocone over any functor into a complete lattice.
-/
def colimitCocone (F : J ⥤ α) : ColimitCocone F where
  cocone :=
    { pt := iSup F.obj
      ι := { app := fun j => homOfLE (CompleteLattice.le_sSup _ _ (Set.mem_range_self _)) } }
  isColimit :=
    { desc := fun s =>
        homOfLE (CompleteLattice.sSup_le _ _ (by rintro _ ⟨j, rfl⟩; exact (s.ι.app j).le)) }
#align category_theory.limits.complete_lattice.colimit_cocone CategoryTheory.Limits.CompleteLattice.colimitCocone

-- It would be nice to only use the `Inf` half of the complete lattice, but
-- this seems not to have been described separately.
-- see Note [lower instance priority]
instance (priority := 100) hasLimits_of_completeLattice : HasLimits α where
  has_limits_of_shape _ := { has_limit := fun F => HasLimit.mk (limitCone F) }
#align category_theory.limits.complete_lattice.has_limits_of_complete_lattice CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice

-- see Note [lower instance priority]
instance (priority := 100) hasColimits_of_completeLattice : HasColimits α where
  has_colimits_of_shape _ := { has_colimit := fun F => HasColimit.mk (colimitCocone F) }
#align category_theory.limits.complete_lattice.has_colimits_of_complete_lattice CategoryTheory.Limits.CompleteLattice.hasColimits_of_completeLattice

/-- The limit of a functor into a complete lattice is the infimum of the objects in the image.
-/
theorem limit_eq_iInf (F : J ⥤ α) : limit F = iInf F.obj :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit F) (limitCone F).isLimit).to_eq
#align category_theory.limits.complete_lattice.limit_eq_infi CategoryTheory.Limits.CompleteLattice.limit_eq_iInf

/-- The colimit of a functor into a complete lattice is the supremum of the objects in the image.
-/
theorem colimit_eq_iSup (F : J ⥤ α) : colimit F = iSup F.obj :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCocone F).isColimit).to_eq
#align category_theory.limits.complete_lattice.colimit_eq_supr CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup

end CategoryTheory.Limits.CompleteLattice
