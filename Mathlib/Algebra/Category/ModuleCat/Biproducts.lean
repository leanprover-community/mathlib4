/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

#align_import algebra.category.Module.biproducts from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# The category of `R`-modules has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

universe w v u

namespace ModuleCat
set_option linter.uppercaseLean3 false -- `Module`

variable {R : Type u} [Ring R]

-- As `ModuleCat R` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts (ModuleCat.{v} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts (ModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `ModuleCat R`, using `ModuleCat.of R (M × N)`.
-/
@[simps cone_pt isLimit_lift]
def binaryProductLimitCone (M N : ModuleCat.{v} R) : Limits.LimitCone (pair M N) where
  cone :=
    { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (LinearMap.fst R M N) (LinearMap.snd R M N)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun s => LinearMap.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> rfl
      uniq := fun s m w => by
        simp_rw [← w ⟨WalkingPair.left⟩, ← w ⟨WalkingPair.right⟩]
        rfl }
#align Module.binary_product_limit_cone ModuleCat.binaryProductLimitCone

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.left⟩ = LinearMap.fst R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_left ModuleCat.binaryProductLimitCone_cone_π_app_left

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.right⟩ = LinearMap.snd R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_right ModuleCat.binaryProductLimitCone_cone_π_app_right

/-- We verify that the biproduct in `ModuleCat R` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps! hom_apply]
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) :
    (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit
#align Module.biprod_iso_prod ModuleCat.biprodIsoProd

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] ModuleCat.biprodIsoProd_hom_apply

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.fst = LinearMap.fst R M N :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
#align Module.biprod_iso_prod_inv_comp_fst ModuleCat.biprodIsoProd_inv_comp_fst

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.snd = LinearMap.snd R M N :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
#align Module.biprod_iso_prod_inv_comp_snd ModuleCat.biprodIsoProd_inv_comp_snd

namespace HasLimit

variable {J : Type w} (f : J → ModuleCat.{max w v} R)

/-- The map from an arbitrary cone over an indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.pt ⟶ ModuleCat.of R (∀ j, f j) where
  toFun x j := s.π.app ⟨j⟩ x
  map_add' x y := by
    simp only [Functor.const_obj_obj, map_add]
    rfl
  map_smul' r x := by
    simp only [Functor.const_obj_obj, map_smul]
    rfl
#align Module.has_limit.lift ModuleCat.HasLimit.lift

/-- Construct limit data for a product in `ModuleCat R`, using `ModuleCat.of R (∀ j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := ModuleCat.of R (∀ j, f j)
      π := Discrete.natTrans fun j => (LinearMap.proj j.as : (∀ j, f j) →ₗ[R] f j.as) }
  isLimit :=
    { lift := lift.{_, v} f
      fac := fun s j => rfl
      uniq := fun s m w => by
        ext x
        funext j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt → f j) x) (w ⟨j⟩) }
#align Module.has_limit.product_limit_cone ModuleCat.HasLimit.productLimitCone

end HasLimit

open HasLimit

variable {J : Type} (f : J → ModuleCat.{v} R)

/-- We verify that the biproduct we've just defined is isomorphic to the `ModuleCat R` structure
on the dependent function type.
-/
@[simps! hom_apply]
noncomputable def biproductIsoPi [Finite J] (f : J → ModuleCat.{v} R) :
    ((⨁ f) : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit
#align Module.biproduct_iso_pi ModuleCat.biproductIsoPi

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] ModuleCat.biproductIsoPi_hom_apply

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π [Finite J] (f : J → ModuleCat.{v} R) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
#align Module.biproduct_iso_pi_inv_comp_π ModuleCat.biproductIsoPi_inv_comp_π

end ModuleCat

section SplitExact

variable {R : Type u} {A M B : Type v} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup M] [Module R M]

variable {j : A →ₗ[R] M} {g : M →ₗ[R] B}

open ModuleCat


/-- The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules. -/
noncomputable def lequivProdOfRightSplitExact {f : B →ₗ[R] M} (hj : Function.Injective j)
    (exac : LinearMap.range j = LinearMap.ker g) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfSection _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (asHom f) h
    (by simpa only [ModuleCat.mono_iff_injective])).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _ ).symm.toLinearEquiv

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules. -/
noncomputable def lequivProdOfLeftSplitExact {f : M →ₗ[R] A} (hg : Function.Surjective g)
    (exac : LinearMap.range j = LinearMap.ker g) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ModuleCat.ofHom f) h
    (by simpa only [ModuleCat.epi_iff_surjective] using hg)).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv
#align lequiv_prod_of_left_split_exact lequivProdOfLeftSplitExact

end SplitExact
