/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.biproducts
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Homology.ShortExact.Abelian

/-!
# The category of `R`-modules has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R]

-- As `Module R` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts (ModuleCat.{v} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts (ModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `Module R`, using `Module.of R (M × N)`.
-/
@[simps cone_x isLimit_lift]
def binaryProductLimitCone (M N : ModuleCat.{v} R) : Limits.LimitCone (pair M N)
    where
  Cone :=
    { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (LinearMap.fst R M N) (LinearMap.snd R M N)
          naturality' := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  IsLimit :=
    { lift := fun s => LinearMap.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x
            simp only [binary_fan.π_app_right, binary_fan.π_app_left, ModuleCat.coe_comp,
              Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.prod_apply,
              Pi.prod]
      uniq := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩];rw [← w ⟨walking_pair.right⟩]] <;> rfl }
#align Module.binary_product_limit_cone ModuleCat.binaryProductLimitCone

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.left⟩ = LinearMap.fst R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_left ModuleCat.binaryProductLimitCone_cone_π_app_left

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.right⟩ = LinearMap.snd R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_right ModuleCat.binaryProductLimitCone_cone_π_app_right

/-- We verify that the biproduct in `Module R` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) :
    (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).IsLimit
#align Module.biprod_iso_prod ModuleCat.biprodIsoProd

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

/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.pt ⟶ ModuleCat.of R (∀ j, f j)
    where
  toFun x j := s.π.app ⟨j⟩ x
  map_add' x y := by
    ext
    simp
  map_smul' r x := by
    ext
    simp
#align Module.has_limit.lift ModuleCat.HasLimit.lift

/-- Construct limit data for a product in `Module R`, using `Module.of R (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f)
    where
  Cone :=
    { pt := ModuleCat.of R (∀ j, f j)
      π := Discrete.natTrans fun j => (LinearMap.proj j.as : (∀ j, f j) →ₗ[R] f j.as) }
  IsLimit :=
    { lift := lift f
      fac := fun s j => by
        cases j
        ext
        simp
      uniq := fun s m w => by
        ext (x j)
        dsimp only [has_limit.lift]
        simp only [LinearMap.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }
#align Module.has_limit.product_limit_cone ModuleCat.HasLimit.productLimitCone

end HasLimit

open HasLimit

variable {J : Type} (f : J → ModuleCat.{v} R)

/-- We verify that the biproduct we've just defined is isomorphic to the `Module R` structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi [Fintype J] (f : J → ModuleCat.{v} R) :
    (⨁ f : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).IsLimit
#align Module.biproduct_iso_pi ModuleCat.biproductIsoPi

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π [Fintype J] (f : J → ModuleCat.{v} R) (j : J) :
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
of modules.-/
noncomputable def lequivProdOfRightSplitExact {f : B →ₗ[R] M} (hj : Function.Injective j)
    (exac : j.range = g.ker) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({             RightSplit := ⟨asHom f, h⟩
                  mono := (ModuleCat.mono_iff_injective <| asHom j).mpr hj
                  exact := (exact_iff _ _).mpr exac } : RightSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm
#align lequiv_prod_of_right_split_exact lequivProdOfRightSplitExact

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequivProdOfLeftSplitExact {f : M →ₗ[R] A} (hg : Function.Surjective g)
    (exac : j.range = g.ker) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({             LeftSplit := ⟨asHom f, h⟩
                  Epi := (ModuleCat.epi_iff_surjective <| asHom g).mpr hg
                  exact := (exact_iff _ _).mpr exac } : LeftSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm
#align lequiv_prod_of_left_split_exact lequivProdOfLeftSplitExact

end SplitExact

