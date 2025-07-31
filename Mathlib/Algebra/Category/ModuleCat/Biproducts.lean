/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The category of `R`-modules has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

universe w v u

namespace ModuleCat

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
              WalkingPair.casesOn j (ofHom <| LinearMap.fst R M N) (ofHom <| LinearMap.snd R M N)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun s => ofHom <| LinearMap.prod
        (s.π.app ⟨WalkingPair.left⟩).hom
        (s.π.app ⟨WalkingPair.right⟩).hom
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> rfl
      uniq := fun s m w => by
        simp_rw [← w ⟨WalkingPair.left⟩, ← w ⟨WalkingPair.right⟩]
        rfl }

@[simp]
theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.left⟩ = ofHom (LinearMap.fst R M N) :=
  rfl

@[simp]
theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.right⟩ = ofHom (LinearMap.snd R M N) :=
  rfl

/-- We verify that the biproduct in `ModuleCat R` is isomorphic to
the cartesian product of the underlying types:
-/
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) :
    (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (LinearMap.fst R M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (LinearMap.snd R M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J → ModuleCat.{max w v} R)

/-- The map from an arbitrary cone over an indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps!]
def lift (s : Fan f) : s.pt ⟶ ModuleCat.of R (∀ j, f j) :=
  ofHom
  { toFun := fun x j => s.π.app ⟨j⟩ x
    map_add' := fun x y => by
      simp only [Functor.const_obj_obj, map_add]
      rfl
    map_smul' := fun r x => by
      simp only [Functor.const_obj_obj, map_smul]
      rfl }

/-- Construct limit data for a product in `ModuleCat R`, using `ModuleCat.of R (∀ j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := ModuleCat.of R (∀ j, f j)
      π := Discrete.natTrans fun j => ofHom (LinearMap.proj j.as : (∀ j, f j) →ₗ[R] f j.as) }
  isLimit :=
    { lift := lift.{_, v} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt → f j) x) (w ⟨j⟩) }

end HasLimit

open HasLimit

variable {J : Type} (f : J → ModuleCat.{v} R)

/-- We verify that the biproduct we've just defined is isomorphic to the `ModuleCat R` structure
on the dependent function type.
-/
noncomputable def biproductIsoPi [Finite J] (f : J → ModuleCat.{v} R) :
    ((⨁ f) : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π [Finite J] (f : J → ModuleCat.{v} R) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end ModuleCat

section SplitExact
open ModuleCat
section universe_monomorphic

variable {R : Type u} {A M B : Type v} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup M] [Module R M]

variable {j : A →ₗ[R] M} {g : M →ₗ[R] B}


private noncomputable def lequivProdOfRightSplitExact' {f : B →ₗ[R] M} (hj : Function.Injective j)
    (exac : LinearMap.range j = LinearMap.ker g) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfSection _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.mono_iff_injective])).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _ ).symm.toLinearEquiv

private noncomputable def lequivProdOfLeftSplitExact' {f : M →ₗ[R] A} (hg : Function.Surjective g)
    (exac : LinearMap.range j = LinearMap.ker g) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ModuleCat.ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.epi_iff_surjective] using hg)).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv

end universe_monomorphic

section universe_polymorphic

universe uA uM uB
variable {R : Type u} {A : Type uA} {M : Type uM} {B : Type uB}
variable [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
variable [Module R A] [Module R B] [Module R M]

variable {j : A →ₗ[R] M} {g : M →ₗ[R] B}

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules. -/
noncomputable def lequivProdOfRightSplitExact {f : B →ₗ[R] M} (hj : Function.Injective j)
    (exac : LinearMap.range j = LinearMap.ker g) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  have := lequivProdOfRightSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
    (g := ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)
    (by simpa using hj)
    (by simp [LinearMap.range_comp, LinearMap.ker_comp, exac, Submodule.comap_equiv_eq_map_symm])
    (by ext x; simpa using congr($h x.down))
  ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm ≪≫ₗ this ≪≫ₗ ULift.moduleEquiv

/-- The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules. -/
noncomputable def lequivProdOfLeftSplitExact {f : M →ₗ[R] A} (hg : Function.Surjective g)
    (exac : LinearMap.range j = LinearMap.ker g) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  have := lequivProdOfLeftSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
    (g := ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)
    (by simpa using hg)
    (by simp [LinearMap.range_comp, LinearMap.ker_comp, exac, Submodule.comap_equiv_eq_map_symm])
    (by ext x; simpa using congr($h x.down))
  ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm ≪≫ₗ this ≪≫ₗ ULift.moduleEquiv

end universe_polymorphic

end SplitExact
