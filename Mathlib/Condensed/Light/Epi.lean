/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.SequentialProduct
import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
import Mathlib.Condensed.Light.Limits
/-!

# Epimorphisms of light condensed objects

This file characterises epimorphisms in light condensed sets and modules as the locally surjective
morphisms. Here, the condition of locally surjective is phrased in terms of continuous surjections
of light profinite sets.

Further, we prove that the functor `lim : Discrete ℕ ⥤ LightCondMod R` preserves epimorphisms.
-/

universe v u w u' v'

open CategoryTheory Sheaf Limits HasForget GrothendieckTopology

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurjective f ↔
    ∀ (S : LightProfinite) (y : ToType (Y.val.obj ⟨S⟩)),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ)
        (x : ToType (X.val.obj ⟨S'⟩)),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R] {X Y : LightCondMod.{u} R} (f : X ⟶ Y)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : (LightCondensed.forget R).ReflectsEpimorphisms where
  reflects f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mpr hf

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : (LightCondensed.forget R).PreservesEpimorphisms where
  preserves f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mp hf

end LightCondMod

namespace LightCondensed

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
include hc hF in
lemma epi_π_app_zero_of_epi : Epi (c.π.app ⟨0⟩) := by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun x h ↦ Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit x) h
  · have := (freeForgetAdjunction R).isRightAdjoint
    exact isLimitOfPreserves _ hc
  · exact fun _ ↦ (forget R).map_epi _

end LightCondensed

open CategoryTheory.Limits.SequentialProduct

namespace LightCondensed

variable (n : ℕ)

attribute [local instance] functorMap_epi Abelian.hasFiniteBiproducts

variable {R : Type u} [Ring R] {M N : ℕ → LightCondMod.{u} R} (f : ∀ n, M n ⟶ N n) [∀ n, Epi (f n)]

instance : Epi (Limits.Pi.map f) := by
  have : Limits.Pi.map f = (cone f).π.app ⟨0⟩ := rfl
  rw [this]
  exact epi_π_app_zero_of_epi R (isLimit f) (fun n ↦ by simpa using by infer_instance)

instance : (lim (J := Discrete ℕ) (C := LightCondMod R)).PreservesEpimorphisms where
  preserves f _ := by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp only [lim_obj, lim_map, limMap, IsLimit.map, limit.isLimit_lift, limit.lift_π,
        Cones.postcompose_obj_pt, limit.cone_x, Cones.postcompose_obj_π, NatTrans.comp_app,
        Functor.const_obj_obj, limit.cone_π, Pi.isoLimit, Limits.Pi.map, Category.assoc,
        limit.conePointUniqueUpToIso_hom_comp, Pi.cone_pt, Pi.cone_π, Discrete.natTrans_app,
        Discrete.functor_obj_eq_as]
      erw [IsLimit.conePointUniqueUpToIso_inv_comp_assoc]
      rfl
    rw [this]
    infer_instance

end LightCondensed
