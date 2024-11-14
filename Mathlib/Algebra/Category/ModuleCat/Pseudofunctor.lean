/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The pseudofunctors which send a commutative ring to its category of modules

In this file, we construct the pseudofunctors
`CommRingCat.moduleCatRestrictScalarsPseudofunctor` and
`RingCat.moduleCatRestrictScalarsPseudofunctor` which sends a (commutative) ring
to its category of modules: the contravariant functoriality is given
by the restriction of scalars functors.

We also define a pseudofunctor
`CommRingCat.moduleCatExtendScalarsPseudofunctor`: the covariant functoriality
is given by the extension of scalars functors.

-/

universe v u

open CategoryTheory ModuleCat

/-- The pseudofunctor from `LocallyDiscrete CommRingCatᵒᵖ` to `Cat` which sends
a commutative ring `R` to its category of modules. The functoriality is given by
the restriction of scalars. -/
@[simps! obj map mapId mapComp]
noncomputable def CommRingCat.moduleCatRestrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{v} R.unop))
    (fun f ↦ restrictScalars f.unop)
    (fun R ↦ restrictScalarsId R.unop)
    (fun f g ↦ restrictScalarsComp g.unop f.unop)

/-- The pseudofunctor from `LocallyDiscrete RingCatᵒᵖ` to `Cat` which sends a ring `R`
to its category of modules. The functoriality is given by the restriction of scalars. -/
@[simps! obj map mapId mapComp]
noncomputable def RingCat.moduleCatRestrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{v} R.unop))
    (fun f ↦ restrictScalars f.unop)
    (fun R ↦ restrictScalarsId R.unop)
    (fun f g ↦ restrictScalarsComp g.unop f.unop)

namespace ModuleCat
-- to be moved to ChangeOfRings
section

@[ext]
lemma extendScalars_hom_ext {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} {M : ModuleCat R} {N : ModuleCat S}
    {α β : (extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M), α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β := by
  letI := f.toAlgebra
  apply (restrictScalars f).map_injective
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s ⊗ₜ m) = β (s ⊗ₜ m)
  have : (s : S) ⊗ₜ[R] (m : M) = s • (1 : S) ⊗ₜ[R] m := by
    rw [ExtendScalars.smul_tmul, mul_one]
  simp only [this, map_smul, h]

end

section

variable (R : Type u) [CommRing R]

/-- The extension of scalars by the identity of a ring is isomorphic to the
identity functor. -/
noncomputable def extendScalarsId : extendScalars (RingHom.id R) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id).symm
    (restrictScalarsId R)).symm

variable {R}

lemma extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M):
    (extendScalarsId R).inv.app M m = (1 : R) ⊗ₜ m := rfl

lemma homEquiv_extendScalarsId (M : ModuleCat R) :
    (extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((extendScalarsId R).hom.app M) =
      (restrictScalarsId R).inv.app M := by
  ext m
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  rw [← extendScalarsId_inv_app_apply]
  erw [← comp_apply]
  simp

lemma extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    ((extendScalarsId R).hom.app M) ((1 : R) ⊗ₜ m) = m := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply,
    homEquiv_extendScalarsId]
  dsimp

end

section

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃)

/-- The extension of scalars by a composition of commutative ring morphisms
identify to the composition of the extension of scalars functors. -/
noncomputable def extendScalarsComp :
    extendScalars (g.comp f) ≅ extendScalars f ⋙ extendScalars g :=
  (conjugateIsoEquiv
    ((extendRestrictScalarsAdj f).comp (extendRestrictScalarsAdj g))
    (extendRestrictScalarsAdj (g.comp f))).symm (restrictScalarsComp f g).symm

lemma homEquiv_extendScalarsComp (M : ModuleCat R₁) :
    (extendRestrictScalarsAdj (g.comp f)).homEquiv _ _ ((extendScalarsComp f g).hom.app M) =
      (extendRestrictScalarsAdj f).unit.app M ≫
        (restrictScalars f).map ((extendRestrictScalarsAdj g).unit.app _) ≫
        (restrictScalarsComp f g).inv.app _ := by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Category.assoc, Category.id_comp, Category.comp_id,
    Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

lemma extendScalarsComp_hom_app_one_tmul (M : ModuleCat R₁) (m : M) :
    ((extendScalarsComp f g).hom.app M) ((1 : R₃) ⊗ₜ m) =
        by exact (1 : R₃) ⊗ₜ ((1 : R₂) ⊗ₜ m) := by
  rw [← extendRestrictScalarsAdj_homEquiv_apply, homEquiv_extendScalarsComp]
  rfl

end

section

variable {R₀ R₁ R₂ R₃ : Type u} [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f : R₀ →+* R₁) (g : R₁ →+* R₂) (h : R₂ →+* R₃)

@[reassoc]
lemma extendScalars_assoc :
    (extendScalarsComp (g.comp f) h).hom ≫ whiskerRight (extendScalarsComp f g).hom _ =
      (extendScalarsComp f (h.comp g)).hom ≫ whiskerLeft _ (extendScalarsComp g h).hom ≫
        (Functor.associator _ _ _).inv := by
  ext M m
  dsimp
  have := extendScalarsComp_hom_app_one_tmul (g.comp f) h M m
  erw [this, extendScalarsComp_hom_app_one_tmul f (h.comp g) M m,
    extendScalarsComp_hom_app_one_tmul g h, ExtendScalars.map_tmul,
    extendScalarsComp_hom_app_one_tmul f g]

/-- The associativity compatibility for the extension of scalars, in the exact form
that is needed in the definition `ModuleCat.extendScalarsPseudofunctor`. -/
lemma extendScalars_assoc' :
    (extendScalarsComp (g.comp f) h).hom ≫ whiskerRight (extendScalarsComp f g).hom _ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft _ (extendScalarsComp g h).inv ≫
        (extendScalarsComp f (h.comp g)).inv = 𝟙 _ := by
  rw [extendScalars_assoc_assoc]
  simp only [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
    whiskerLeft_id', Category.id_comp]

@[reassoc]
lemma extendScalars_id_comp :
    (extendScalarsComp (RingHom.id R₀) f).hom ≫ whiskerRight (extendScalarsId R₀).hom _ ≫
      (Functor.leftUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul (RingHom.id R₀) f M m]
  rw [ExtendScalars.map_tmul]
  erw [extendScalarsId_hom_app_one_tmul]
  rfl

@[reassoc]
lemma extendScalars_comp_id :
    (extendScalarsComp f (RingHom.id R₁)).hom ≫ whiskerLeft _ (extendScalarsId R₁).hom ≫
      (Functor.rightUnitor _).hom = 𝟙 _ := by
  ext M m
  dsimp
  erw [extendScalarsComp_hom_app_one_tmul f (RingHom.id R₁) M m,
    extendScalarsId_hom_app_one_tmul]
  rfl

end

end ModuleCat

/-- The pseudofunctor from `LocallyDiscrete CommRingCat` to `Cat` which sends
a commutative ring `R` to its category of modules. The functoriality is given by
the extension of scalars. -/
@[simps! obj map mapId mapComp]
noncomputable def CommRingCat.moduleCatExtendScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{u} R))
    (fun f ↦ extendScalars f)
    (fun R ↦ extendScalarsId R)
    (fun f g ↦ extendScalarsComp f g)
    (fun _ _ _ ↦ extendScalars_assoc' _ _ _)
    (fun _ ↦ extendScalars_id_comp _)
    (fun _ ↦ extendScalars_comp_id _)
