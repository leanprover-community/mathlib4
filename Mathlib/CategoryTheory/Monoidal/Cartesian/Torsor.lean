/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Torsors in a cartesian monoidal category

A module object `X` over a monoid object `M` is a torsor for the topology
`J` if `M` acts simply transitively on `X` and `locally `X` is trivial on some `J`-cover.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M : C} [MonObj M] {X Y : C} [ModObj M Y] [ModObj M X]
  {G : C} [GrpObj G] [ModObj G X]

attribute [local instance] ModObj.regular

open Limits

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

variable (J : GrothendieckTopology C)

/-- A homogeneous module object is trivial over `U : C`, if there exists a morphism `U ⟶ X ⊗ U`. -/
@[mk_iff]
class IsTrivialOver (M : C) [MonObj M] (X : C) [ModObj M X] (U : C) [IsHomogeneous M X] where
  nonempty_hom : Nonempty (U ⟶ X)

lemma isTrivialOver_iff_isSplitEpi [IsHomogeneous M X] (U : C) :
    IsTrivialOver M X U ↔ IsSplitEpi (snd X U) :=
  ⟨fun h ↦ ⟨⟨⟨lift h.nonempty_hom.some (𝟙 _), by simp⟩⟩⟩, fun ⟨h⟩ ↦ ⟨⟨h.some.section_ ≫ fst _ _⟩⟩⟩

variable (M X) in
/-- A module object `X` over a monoid object `M` is a torsor for the Grothendieck topology `J`,
if `M` acts simply transitively on `X` and there exists a `J`-covering that trivializes `X`. -/
class IsTorsor (J : GrothendieckTopology C) (M : C) [MonObj M] (X : C) [ModObj M X] where
  isHomogeneous : IsHomogeneous M X := by infer_instance
  exists_coversTop : ∃ (I : Type max u v) (U : I → C),
    J.CoversTop U ∧ ∀ (i : I), IsTrivialOver M X (U i)

namespace IsTorsor

instance : IsTorsor J G G where
  exists_coversTop := by
    refine ⟨PUnit, fun _ ↦ 𝟙_ _, ?_, ?_⟩
    · rw [J.coversTop_iff_of_isTerminal _ isTerminalTensorUnit,
        Sieve.pullback_ofObjects_eq_top (i := ⟨⟩) _ (𝟙 _)]
      simp
    · simp only [isTrivialOver_iff, forall_const]
      exact ⟨η⟩

end IsTorsor

variable (M) in
/-- A morphism `s : U ⟶ X` trivializes a homogeneous module object over `U`, i.e.,
`X ⊗ U` is isomorphic to `M ⊗ U`.
This corresponds to `X` being the trivial torsor when restricted to `Over U`. -/
noncomputable
def isoTensorOfHom {U : C} (s : U ⟶ X) [IsHomogeneous M X] : M ⊗ U ≅ X ⊗ U where
  hom := lift (𝟙 _ ⊗ₘ s) (snd _ _) ≫ γ[M, X] ▷ U
  inv := lift (𝟙 _ ⊗ₘ s) (snd _ _) ≫ inv (leftSMul M X) ▷ U ≫ fst _ _ ▷ U
  hom_inv_id := by
    have : (lift (𝟙 M ⊗ₘ s) (snd M U) ≫ γ[M, X] ▷ U) ≫ lift (𝟙 X ⊗ₘ s) (snd X U) =
        lift (𝟙 M ⊗ₘ s) (snd _ _) ≫ leftSMul M X ▷ U := by
      ext <;> simp
    rw [Category.assoc, reassoc_of% this]
    simp
  inv_hom_id := by
    have h1 :
        lift (𝟙 X ⊗ₘ s) (snd X U) ≫ inv (leftSMul M X) ▷ U ≫ fst M X ▷ U ≫
          lift (𝟙 M ⊗ₘ s) (snd M U) =
          lift (𝟙 X ⊗ₘ s) (snd X U) ≫ inv (leftSMul M X) ▷ U := by
      ext <;> simp
    have h2 : inv (leftSMul M X) ≫ γ[M, X] = fst X X := by simp
    simp only [Category.assoc, reassoc_of% h1]
    simp [h2]

@[reassoc (attr := simp)]
lemma isoTensorOfHom_hom_fst {U : C} (s : U ⟶ X) [IsHomogeneous M X] :
    (isoTensorOfHom M s).hom ≫ fst _ _ = _ ◁ s ≫ γ[M, X] := by
  simp [isoTensorOfHom]

@[reassoc (attr := simp)]
lemma isoTensorOfHom_hom_snd {U : C} (s : U ⟶ X) [IsHomogeneous M X] :
    (isoTensorOfHom M s).hom ≫ snd _ _ = snd _ _ := by
  simp [isoTensorOfHom]

@[reassoc (attr := simp)]
lemma isoTensorOfHom_inv_snd {U : C} (s : U ⟶ X) [IsHomogeneous M X] :
    (isoTensorOfHom M s).inv ≫ snd _ _ = snd _ _ := by
  simp [isoTensorOfHom]

/-- `isoTensorOfHom` is a module object homomorphism in `Over U`. To avoid passing
to `Over U`, we state this as an equality of morphisms `C`. -/
@[reassoc]
lemma smul_isoTensorOfHom_hom {U : C} (s : U ⟶ X) [IsHomogeneous M X] :
    μ ▷ U ≫ (isoTensorOfHom M s).hom =
      (α_ _ _ _).hom ≫ M ◁ (isoTensorOfHom M s).hom ≫ (α_ _ _ _).inv ≫ γ[M, X] ▷ U := by
  ext
  · have : M ◁ M ◁ s ≫ M ◁ γ[M, X] =
        (M ◁ lift (M ◁ s ≫ γ[M, X]) (snd M U) ≫ (α_ M X U).inv) ≫ fst (M ⊗ X) U := by
      ext <;> simp
    simp [isoTensorOfHom, ← whisker_exchange_assoc, reassoc_of% this]
  · simp

variable (M) in
/-- Any global section section `𝟙_ C ⟶ X`, induces an isomorphism `M ≅ X`. This
is compatible with the module structure. -/
noncomputable def isoOfHom (s : 𝟙_ C ⟶ X) [IsHomogeneous M X] : M ≅ X :=
  (ρ_ _).symm ≪≫ isoTensorOfHom M s ≪≫ ρ_ _

instance (s : 𝟙_ C ⟶ X) [IsHomogeneous M X] :
    IsModHom M (isoOfHom M s).hom where
  smul_hom := by
    have : μ ≫ (ρ_ M).inv = (ρ_ _).inv ≫ μ ▷ 𝟙_ C := by simp
    dsimp [isoOfHom]
    simp only [Iso.trans_hom, Iso.symm_hom, reassoc_of% this, smul_isoTensorOfHom_hom_assoc]
    simp

lemma isTrivialOver_iff_nonempty_iso [IsHomogeneous M X] (U : C) :
    IsTrivialOver M X U ↔ Nonempty (M ⊗ U ≅ X ⊗ U) :=
  ⟨fun h ↦ ⟨isoTensorOfHom _ h.nonempty_hom.some⟩,
    fun ⟨u⟩ ↦ ⟨⟨lift (toUnit _ ≫ η) (𝟙 _) ≫ u.hom ≫ fst _ _⟩⟩⟩

end CategoryTheory.ModObj
