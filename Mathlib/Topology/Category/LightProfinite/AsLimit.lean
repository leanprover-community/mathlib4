/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

-/

noncomputable section

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

/-- The functor `ℕᵒᵖ ⥤ FintypeCat` whose limit is isomorphic to `S`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram

/-- An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
A cone over `S.diagram` whose cone point is isomorphic to `S`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

/-- An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

/--
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
-/
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A cone over `S.diagram` whose cone point is `S`. -/
def asLimitCone : Cone S.diagram where
  pt := S
  π := {
    app := fun n ↦ (lightToProfiniteFullyFaithful.preimageIso <|
      Cones.ptIsoOfIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

/-- `S.asLimitCone` is indeed a limit cone. -/
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit <|
  Cones.ext (lightToProfiniteFullyFaithful.preimageIso <|
    Cones.ptIsoOfIso S.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)

/-- A bundled version of `S.asLimitCone` and `S.asLimit`. -/
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩

abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩

lemma map_liftedLimit {C D J : Type*} [Category C] [Category D] [Category J] {K : J ⥤ C}
    {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (n : J) :
    (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app n) = c.π.app n := by
  have : (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app n = F.map ((liftLimit t).π.app n) := by
    simp
  rw [← this, ← Category.assoc, ← Cone.category_comp_hom]
  simp

lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [Functor.comp_obj, proj, asLimitCone, Functor.const_obj_obj, asLimitConeAux, isoMapCone,
    Functor.FullyFaithful.preimageIso_inv, Cones.ptIsoOfIso_inv, Functor.map_comp,
    Functor.FullyFaithful.map_preimage]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact map_liftedLimit hc _

lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩

abbrev transitionMap (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

@[simp, reassoc]
lemma proj_comp_transitionMap (n : ℕ) : S.proj (n + 1) ≫ S.transitionMap n = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

@[simp]
lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl

@[simp, reassoc]
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.transitionMapLE h = S.proj n :=
  S.asLimitCone.w (homOfLE h).op

@[simp]
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

lemma surjective_transitionMap (n : ℕ) : Function.Surjective (S.transitionMap n) := by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n

lemma surjective_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (S.transitionMapLE h) := by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

end LightProfinite
