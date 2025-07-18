/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

-/

noncomputable section

open CategoryTheory Limits CompHausLike

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

/-- The functor `ℕᵒᵖ ⥤ FintypeCat` whose limit is isomorphic to `S`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram

/-- An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
A cone over `S.diagram` whose cone point is isomorphic to `S`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

/-- An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

/--
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
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
      (Cones.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

/-- `S.asLimitCone` is indeed a limit cone. -/
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit <|
  Cones.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cones.forget _).mapIso S.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)

/-- A bundled version of `S.asLimitCone` and `S.asLimit`. -/
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩

/-- The projection from `S` to the `n`th component of `S.diagram`. -/
abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩

lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [Functor.comp_obj, toCompHausLike_map]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _

lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

/-- An abbreviation for the `n`th component of `S.diagram`. -/
abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩

/-- The transition map from `S_{n+1}` to `S_n` in `S.diagram`. -/
abbrev transitionMap (n : ℕ) :  S.component (n + 1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

/-- The transition map from `S_m` to `S_n` in `S.diagram`, when `m ≤ n`. -/
abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

lemma proj_comp_transitionMap (n : ℕ) :
    S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl

lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE h).op

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
