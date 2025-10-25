/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.TopComparison
import Mathlib.Topology.Category.Sequential
import Mathlib.Topology.Category.LightProfinite.Sequence
/-!

# The adjunction between light condensed sets and topological spaces

This file defines the functor `lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u}` which is
left adjoint to `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for sequential spaces, and we conclude that the functor
`topCatToLightCondSet` is fully faithful when restricted to sequential spaces.
-/

universe u

open LightCondensed LightCondSet CategoryTheory LightProfinite

namespace LightCondSet

variable (X : LightCondSet.{u})

/-- Auxiliary definition to define the topology on `X(*)` for a light condensed set `X`. -/
private def coinducingCoprod :
    (Σ (i : (S : LightProfinite.{u}) × X.val.obj ⟨S⟩), i.fst) →
      X.val.obj ⟨LightProfinite.of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ ↦ X.val.map ((of PUnit.{u+1}).const s).op i

/-- Let `X` be a light condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from light profinite sets `S` to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `LightCondSet.coinducingCoprod` above. -/
local instance underlyingTopologicalSpace :
    TopologicalSpace (X.val.obj ⟨LightProfinite.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/-- The object part of the functor `LightCondSet ⥤ TopCat` -/
abbrev toTopCat : TopCat.{u} := TopCat.of (X.val.obj ⟨LightProfinite.of PUnit⟩)

lemma continuous_coinducingCoprod {S : LightProfinite.{u}} (x : X.val.obj ⟨S⟩) :
    Continuous fun a ↦ (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices ∀ (i : (T : LightProfinite.{u}) × X.val.obj ⟨T⟩),
      Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : LightCondSet} (f : X ⟶ Y)

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
/-- The map part of the functor `LightCondSet ⥤ TopCat` -/
@[simps!]
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.val.app ⟨LightProfinite.of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) ↦ f.val.app ⟨of PUnit⟩ (X.val.map ((of PUnit.{u+1}).const a).op x)) = _
        from funext fun a ↦ NatTrans.naturality_apply f.val ((of PUnit.{u+1}).const a).op x]
      exact continuous_coinducingCoprod _ _ }

/-- The functor `LightCondSet ⥤ TopCat` -/
@[simps]
def _root_.lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u} where
  obj X := X.toTopCat
  map f := toTopCatMap f

/-- The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u}) : X.toLightCondSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

/-- The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` is always bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is sequential).
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u}) : X.toLightCondSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

lemma topCatAdjunctionCounit_bijective (X : TopCat.{u}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

/-- The unit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
@[simps val_app val_app_apply]
noncomputable def topCatAdjunctionUnit (X : LightCondSet.{u}) : X ⟶ X.toTopCat.toLightCondSet where
  val := {
    app := fun S x ↦ {
      toFun := fun s ↦ X.val.map ((of PUnit.{u+1}).const s).op x
      continuous_toFun := by
        suffices ∀ (i : (T : LightProfinite.{u}) × X.val.obj ⟨T⟩),
          Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ ↦ by
      ext
      simp only [TopCat.toSheafCompHausLike_val_obj, Opposite.op_unop, types_comp_apply,
        TopCat.toSheafCompHausLike_val_map, ← FunctorToTypes.map_comp_apply]
      rfl }

/-- The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
noncomputable def topCatAdjunction : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where
  unit := { app := topCatAdjunctionUnit }
  counit := { app := topCatAdjunctionCounit }
  left_triangle_components Y := by
    ext
    change Y.val.map (𝟙 _) _ = _
    simp

instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2

instance : topCatToLightCondSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open Sequential

instance (X : LightCondSet.{u}) : SequentialSpace X.toTopCat := by
  apply SequentialSpace.coinduced

instance (X : LightCondSet.{u}) : SequentialSpace (lightCondSetToTopCat.obj X) :=
  inferInstanceAs (SequentialSpace X.toTopCat)

/-- The functor from light condensed sets to topological spaces lands in sequential spaces. -/
def lightCondSetToSequential : LightCondSet.{u} ⥤ Sequential.{u} where
  obj X := Sequential.of (lightCondSetToTopCat.obj X)
  map f := toTopCatMap f

/--
The functor from topological spaces to light condensed sets restricted to sequential spaces.
-/
noncomputable def sequentialToLightCondSet :
    Sequential.{u} ⥤ LightCondSet.{u} :=
  sequentialToTop ⋙ topCatToLightCondSet

/--
The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` restricted to sequential
spaces.
-/
noncomputable def sequentialAdjunction :
    lightCondSetToSequential ⊣ sequentialToLightCondSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := sequentialToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulSequentialToTop
    (Iso.refl _) (Iso.refl _)

/--
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSet`
is a homeomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for `X : TopCat.{0}`.
-/
noncomputable def sequentialAdjunctionHomeo (X : TopCat.{0}) [SequentialSpace X] :
    X.toLightCondSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply SeqContinuous.continuous
    unfold SeqContinuous
    intro f p h
    let g := (topCatAdjunctionCounitEquiv X).invFun ∘ (OnePoint.continuousMapMkNat f p h)
    change Filter.Tendsto (fun n : ℕ ↦ g n) _ _
    erw [← OnePoint.continuous_iff_from_nat]
    let x : X.toLightCondSet.val.obj ⟨(ℕ∪{∞})⟩ := OnePoint.continuousMapMkNat f p h
    exact continuous_coinducingCoprod X.toLightCondSet x

/--
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSet`
is an isomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for `X : Sequential.{0}`.
-/
noncomputable def sequentialAdjunctionCounitIso (X : Sequential.{0}) :
    lightCondSetToSequential.obj (sequentialToLightCondSet.obj X) ≅ X :=
  isoOfHomeo (sequentialAdjunctionHomeo X.toTop)

instance : IsIso sequentialAdjunction.{0}.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (sequentialAdjunctionCounitIso X).hom)

/--
The functor from topological spaces to light condensed sets restricted to sequential spaces
is fully faithful.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for the functor `Sequential.{0} ⥤ LightCondSet.{0}`.
-/
noncomputable def fullyFaithfulSequentialToLightCondSet :
    sequentialToLightCondSet.{0}.FullyFaithful :=
  sequentialAdjunction.fullyFaithfulROfIsIsoCounit

end LightCondSet
