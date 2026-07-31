/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.CompactlyGenerated
meta import Lean.PostprocessTraces
/-!

# The adjunction between condensed sets and topological spaces

This file defines the functor `condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1}` which is
left adjoint to `topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for compactly generated spaces, and we conclude that the functor
`topCatToCondensedSet` is fully faithful when restricted to compactly generated spaces.
-/


@[expose] public section

open Lean.PostprocessTraces

universe u

open Condensed CondensedSet CategoryTheory CompHaus

variable (X : CondensedSet.{u})

set_option backward.privateInPublic true in
/-- Auxiliary definition to define the topology on `X(*)` for a condensed set `X`. -/
private def CondensedSet.coinducingCoprod :
    (Σ (i : (S : CompHaus.{u}) × X.obj.obj ⟨S⟩), i.fst) → X.obj.obj ⟨of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ ↦ X.obj.map ((of PUnit.{u + 1}).const s).op i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Let `X` be a condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from compact Hausdorff `S` spaces to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `CondensedSet.coinducingCoprod` above. -/
local instance : TopologicalSpace (X.obj.obj ⟨CompHaus.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/-- The object part of the functor `CondensedSet ⥤ TopCat` -/
abbrev CondensedSet.toTopCat : TopCat.{u + 1} := TopCat.of (X.obj.obj ⟨of PUnit⟩)

namespace CondensedSet

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma continuous_coinducingCoprod {S : CompHaus.{u}} (x : X.obj.obj ⟨S⟩) :
    Continuous fun a ↦ (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices ∀ (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : CondensedSet} (f : X ⟶ Y)

/-- The map part of the functor `CondensedSet ⥤ TopCat` -/
@[simps!]
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.hom.app ⟨of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw [show (fun (a : S) ↦
          f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u + 1}).const a).op x)) = _
        from funext fun a ↦ NatTrans.naturality_apply f.hom ((of PUnit.{u + 1}).const a).op x]
      exact continuous_coinducingCoprod Y _ }

end CondensedSet

/-- The functor `CondensedSet ⥤ TopCat` -/
@[simps]
def condensedSetToTopCat : CondensedSet.{u} ⥤ TopCat.{u + 1} where
  obj X := X.toTopCat
  map f := toTopCatMap f

namespace CondensedSet

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u + 1}) : X.toCondensedSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

-- The dual of `filterSubtrees`: drop matching subtrees (used to remove `onFailure` duplicates).
private meta partial def dropSubtrees (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.filterMapM go
where
  go (t : TraceTree) : Lean.CoreM (Option TraceTree) := do
    if ← p t then
      return none
    match t with
    | .leaf msg => return some (.leaf msg)
    | .node data msg children wrap => return some (.node data msg (← children.filterMapM go) wrap)

private meta partial def elideBelow (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.mapM go
where
  go (t : TraceTree) : Lean.CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

/-! # Issue (Medium Severity) -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.instanceTypes false in
/-- `simp`-normal form of the lemma that `@[simps]` would generate. -/
@[simp] lemma topCatAdjunctionCounit_hom_apply (X : TopCat) (x) :
    -- We have to specify here to not infer the `TopologicalSpace` instance on `C(PUnit, X)`,
    -- which suggests type synonyms are being unfolded too far somewhere.
    DFunLike.coe (F := @ContinuousMap C(PUnit, X) X (_) _)
        (TopCat.Hom.hom (topCatAdjunctionCounit X)) x =
      (x PUnit.unit : TopCat.carrier X) := rfl

/-!
# Explanation

Summary of the investigation:
* This lemma explicitly requires non-canonical topologies on spaces of continuous maps.
* Possible workaround: Give the instance explicitly.
* Question: Is this lemma's signature actually useful in this form? It seems to be unused.
-/

set_option linter.style.longLine false in
/--
error: failed to synthesize instance of type class
  DFunLike C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) ?m.1 ?m.7
---
error: Function expected at
  x
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  PUnit.unit
---
trace: [Meta.synthInstance] ❌️ DFunLike C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) ?m.1 ?m.7
  [Meta.synthInstance.apply] ❌️ apply @ContinuousMap.instFunLike to DFunLike C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) ?m.11 ?m.12
    [Meta.synthInstance.tryResolve] ❌️ DFunLike C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) ?m.11
          ?m.12 ≟ DFunLike C(?m.14, ?m.15) ?m.14 fun x ↦ ?m.15
      [Meta.isDefEq] ❌️ [instances] DFunLike C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) ?m.11
            ?m.12 =?= DFunLike C(?m.14, ?m.15) ?m.14 fun x ↦ ?m.15
        [Meta.isDefEq] ❌️ [instances] C(C(PUnit.{?u.16 + 1}, ↑X), ↑X) =?= C(?m.14, ?m.15)
          [Meta.isDefEq] ❌️ [implicit] X.toCondensedSet.toTopCat.str =?= ?m.16
            [Meta.isDefEq.assign.checkTypes] ❌️ (?m.16 : TopologicalSpace
                  C(PUnit.{?u.16 + 1},
                    ↑X)) := (X.toCondensedSet.toTopCat.str : TopologicalSpace ↑X.toCondensedSet.toTopCat)
              [Meta.isDefEq] ❌️ [instances] TopologicalSpace
                    C(PUnit.{?u.16 + 1}, ↑X) =?= TopologicalSpace ↑X.toCondensedSet.toTopCat
                [Meta.isDefEq] ❌️ [instances] C(PUnit.{?u.16 + 1}, ↑X) =?= ↑X.toCondensedSet.toTopCat
                  [Meta.isDefEq] ❌️ [instances] C(PUnit.{?u.16 + 1}, ↑X) =?= X.toCondensedSet.toTopCat.1
                    [Meta.isDefEq] ❌️ [instances] C(PUnit.{?u.16 + 1},
                          ↑X) =?= X.toCondensedSet.obj.obj (Opposite.op (of PUnit.{?u.16 + 1}))
                      [Meta.isDefEq] ❌️ [instances] C(PUnit.{?u.16 + 1},
                            ↑X) =?= X.toCondensedSet.obj.1 (Opposite.op (of PUnit.{?u.16 + 1}))
                        [Meta.isDefEq] ❌️ [instances] ContinuousMap =?= X.toCondensedSet.obj.1
                          [Meta.isDefEq.onFailure] ❌️ ContinuousMap =?= X.toCondensedSet.obj.1
                        [Meta.isDefEq.onFailure] ❌️ C(PUnit.{?u.16 + 1},
                              ↑X) =?= X.toCondensedSet.obj.1 (Opposite.op (of PUnit.{?u.16 + 1}))
                [Meta.isDefEq.onFailure] ❌️ TopologicalSpace
                      C(PUnit.{?u.16 + 1}, ↑X) =?= TopologicalSpace ↑X.toCondensedSet.toTopCat
              [Meta.synthInstance] ✅️ TopologicalSpace C(PUnit.{?u.16 + 1}, ↑X) (truncated)
              [Meta.isDefEq] ❌️ [implicit] X.toCondensedSet.toTopCat.str =?= ContinuousMap.compactOpen (truncated)
            [Meta.isDefEq.assign.checkTypes] ❌️ (?m.16 : TopologicalSpace
                  C(PUnit.{?u.16 + 1},
                    ↑X)) := ({ IsOpen := fun s ↦ IsOpen (X.toCondensedSet.coinducingCoprod ⁻¹' s), isOpen_univ := ⋯,
                  isOpen_inter := ⋯,
                  isOpen_sUnion :=
                    ⋯ } : TopologicalSpace (X.toCondensedSet.obj.obj (Opposite.op (of PUnit.{?u.16 + 1})))) (truncated)
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x) <&&>
    (containsString "ContinuousMap.instFunLike" x))
  >=> filterSubtrees (fun x => ofClass `Meta.isDefEq.assign.checkTypes x <&&> failed x)
  >=> elideBelow (fun x => ofClass `Meta.synthInstance x <&&> succeeded x)
  >=> elideBelow (fun x => ofClass `Meta.isDefEq x <&&> containsString "ContinuousMap.compactOpen" x)
  >=> elideBelow (fun x => ofClass `Meta.isDefEq.assign.checkTypes x <&&> containsString ":= ({" x)
in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.printTransparency true in
set_option trace.Meta.isDefEq.assign.checkTypes true in
set_option backward.isDefEq.respectTransparency.types false in
example (X : TopCat) (x) :
    DFunLike.coe (F := @ContinuousMap C(PUnit, X) X (_) _)
        (TopCat.Hom.hom (topCatAdjunctionCounit X)) x =
      x PUnit.unit := rfl

section
variable (X : TopCat.{u + 1})

/--
error: Tactic `rfl` failed: The left-hand side
  X.toCondensedSet.toTopCat.str
is not definitionally equal to the right-hand side
  ContinuousMap.compactOpen

X✝¹ : CondensedSet
X✝ X : TopCat
⊢ X.toCondensedSet.toTopCat.str = ContinuousMap.compactOpen
-/
#guard_msgs in
example (X : TopCat.{u + 1}) :
    X.toCondensedSet.toTopCat.str =
      (ContinuousMap.compactOpen : TopologicalSpace C(PUnit, X)) := by
  apply_rfl

end


/-! # Fix -/
/-
Potential fix: explicitly annotate `x`, making the synthesis succeed without the `F` annotation.
This changes the `F` value, though, and this affects the discrimination key.
It's a very significant change, but I can't tell which version has the correct signature.
-/
set_option backward.isDefEq.respectTransparency.types false in
/-- `simp`-normal form of the lemma that `@[simps]` would generate. -/
@[simp] lemma topCatAdjunctionCounit_hom_apply_fixed? (X : TopCat) (x : C(PUnit, X)) :
    -- We have to specify here to not infer the `TopologicalSpace` instance on `C(PUnit, X)`,
    -- which suggests type synonyms are being unfolded too far somewhere.
    DFunLike.coe
        (TopCat.Hom.hom (topCatAdjunctionCounit X)) x =
      (x PUnit.unit : TopCat.carrier X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` is always bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is compactly generated).
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u + 1}) :
    X.toCondensedSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x

lemma topCatAdjunctionCounit_bijective (X : TopCat.{u + 1}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
@[simps hom_app]
noncomputable def topCatAdjunctionUnit (X : CondensedSet.{u}) : X ⟶ X.toTopCat.toCondensedSet where
  hom := {
    app S := ↾fun x ↦ {
      toFun := fun s ↦ X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices ∀ (i : (T : CompHaus.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ ↦ by
      ext
      simp only [TypeCat.Fun.toFun_apply,
        comp_apply, TopCat.toSheafCompHausLike_obj_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, ← Functor.map_comp_apply]
      rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` -/
noncomputable def topCatAdjunction : condensedSetToTopCat.{u} ⊣ topCatToCondensedSet where
  unit.app := topCatAdjunctionUnit
  counit.app := topCatAdjunctionCounit
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

set_option backward.isDefEq.respectTransparency.types false in
instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2

instance : topCatToCondensedSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open CompactlyGenerated

instance (X : CondensedSet.{u}) : UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f h
  rw [continuous_coinduced_dom, continuous_sigma_iff]
  exact fun ⟨S, s⟩ ↦ h S ⟨_, continuous_coinducingCoprod X _⟩

instance (X : CondensedSet.{u}) :
    UCompactlyGeneratedSpace.{u, u + 1} (condensedSetToTopCat.obj X) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u, u + 1} X.toTopCat)

/-- The functor from condensed sets to topological spaces lands in compactly generated spaces. -/
def condensedSetToCompactlyGenerated : CondensedSet.{u} ⥤ CompactlyGenerated.{u, u + 1} where
  obj X := CompactlyGenerated.of (condensedSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

/--
The functor from topological spaces to condensed sets restricted to compactly generated spaces.
-/
noncomputable def compactlyGeneratedToCondensedSet :
    CompactlyGenerated.{u, u + 1} ⥤ CondensedSet.{u} :=
  compactlyGeneratedToTop ⋙ topCatToCondensedSet


/--
The adjunction `condensedSetToTopCat ⊣ topCatToCondensedSet` restricted to compactly generated
spaces.
-/
noncomputable def compactlyGeneratedAdjunction :
    condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := compactlyGeneratedToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulCompactlyGeneratedToTop
    (Iso.refl _) (Iso.refl _)

/--
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet`
is a homeomorphism.
-/
noncomputable def compactlyGeneratedAdjunctionCounitHomeo
    (X : TopCat.{u + 1}) [UCompactlyGeneratedSpace.{u} X] :
    X.toCondensedSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply continuous_from_uCompactlyGeneratedSpace
    exact fun _ _ ↦ continuous_coinducingCoprod X.toCondensedSet _

/--
The counit of the adjunction `condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet`
is an isomorphism.
-/
noncomputable def compactlyGeneratedAdjunctionCounitIso (X : CompactlyGenerated.{u, u + 1}) :
    condensedSetToCompactlyGenerated.obj (compactlyGeneratedToCondensedSet.obj X) ≅ X :=
  isoOfHomeo (compactlyGeneratedAdjunctionCounitHomeo X.toTop)

instance : IsIso compactlyGeneratedAdjunction.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (compactlyGeneratedAdjunctionCounitIso X).hom)

/--
The functor from topological spaces to condensed sets restricted to compactly generated spaces
is fully faithful.
-/
noncomputable def fullyFaithfulCompactlyGeneratedToCondensedSet :
    compactlyGeneratedToCondensedSet.FullyFaithful :=
  compactlyGeneratedAdjunction.fullyFaithfulROfIsIsoCounit

end CondensedSet
