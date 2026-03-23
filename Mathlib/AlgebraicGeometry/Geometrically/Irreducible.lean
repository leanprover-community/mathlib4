/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically Irreducible Schemes

## Main results
- `AlgebraicGeometry.GeometricallyIrreducible`:
  We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is irrreducible.
  We also provide the fact that this is stable under base change (by infer_instance)
- `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber`:
  A scheme is geometrically irreducible over `S` iff the fibers of all
  `s : S` are geometrically irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace`:
  If `X` is geometrically irreducible and universally open (e.g. when flat + finite presentation),
  over an irreducible scheme, then `X` is also irreducible.
  In particular, the base change of a geometrically irreducible and universally open scheme to an
  irreducible scheme is irreducible (by infer_instance).
-/

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is irrreducible. -/
@[mk_iff]
class GeometricallyIrreducible (f : X ⟶ Y) : Prop where
  geometrically_irreducibleSpace : geometrically (IrreducibleSpace ·) f

lemma GeometricallyIrreducible.eq_geometrically :
    @GeometricallyIrreducible = geometrically (IrreducibleSpace ·) := by
  ext; exact geometricallyIrreducible_iff _

instance : IsStableUnderBaseChange @GeometricallyIrreducible :=
  GeometricallyIrreducible.eq_geometrically ▸ inferInstance

instance [GeometricallyIrreducible g] : GeometricallyIrreducible (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance [GeometricallyIrreducible f] : GeometricallyIrreducible (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyIrreducible f] : GeometricallyIrreducible (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

instance (s : S) [GeometricallyIrreducible f] :
    GeometricallyIrreducible (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyIrreducible f] : IrreducibleSpace (f.fiber s) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)

instance (priority := low) [GeometricallyIrreducible f] : Surjective f :=
  ⟨fun x ↦ ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩

lemma Scheme.Hom.isIrreducible_preimage
    [GeometricallyIrreducible f] (hf : IsOpenMap f)
    {s : Set S} (hs : IsIrreducible s) : IsIrreducible (f ⁻¹' s) := by
  wlog H : ∃ x, s = {x} generalizing s
  · refine hs.preimage_of_isPreirreducible_fiber _ hf
      (fun x ↦ (this isIrreducible_singleton ⟨_, rfl⟩).isPreirreducible) ?_
    rw [Set.range_eq_univ.mpr f.surjective, Set.inter_univ]
    exact hs.nonempty
  obtain ⟨s, rfl⟩ := H
  rw [← f.range_fiberι, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι _).continuous.continuousOn

/-- If `f : X ⟶ S` is geometrically irreducible and open,
then `f` induces an equivalence between the irreducible components of `X` and `S`. -/
@[simps!]
def Scheme.Hom.irreducibleComponentsEquiv [GeometricallyIrreducible f] (hf : IsOpenMap f) :
    irreducibleComponents X ≃ irreducibleComponents S :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous hf
    (fun _ ↦ (f.isIrreducible_preimage hf isIrreducible_singleton).isPreirreducible)
    f.surjective).symm.toEquiv

lemma GeometricallyIrreducible.irreducibleSpace
    [GeometricallyIrreducible f] [IrreducibleSpace S] (hf : IsOpenMap f) : IrreducibleSpace X := by
  simpa [irreducibleSpace_def] using
    f.isIrreducible_preimage hf (IrreducibleSpace.isIrreducible_univ _)

/-- If `X` is geometrically irreducible over a point, then it is irreducible. -/
lemma GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    [GeometricallyIrreducible f] [Subsingleton S] [Nonempty S] : IrreducibleSpace X :=
  have : IrreducibleSpace S := ⟨‹_›⟩
  GeometricallyIrreducible.irreducibleSpace (f := f) fun _ _ ↦ isOpen_discrete _

/-- If `X` is geometrically irreducible and universally open over `S` and `Y` is irreducible,
then `X ×ₛ Y` is irreducible.

The universally open assumption in particular holds when it is flat and locally of finite
presentation, or when `S` is a field. -/
instance [GeometricallyIrreducible f] [UniversallyOpen f] [IrreducibleSpace Y] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

instance [GeometricallyIrreducible g] [UniversallyOpen g] [IrreducibleSpace X] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

lemma GeometricallyIrreducible.iff_geometricallyIrreducible_fiber :
    GeometricallyIrreducible f ↔ ∀ s, GeometricallyIrreducible (f.fiberToSpecResidueField s) := by
  simp only [GeometricallyIrreducible.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

lemma GeometricallyIrreducible.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIrreducible f] [GeometricallyIrreducible g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyIrreducible (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

end AlgebraicGeometry
