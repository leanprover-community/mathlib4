/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically connected schemes

In this file we define geometrically connected morphisms of schemes. A morphism `f : X ⟶ Y` is
geometrically connected if for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
In the case where `Y = Spec K` for some field `K` this recovers the standard definition
of a geometrically connected scheme over a field.

## Main results

- `AlgebraicGeometry.GeometricallyConnected`: A morphism `f : X ⟶ Y` is geometrically connected if
  for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
- `GeometricallyConnected.iff_geometricallyConnected_fiber`: A scheme is geometrically connected
  over `S` iff the fibers of all `s : S` are geometrically connected.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that a morphism `f : X ⟶ Y` is geometrically connected if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is connected. -/
@[mk_iff]
class GeometricallyConnected (f : X ⟶ Y) : Prop where
  geometrically_connectedSpace : geometrically (ConnectedSpace ·) f

lemma GeometricallyConnected.eq_geometrically :
    @GeometricallyConnected = geometrically (ConnectedSpace ·) := by
  ext; exact geometricallyConnected_iff _

instance : IsStableUnderBaseChange @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

instance [GeometricallyConnected g] : GeometricallyConnected (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance [GeometricallyConnected f] : GeometricallyConnected (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyConnected f] : GeometricallyConnected (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

instance (s : S) [GeometricallyConnected f] :
    GeometricallyConnected (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyConnected f] : ConnectedSpace (f.fiber s) :=
  GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)

instance (priority := low) [GeometricallyConnected f] : Surjective f :=
  ⟨fun x ↦ ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩

lemma Scheme.Hom.isConnected_preimage_singleton [GeometricallyConnected f] (x : S) :
    _root_.IsConnected (f ⁻¹' {x}) := by
  rw [← f.range_fiberι, ← Set.image_univ]
  exact isConnected_univ.image _ (f.fiberι _).continuous.continuousOn

lemma Scheme.Hom.isConnected_preimage [GeometricallyConnected f] (hf : IsOpenMap f)
    {s : Set S} (hs : _root_.IsConnected s) (hs' : IsClosed s) : _root_.IsConnected (f ⁻¹' s) := by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed f.isConnected_preimage_singleton
    ?_ hs' hs
  exact (hf.isQuotientMap f.continuous f.surjective).isCoinducing

/-- If `f : X ⟶ S` is geometrically connected and open,
then `f` induces a homeomorphism between the connected components of `X` and `S`. -/
@[simps! apply]
noncomputable
def Scheme.Hom.connectedComponentsHomeomorph [GeometricallyConnected f] (hf : IsOpenMap f) :
    ConnectedComponents X ≃ₜ ConnectedComponents S :=
  (hf.isQuotientMap f.continuous f.surjective).isCoinducing.connectedComponentsHomeomorph
    f.isConnected_preimage_singleton

lemma GeometricallyConnected.connectedSpace [GeometricallyConnected f] [ConnectedSpace S]
    (hf : IsOpenMap f) :
    ConnectedSpace X := by
  simpa [connectedSpace_iff_univ] using f.isConnected_preimage hf isConnected_univ

/-- If `X` is geometrically connected over a point, then it is connected. -/
lemma GeometricallyConnected.connectedSpace_of_subsingleton
    [GeometricallyConnected f] [Subsingleton S] [Nonempty S] : ConnectedSpace X :=
  have : ConnectedSpace S := ⟨‹_›⟩
  GeometricallyConnected.connectedSpace (f := f) fun _ _ ↦ isOpen_discrete _

instance [GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

instance [GeometricallyConnected g] [UniversallyOpen g] [ConnectedSpace X] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

lemma GeometricallyConnected.iff_geometricallyConnected_fiber :
    GeometricallyConnected f ↔ ∀ s, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  simp only [eq_geometrically, ← geometrically_iff_forall_fiberToSpecResidueField]

lemma GeometricallyConnected.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected f] [GeometricallyConnected g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  infer_instance

end AlgebraicGeometry
