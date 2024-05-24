import Mathlib.Topology.Category.LightProfinite.IsLight

open CategoryTheory LightProfinite TopologicalSpace CompHausLike

abbrev LightCompHausLike :=
  CompHausLike (fun X ↦ TotallyDisconnectedSpace X ∧ Countable (Clopens X))

def LightCompHausLike.toProfinite (X : LightCompHausLike) : Profinite where
  toTop := X.toTop
  prop := X.prop.1

instance (X : LightCompHausLike) : X.toProfinite.IsLight where
  countable_clopens := X.prop.2

instance (X : LightCompHausLike) : TotallyDisconnectedSpace X := X.prop.1

instance (X : LightCompHausLike) : Countable (Clopens X) := X.prop.2

instance (X : LightCompHausLike) : SecondCountableTopology X := by
  rw [← Clopens.countable_iff_second_countable]
  infer_instance

namespace LightProfinite

@[simps]
def toCompHausLike : LightProfinite ⥤ LightCompHausLike where
  obj X := {
    toTop := (lightToProfinite.obj X).toTop
    prop := ⟨inferInstance, inferInstance⟩ }
  map f := f

@[simps]
noncomputable def fromCompHausLike : LightCompHausLike ⥤ LightProfinite where
  obj X := ofIsLight X.toProfinite
  map f := f

instance : toCompHausLike.Full := show (inducedFunctor _).Full from inferInstance

instance : toCompHausLike.Faithful := show (inducedFunctor _).Faithful from inferInstance

instance : toCompHausLike.IsEquivalence where
  essSurj := { mem_essImage := fun Y ↦ ⟨ofIsLight Y.toProfinite, ⟨Iso.refl _⟩⟩ }

instance : fromCompHausLike.Full := show (inducedFunctor _).Full from inferInstance

instance : fromCompHausLike.Faithful := show (inducedFunctor _).Faithful from inferInstance

instance : fromCompHausLike.IsEquivalence where
  essSurj := { mem_essImage := fun Y ↦ ⟨{
    toTop := (lightToProfinite.obj Y).toTop
    prop := ⟨inferInstance, inferInstance⟩ }, ⟨lightToProfinite.preimageIso (Iso.refl _)⟩⟩ }

noncomputable def equivCompHausLike :
    LightProfinite ≌ LightCompHausLike where
  functor := toCompHausLike
  inverse := fromCompHausLike
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ lightToProfinite.preimageIso (Iso.refl _)) ?_
    intro _ _ f
    simp only [Functor.id_obj, Functor.comp_obj, fromCompHausLike_obj, Functor.id_map,
      lightToProfinite_obj, Functor.preimageIso_hom, Iso.refl_hom, Functor.comp_map,
      toCompHausLike_map, fromCompHausLike_map]
    erw [lightToProfinite.preimage_id, lightToProfinite.preimage_id, Category.comp_id f]
  counitIso := Iso.refl _
  functor_unitIso_comp := by
    intro X
    simp only [Functor.id_obj, Functor.comp_obj, fromCompHausLike_obj, lightToProfinite_obj,
      NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Iso.refl_hom, toCompHausLike_map,
      NatTrans.id_app, Category.comp_id]
    exact lightToProfinite.preimage_id

theorem countable_clopens_of_injective {X : LightCompHausLike} {Y : Profinite}
    [Countable (Clopens Y)] (f : C(X, Y)) (hf : Function.Injective f) :
    Countable (Clopens X) := by
  rw [Clopens.countable_iff_second_countable] at *
  refine
    (closedEmbedding_of_continuous_injective_closed f.2 hf ?_).embedding.secondCountableTopology
  exact fun _ hC => (hC.isCompact.image f.continuous).isClosed
