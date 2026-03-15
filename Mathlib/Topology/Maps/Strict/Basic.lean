import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Data.Setoid.Basic

open Function Set Topology

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- Bourbaki strict map: quotient topology on the image. -/
def IsStrictMap : Prop :=
  IsQuotientMap (Set.rangeFactorization f)


lemma IsQuotientMap.isOpenMap_of_injective {f : X → Y} (hq : IsQuotientMap f)
(hinj : Function.Injective f) : IsOpenMap f := by
    intro s hs
    rwa [← hq.isOpen_preimage, Set.preimage_image_eq _ hinj]

theorem isStrictMap_iff_kerLift_isEmbedding :
    IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f) := by
  let e := Setoid.quotientKerEquivRange f
  let q := @Quotient.mk X (Setoid.ker f)
  have hq : IsStrictMap f ↔ IsQuotientMap e :=
    ⟨fun hf => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' hf,
     fun he => he.comp isQuotientMap_quotient_mk'⟩
  have he : IsQuotientMap e ↔ IsEmbedding e := by
    refine ⟨fun hqe => ?_, fun hee => ?_⟩
    · exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hqe.continuous
        e.injective (hqe.isOpenMap_of_injective e.injective)).isEmbedding
    · exact (hee.isOpenEmbedding_of_surjective e.surjective).isOpenMap.isQuotientMap
        hee.continuous e.surjective
  rw [hq, he]
  exact (IsEmbedding.of_comp_iff (f := e) (g := (Subtype.val : Set.range f → Y)) .subtypeVal).symm

theorem isStrictMap_iff_quotientKerEquivRange_isHomeomorph :
    IsStrictMap f ↔
      IsHomeomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) → Set.range f) := by
  let e := Setoid.quotientKerEquivRange f
  rw [isStrictMap_iff_kerLift_isEmbedding, isHomeomorph_iff_isEmbedding_surjective]
  have h_comp : IsEmbedding (Setoid.kerLift f) ↔ IsEmbedding e :=
    IsEmbedding.of_comp_iff (f := e) (g := (Subtype.val : Set.range f → Y)) .subtypeVal
  rw [h_comp]
  exact (and_iff_left e.surjective).symm

end Topology
