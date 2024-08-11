import Mathlib.Topology.Compactness.Compact

open Function Set Filter
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

structure IsOpenQuotientMap (f : X → Y) : Prop where
  surjective : Surjective f
  continuous : Continuous f
  isOpenMap : IsOpenMap f

namespace IsOpenQuotientMap

theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) :
    IsOpenQuotientMap (Prod.map f g) where
  surjective := hf.surjective.prodMap hg.surjective
  continuous := hf.continuous.prod_map hg.continuous
  isOpenMap := hf.isOpenMap.prod hg.isOpenMap

theorem piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i} (hf : ∀ i, IsOpenQuotientMap (f i)) :
    IsOpenQuotientMap (fun (x : ∀ i, X i) (i : ι) ↦ f i (x i)) where
  surjective := surjective_pi_map fun i ↦ (hf i).surjective
  continuous := continuous_pi fun i ↦ (hf i).continuous.comp (continuous_apply i)
  isOpenMap := by
    refine IsOpenMap.of_nhds_le fun x ↦ ?_
    simp only [nhds_pi]


protected theorem id : IsOpenQuotientMap (id : X → X) :=
  ⟨surjective_id, continuous_id, IsOpenMap.id⟩

end IsOpenQuotientMap  

structure IsPullbackQuotientMap (f : X → Y) : Prop where
  surjective : Surjective f
  continuous : Continuous f
  exists_finite_image_mem_nhds :
    ∀ y : Y, ∀ S : Set (Set X), (f ⁻¹' {y} ⊆ ⋃₀ S) → (∀ s ∈ S, IsOpen s) →
      ∃ T ⊆ S, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y

namespace IsPullbackQuotientMap

theorem of_isOpenMap {f : X → Y}

end IsPullbackQuotientMap

structure IsProdQuotientMap (f : X → Y) : Prop where
  surjective : Surjective f
  continuous : Continuous f
  exists_finite_image_mem_nhds :
    ∀ V : Set Y, ∀ S : Set (Set X), (⋃₀ S = f ⁻¹' V) → (∀ s ∈ S, IsOpen s) →
      ∀ y ∈ V, ∃ T ⊆ S, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y

namespace IsProdQuotientMap

theorem quotientMap {f : X → Y} (hf : IsProdQuotientMap f) : QuotientMap f := by
  refine quotientMap_iff.2 ⟨hf.surjective, fun V ↦ ⟨fun h ↦ h.preimage hf.continuous, fun ho ↦ ?_⟩⟩
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  obtain ⟨T, hTV, -, hTy⟩ : ∃ T ⊆ {f ⁻¹' V}, T.Finite ∧ f '' ⋃₀ T ∈ 𝓝 y :=
    hf.exists_finite_image_mem_nhds V {f ⁻¹' V} (sUnion_singleton _) (by simp [ho]) y hy
  calc
    V = f '' ⋃₀ {f ⁻¹' V} := by simp [hf.surjective]
    _ ⊇ f '' ⋃₀ T := by gcongr
    _ ∈ 𝓝 y := hTy

theorem of_open {f : X → Y} (hfc : Continuous f) (hfo : IsOpenMap f) (hsurj : Surjective f) :
    IsProdQuotientMap f := by
  refine ⟨hsurj, hfc, fun V S hSV hSo y hy ↦ ?_⟩
  rcases hsurj y with ⟨x, rfl⟩
  rw [← mem_preimage, ← hSV, mem_sUnion] at hy
  rcases hy with ⟨U, hUS, hxU⟩
  refine ⟨{U}, by simp [hUS], by simp, ?_⟩
  simpa using hfo.image_mem_nhds ((hSo U hUS).mem_nhds hxU)

theorem of_locallyCompact [LocallyCompactSpace Y] {f : X → Y} (hf : QuotientMap f) :
    IsProdQuotientMap f := by
  refine ⟨hf.surjective, hf.continuous, fun V S hSV hSo y hy ↦ ?_⟩
  

protected theorem id : IsProdQuotientMap (id : X → X) :=
  .of_open continuous_id IsOpenMap.id surjective_id
  
theorem prodMap {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : X → Y} (hf : IsProdQuotientMap f) {g : X' → Y'} (hg : IsProdQuotientMap g) :
    IsProdQuotientMap (Prod.map f g) := by
  sorry

end IsProdQuotientMap
