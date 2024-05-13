import Mathlib


variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
variable (S : Subalgebra 𝕜 A) [hS : IsClosed (S : Set A)] (x : S)

open Topology Filter

-- this could be an `iff`. seems unnecessary though
---lemma NormedRing.tendsto_inv {l : Filter Aˣ} (a : Aˣ) (hx : Tendsto Units.val l (𝓝 a)) :
    ---Tendsto (fun x : Aˣ ↦ (↑x⁻¹ : A)) l (𝓝 (↑a⁻¹ : A)) := by
  ---rw [← Function.comp, ← Units.openEmbedding_val.tendsto_nhds_iff]
  ---apply Tendsto.inv
  ---rwa [Units.openEmbedding_val.tendsto_nhds_iff]

lemma NormedRing.tendsto_ring_inverse {l : Filter A} {a : Aˣ}
    (hla : l ≤ 𝓝 (a : A)) : Tendsto Ring.inverse l (𝓝 (↑a⁻¹ : A)) := by
  rw [← Ring.inverse_unit]
  exact (NormedRing.inverse_continuousAt a).tendsto.comp hla

lemma _root_.Subalgebra.isUnit_of_isUnit_val {l : Filter S} {a : S} (ha : IsUnit (a : A))
    (hla : l ≤ 𝓝 a) (hl : ∀ᶠ x in l, IsUnit x) (hl' : l.NeBot) : IsUnit a := by
  have hla₂ : Tendsto Ring.inverse (map S.val l) (𝓝 (↑ha.unit⁻¹ : A)) :=
    NormedRing.tendsto_ring_inverse <| continuousAt_subtype_val.tendsto.comp <| map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) ∈ S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply  hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mp <| eventually_of_forall fun x hx ↦ ?_
  suffices Ring.inverse (S.val x) = (S.val ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map S.val).unit_spec, Ring.inverse_unit (hx.map S.val).unit, Subalgebra.val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

attribute [fun_prop] continuous_algebraMap

open Set

lemma _root_.Subalgebra.frontier_spectrum : frontier (spectrum 𝕜 x) ⊆ spectrum 𝕜 (x : A) := by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.not_mem_iff] at h
  rw [← frontier_compl, IsOpen.frontier_eq, mem_diff] at hμ
  swap
  · rw [spectrum, compl_compl]
    exact spectrum.isOpen_resolventSet _
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff, spectrum.not_mem_iff]
  refine S.isUnit_of_isUnit_val h ?_ ?_ (NeBot.map hμ₁ (algebraMap 𝕜 S · - x))
  · calc
      _ ≤ map _ (𝓝 μ) := map_mono (by simp)
      _ ≤ _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.not_mem_iff]

lemma Subalgebra.frontier_subset_frontier :
    frontier (spectrum 𝕜 x) ⊆ frontier (spectrum 𝕜 (x : A)) := by
  rw [frontier_eq_closure_inter_closure (s := spectrum 𝕜 (x : A)),
    (spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (S.frontier_spectrum x)
  rw [frontier_eq_closure_inter_closure]
  exact inter_subset_right _ _ |>.trans <|
    closure_mono <| compl_subset_compl.mpr <| spectrum.subset_subalgebra x

open Set Notation

lemma isClopen_preimage_val {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsOpen u) (huv : frontier u ∩ v = ∅) : IsClopen (v ↓∩ u) := by
  refine ⟨?_, isOpen_induced hu (f := Subtype.val)⟩
  refine isClosed_induced_iff.mpr ⟨closure u, isClosed_closure, ?_⟩
  apply image_val_injective
  simp only [Subtype.image_preimage_coe]
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_comm _ (frontier u),
    huv, union_empty]

/-- If `u v : Set X` and `u ⊆ v` is clopen in `v`, then `u` is the union of the connected
components of `v` in `X` which intersect `u`. -/
lemma IsClopen.biUnion_connectedComponentIn {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hu : IsClopen (v ↓∩ u)) (huv₁ : u ⊆ v) :
    u = ⋃ x ∈ u, connectedComponentIn v x := by
  have := congr(((↑) : Set v → Set X) $(hu.biUnion_connectedComponent_eq.symm))
  simp only [Subtype.image_preimage_coe, mem_preimage, iUnion_coe_set, image_val_iUnion] at this
  rw [inter_eq_right.mpr huv₁] at this
  nth_rw 1 [this]
  congr! 2 with x hx
  simp only [← connectedComponentIn_eq_image]
  exact le_antisymm (iUnion_subset fun _ ↦ le_rfl) <|
    iUnion_subset fun hx ↦ subset_iUnion₂_of_subset (huv₁ hx) hx le_rfl

example {X : Type*} [TopologicalSpace X] {u v : Set X} (hu : IsOpen u) (huv₁ : u ⊆ v)
    (huv₂ : frontier u ∩ v = ∅) : u = ⋃ x ∈ u, connectedComponentIn v x :=
  isClopen_preimage_val hu huv₂ |>.biUnion_connectedComponentIn huv₁

local notation "σ" => spectrum

lemma Set.diff_subset_compl {X : Type*} {u v : Set X} : u \ v ⊆ vᶜ :=
  diff_eq_compl_inter ▸ inter_subset_left _ _

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complement of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`. -/
lemma Subalgebra.spectrum_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) ∪ (⋃ z ∈ (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓∩ (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn diff_subset_compl,
      union_diff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq, closure_eq_interior_union_frontier,
      union_diff_distrib, diff_eq_empty.mpr (S.frontier_spectrum x),
      diff_eq_compl_inter, union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) ⊆ frontier (σ 𝕜 (x : A)) by
    rw [← disjoint_iff_inter_eq_empty]
    exact disjoint_of_subset_left h_frontier <|
      disjoint_compl_right.frontier_left (spectrum.isClosed _).isOpen_compl
  rw [diff_eq_compl_inter]
  apply (frontier_inter_subset _ _).trans
  rw [frontier_compl]
  apply union_subset <| inter_subset_left _ _
  refine inter_subset_inter_right _ ?_ |>.trans <| inter_subset_right _ _
  exact S.frontier_subset_frontier x

lemma Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z ∈ σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z ∈ σ 𝕜 (x : A)
  · rw [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
    exact Bornology.isBounded_empty
  · have : CompleteSpace S := hS.completeSpace_coe
    suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z ⊆ σ 𝕜 x from spectrum.isBounded x |>.subset this
    rw [S.spectrum_sUnion_connectedComponentIn]
    exact subset_biUnion_of_mem (mem_diff_of_mem hz hz') |>.trans (subset_union_right _ _)
