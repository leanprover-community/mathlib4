import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Data.Set.Subset
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

local notation "σ" => spectrum

namespace SubalgebraClass

section Algebra

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

instance (priority := 75) toAlgebra : Algebra R s where
  toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
  map_one' := Subtype.ext <| by simp
  map_mul' _ _ := Subtype.ext <| by simp
  map_zero' := Subtype.ext <| by simp
  map_add' _ _ := Subtype.ext <| by simp
  commutes' r x := Subtype.ext <| Algebra.commutes r (x : A)
  smul_def' r x := Subtype.ext <| (algebraMap_smul A r (x : A)).symm


/-- Embedding of a non-unital subalgebra into the non-unital algebra. -/
def val (s : S) : s →ₐ[R] A :=
  { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ ↦ rfl }

@[simp]
theorem coe_val : (val s : s → A) = ((↑) : s → A) :=
  rfl

end Algebra

section spectrum


variable {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
variable [SetLike S A] [SubringClass S A] [hSR : SMulMemClass S R A]

lemma _root_.spectrum.subset_subalgebra' {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a :=
  Set.compl_subset_compl.mpr fun _ ↦ IsUnit.map (val s)


end spectrum

section NormedAlgebra

variable {S R A : Type*} [NormedField R] [NormedRing A] [NormedAlgebra R A]
variable [SetLike S A] [SubringClass S A] [hSR : SMulMemClass S R A] (s : S)

instance (priority := 75) toNormedAlgebra : NormedAlgebra R s where
  norm_smul_le r x := norm_smul_le r (x : A)

end NormedAlgebra

end SubalgebraClass

section BoundarySpectrum

variable {𝕜 A SubalgClass : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
variable [SetLike SubalgClass A] [SubringClass SubalgClass A] [SMulMemClass SubalgClass 𝕜 A]
variable (S : SubalgClass) [hS : IsClosed (S : Set A)] (x : S)

open Topology Filter

open SubalgebraClass in
/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If `a : S` is invertible in `A`,
and for all `x : S` sufficiently close to `a` within some filter `l`, `x` is invertible in `S`,
then `a` is invertible in `S` as well. -/
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S}
    (ha : IsUnit (a : A)) (hla : l ≤ 𝓝 a) (hl : ∀ᶠ x in l, IsUnit x) (hl' : l.NeBot) :
    IsUnit a := by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
    exact (NormedRing.inverse_continuousAt _).tendsto.comp <|
      continuousAt_subtype_val.tendsto.comp <| map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) ∈ S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mp <| eventually_of_forall fun x hx ↦ ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  have := (hx.map (val S)).unit_spec
  rw [← (hx.map (val S)).unit_spec, Ring.inverse_unit (hx.map (val S)).unit, val]
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
    exact spectrum.isOpen_resolventSet (𝕜 := 𝕜) x
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff, spectrum.not_mem_iff]
  refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ <| .map hμ₁ (algebraMap 𝕜 S · - x)
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
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  exact inter_subset_right _ _ |>.trans <|
    closure_mono <| compl_subset_compl.mpr <| spectrum.subset_subalgebra' x

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

lemma Set.diff_subset_compl {X : Type*} {u v : Set X} : u \ v ⊆ vᶜ :=
  diff_eq_compl_inter ▸ inter_subset_left _ _

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complement of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`. -/
lemma Subalgebra.spectrum_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) ∪ (⋃ z ∈ (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓∩ (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn diff_subset_compl,
      union_diff_cancel (spectrum.subset_subalgebra' x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq, closure_eq_interior_union_frontier,
      union_diff_distrib, diff_eq_empty.mpr (frontier_spectrum S x),
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
  exact frontier_subset_frontier S x

lemma Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z ∈ σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z ∈ σ 𝕜 (x : A)
  · rw [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
    exact Bornology.isBounded_empty
  · have : CompleteSpace S := hS.completeSpace_coe
    suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z ⊆ σ 𝕜 x from spectrum.isBounded x |>.subset this
    rw [spectrum_sUnion_connectedComponentIn S]
    exact subset_biUnion_of_mem (mem_diff_of_mem hz hz') |>.trans (subset_union_right _ _)

end BoundarySpectrum

section

variable {𝕜 A SubalgClass : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
variable [SetLike SubalgClass A] [SubringClass SubalgClass A] [SMulMemClass SubalgClass 𝕜 A]
variable (S : SubalgClass) [hS : IsClosed (S : Set A)] (x : S)

open Set

/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If for `x : S` the complement of the
spectrum of `↑x : A` is connected, then `spectrum 𝕜 x = spectrum 𝕜 (x : A)`. -/
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) :
    σ 𝕜 x = σ 𝕜 (x : A) := by
  nontriviality A
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn, this]
    simp
  refine eq_empty_of_forall_not_mem fun z hz ↦ ?_
  obtain ⟨hz, hz'⟩ := mem_diff _ |>.mp hz
  have := (spectrum.isBounded (x : A)).union <|
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  exact NormedSpace.unbounded_univ 𝕜 𝕜 <| by simpa

end

section SpectralPermanence

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A] [CstarRing A]

open Bornology

lemma Complex.isConnected_of_upperHalfPlane {s : Set ℂ} (hs₁ : {z | 0 < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | 0 ≤ z.im}) : IsConnected s := by
  refine IsConnected.subset_closure ?_ hs₁ (by simpa using hs₂)
  rw [isConnected_iff_connectedSpace]
  exact inferInstanceAs (ConnectedSpace UpperHalfPlane)

lemma Complex.isConnected_of_lowerHalfPlane {s : Set ℂ} (hs₁ : {z | z.im < 0} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ 0}) : IsConnected s := by
  rw [← Equiv.star.surjective.image_preimage s]
  refine IsConnected.image (f := Equiv.star) ?_ continuous_star.continuousOn
  apply Complex.isConnected_of_upperHalfPlane
  · exact fun z hz ↦ hs₁ <| show star z ∈ _ by simpa
  · exact fun z hz ↦ by simpa using show (star z).im ≤ 0 from hs₂ hz

lemma IsSelfAdjoint.isConnected_spectrum_compl [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a) :
    IsConnected (σ ℂ a)ᶜ := by
  suffices IsConnected (((σ ℂ a)ᶜ ∩ {z | 0 ≤ z.im}) ∪ (σ ℂ a)ᶜ ∩ {z | z.im ≤ 0}) by
    rw [← Set.inter_union_distrib_left, ← Set.setOf_or] at this
    rw [← Set.inter_univ (σ ℂ a)ᶜ]
    convert this using 2
    exact Eq.symm <| Set.eq_univ_of_forall (fun z ↦ le_total 0 z.im)
  refine IsConnected.union ?nonempty ?upper ?lower
  case nonempty =>
    have := Filter.NeBot.nonempty_of_mem inferInstance <| Filter.mem_map.mp <|
      Complex.isometry_ofReal.antilipschitz.tendsto_cobounded (spectrum.isBounded a |>.compl)
    exact this.image Complex.ofReal' |>.mono <| by simpa using Set.Subset.rfl
  case' upper => apply Complex.isConnected_of_upperHalfPlane ?_ <| Set.inter_subset_right _ _
  case' lower => apply Complex.isConnected_of_lowerHalfPlane ?_ <| Set.inter_subset_right _ _
  all_goals
    apply Set.subset_inter ?_ (fun z hz ↦ by rw [Set.mem_setOf_eq] at hz ⊢; exact hz.le)
    intro z hz hz'
    rw [Set.mem_setOf_eq, ha.mem_spectrum_eq_re hz'] at hz
    simp_all

lemma StarSubalgebra.coe_isUnit [StarModule ℂ A] (S : StarSubalgebra ℂ A)
    [_hS : IsClosed (S : Set A)] {a : S} :
    IsUnit (a : A) ↔ IsUnit a := by
  refine ⟨fun ha ↦ ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum ℂ x = spectrum ℂ (x : A) :=
    Subalgebra.spectrum_eq_of_isPreconnected_compl S _ <|
      (hx.starHom_apply S.subtype).isConnected_spectrum_compl.isPreconnected
  rw [← StarMemClass.coe_star, ← MulMemClass.coe_mul, ← spectrum.zero_not_mem_iff ℂ, ← spec_eq,
    spectrum.zero_not_mem_iff] at ha₁ ha₂
  · have h₁ : ha₁.unit⁻¹ * star a * a = 1 := mul_assoc _ _ a ▸ ha₁.val_inv_mul
    have h₂ : a * (star a * ha₂.unit⁻¹) = 1 := (mul_assoc a _ _).symm ▸ ha₂.mul_val_inv
    exact ⟨⟨a, ha₁.unit⁻¹ * star a, left_inv_eq_right_inv h₁ h₂ ▸ h₂, h₁⟩, rfl⟩
  · exact IsSelfAdjoint.mul_star_self a
  · exact IsSelfAdjoint.star_mul_self a

lemma StarSubalgebra.mem_spectrum_iff [StarModule ℂ A] (S : StarSubalgebra ℂ A)
    [_hS : IsClosed (S : Set A)] {a : S} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ z ∈ spectrum ℂ (a : A) :=
  not_iff_not.2 S.coe_isUnit.symm

lemma StarSubalgebra.spectrum_eq [StarModule ℂ A] (S : StarSubalgebra ℂ A)
    [_hS : IsClosed (S : Set A)] {a : S} :
    spectrum ℂ a = spectrum ℂ (a : A) :=
  Set.ext fun _ ↦ S.mem_spectrum_iff

end SpectralPermanence
