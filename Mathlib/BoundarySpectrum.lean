import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Data.Set.Subset
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

local notation "σ" => spectrum

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
  case' upper => apply Complex.isConnected_of_upperHalfPlane ?_ <| Set.inter_subset_right
  case' lower => apply Complex.isConnected_of_lowerHalfPlane ?_ <| Set.inter_subset_right
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
