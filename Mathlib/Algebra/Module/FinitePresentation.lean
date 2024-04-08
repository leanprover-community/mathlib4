import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.LinearAlgebra.Isomorphisms


variable (R M N) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

class Module.FinitePresentation : Prop where
  out : ∃ (s : Finset M), Submodule.span R (s : Set M) = ⊤ ∧
    (LinearMap.ker (Finsupp.total s M R Subtype.val)).FG

instance [h : Module.FinitePresentation R M] : Module.Finite R M := by
  obtain ⟨s, hs₁, _⟩ := h
  exact ⟨s, hs₁⟩

noncomputable
def Module.FinitePresentation.spanningSet [h : Module.FinitePresentation R M] : Finset M :=
  h.1.choose

lemma Module.FinitePresentation.span_spanningSet [h : Module.FinitePresentation R M] :
    Submodule.span R (spanningSet R M : Set M) = ⊤ := h.1.choose_spec.1

lemma Module.FinitePresentation.ker_total_spanningSet [h : Module.FinitePresentation R M] :
    (LinearMap.ker (Finsupp.total (spanningSet R M) M R Subtype.val)).FG := h.1.choose_spec.2

noncomputable
def Module.FinitePresentation.presentation [Module.FinitePresentation R M] :
    (spanningSet R M → R) →ₗ[R] M :=
  Fintype.total (α := spanningSet R M) R R Subtype.val

lemma Module.FinitePresentation.ker_presentation [Module.FinitePresentation R M] :
    (LinearMap.ker (presentation R M)).FG := by
  rw [presentation, ← Finsupp.total_eq_fintype_total, LinearMap.ker_comp,
    Submodule.comap_equiv_eq_map_symm]
  exact (Module.FinitePresentation.ker_total_spanningSet R M).map _

lemma Module.FinitePresentation.presentation_surjective [Module.FinitePresentation R M] :
    Function.Surjective (presentation R M) := by
  rw [← LinearMap.range_eq_top, presentation, Fintype.range_total,
    Subtype.range_coe_subtype, Finset.setOf_mem, span_spanningSet]

variable {R M N}

@[simp]
lemma Module.FinitePresentation.presentation_single [Module.FinitePresentation R M]
    [DecidableEq (spanningSet R M)] (i r) :
  presentation R M (Pi.single i r) = r • (i : M) := Fintype.total_apply_single _ _ _ _

open BigOperators
def Module.FinitePresentation.exists_lift_of_isLocalizedModule (S : Submonoid R)
    {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') [IsLocalizedModule S f]
    [Module.FinitePresentation R M] (g : M →ₗ[R] N') :
    ∃ (h : M →ₗ[R] N) (s : S), f ∘ₗ h = s • g := by
  classical
  choose s hs using IsLocalizedModule.surj S f
  let i : spanningSet R M → N :=
    fun x ↦ (∏ j in (spanningSet R M).erase x.1, (s (g j)).2) • (s (g x)).1
  let s₀ := ∏ j in spanningSet R M, (s (g j)).2
  have hi : f ∘ₗ Fintype.total R R i = (s₀ • g) ∘ₗ presentation R M := by
    ext j
    simp only [ne_eq, LinearMap.coe_comp, LinearMap.coe_single, Function.comp_apply,
      Fintype.total_apply_single, one_smul, LinearMap.map_smul_of_tower, ← hs, LinearMap.smul_apply,
      presentation_single, i, s₀]
    rw [← mul_smul, Finset.prod_erase_mul]
    exact j.prop
  obtain ⟨σ, hσ⟩ := Module.FinitePresentation.ker_presentation R M
  have : ∀ x : σ, ∃ s : S, s • (Fintype.total R R i x) = 0 := by
    intros x
    convert_to ∃ s : S, s • (Fintype.total R R i x) = s • 0
    · simp only [smul_zero]
    apply IsLocalizedModule.exists_of_eq (S := S) (f := f)
    rw [← LinearMap.comp_apply, map_zero, hi, LinearMap.comp_apply]
    convert map_zero (s₀ • g)
    rw [← LinearMap.mem_ker, ← hσ]
    exact Submodule.subset_span x.prop
  choose s' hs' using this
  let s₁ := ∏ i : σ, s' i
  have : LinearMap.ker (presentation R M) ≤ LinearMap.ker (s₁ • Fintype.total R R i) := by
    rw [← hσ, Submodule.span_le]
    intro x hxσ
    simp only [s₁]
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨x, hxσ⟩), mul_smul]
    convert smul_zero _
    exact hs' ⟨x, hxσ⟩
  refine ⟨Submodule.liftQ _ _ this ∘ₗ (LinearMap.quotKerEquivOfSurjective _
    (presentation_surjective R M)).symm.toLinearMap, s₁ * s₀, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := presentation_surjective R M x
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, mul_smul, LinearMap.smul_comp, ← hi,
    ← LinearMap.comp_smul, LinearMap.comp_assoc, LinearMap.comp_assoc]
  congr 2
  convert Submodule.liftQ_mkQ _ _ this using 2
  ext x
  apply (LinearMap.quotKerEquivOfSurjective _ (presentation_surjective R M)).injective
  simp [LinearMap.quotKerEquivOfSurjective]








  -- have : ∀ i ∈ spanningSet R M, ∃ s : S, s • (g i) ∈ LinearMap.range f := by
  --   intro i hi
  --   have :=
