import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.Condensed.Module

universe u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike


open CategoryTheory Sheaf Limits

namespace Condensed

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

lemma epi_iff_locallySurjective : Epi f ↔
    ∀ (S : CompHaus) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi]
  constructor
  · intro ⟨h⟩ S y
    specialize h y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    refine ⟨∐ Z, Sigma.desc π, ?_, ?_⟩
    · rwa [← CompHaus.epi_iff_surjective, ((CompHaus.effectiveEpiFamily_tfae Z π).out 1 0 :)]
    · simp [Presheaf.imageSieve] at h'
      let x : (a : α) → X.val.obj ⟨Z a⟩ := fun a ↦ (h' a).choose
      sorry
      /- apply the isomorphism `X.val.obj ⟨∐ Z⟩ ≅ (a : α) → X.val.obj ⟨Z a⟩` to `x` and use that -/
  · intro h
    constructor
    intro S y
    obtain ⟨S', φ, hφ, _⟩ := h S y
    have : regularTopology CompHaus ≤ coherentTopology CompHaus := by
      rw [← extensive_regular_generate_coherent]
      exact (Coverage.gi _).gc.monotone_l le_sup_right
    fconstructor
    · exact Sieve.ofArrows (fun () ↦ S') (fun _ ↦ φ)
    · apply this
      apply Coverage.saturate.of
      refine ⟨S', φ, rfl, ?_⟩
      rwa [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
    · intro S'' f' hf
      cases hf with
      | intro w h =>
        obtain ⟨_, _, hh⟩ := h
        cases hh.1
        rw [← hh.2]
        change _ ∈ (coherentTopology _).sieves _
        apply (coherentTopology _).pullback_stable
        apply this
        rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
        refine ⟨S', φ, ?_, ?_⟩
        · rwa [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
        · assumption
