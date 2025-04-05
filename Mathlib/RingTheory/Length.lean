/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Exact
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.FiniteLength

/-!

# Length of modules

## Main results
- `Module.length`: `Module.length R M` is the length of `M` as an `R`-module.
- `Module.length_pos`: The length of a nontrivial module is positive
- `Module.length_ne_top`: The length of an artinian and noetherian module is finite.
- `Module.length_eq_add_of_exact`: Length is additive in exact sequences.

-/

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The length of a module, defined as the krull dimension of its submodule lattice. -/
noncomputable
def Module.length : ℕ∞ :=
  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

lemma Module.coe_length :
    (Module.length R M : WithBot ℕ∞) = Order.krullDim (Submodule R M) :=
  WithBot.coe_unbot _ _

lemma Module.length_eq_height : Module.length R M = Order.height (⊤ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.height_top_eq_krullDim]

lemma Module.length_eq_coheight : Module.length R M = Order.coheight (⊥ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.coheight_bot_eq_krullDim]

variable {R M}

lemma Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M := by
  rw [← WithBot.coe_inj, Module.coe_length, WithBot.coe_zero,
    Order.krullDim_eq_zero_iff_of_orderTop, Submodule.subsingleton_iff]

@[nontriviality]
lemma Module.length_eq_zero [Subsingleton M] : Module.length R M = 0 :=
  Module.length_eq_zero_iff.mpr ‹_›

lemma Module.length_pos_iff : 0 < Module.length R M ↔ Nontrivial M := by
  rw [pos_iff_ne_zero, ne_eq, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]

lemma Module.length_pos [Nontrivial M] : 0 < Module.length R M :=
  Module.length_pos_iff.mpr ‹_›

lemma Module.length_compositionSeries (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥)
    (h₂ : s.last = ⊤) : s.length = Module.length R M := by
  have H := isFiniteLength_of_exists_compositionSeries ⟨s, h₁, h₂⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).2
  rw [← WithBot.coe_inj, Module.coe_length]
  apply le_antisymm
  · let s' := s.map (β := Submodule R M) (s := (· < ·)) ⟨id, fun h ↦ h.1⟩
    exact (Order.LTSeries.length_le_krullDim s')
  · rw [Order.krullDim, iSup_le_iff]
    intro t
    refine WithBot.coe_le_coe.mpr ?_
    obtain ⟨t', i, hi, ht₁, ht₂⟩ := t.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
    have := (s.jordan_holder t' (h₁.trans ht₁.symm) (h₂.trans ht₂.symm)).choose
    have h : t.length ≤ t'.length := by simpa using Fintype.card_le_of_embedding i
    have h' : t'.length = s.length := by simpa using (Fintype.card_congr this.symm)
    simpa using h.trans h'.le

lemma Module.length_ne_top_iff : Module.length R M ≠ ⊤ ↔ IsFiniteLength R M := by
  constructor
  · nontriviality M
    cases finiteDimensionalOrder_or_infiniteDimensionalOrder (Submodule R M)
    · intro _
      rw [isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, isArtinian_iff]
      exact ⟨Rel.wellFounded_swap_of_finiteDimensional _, Rel.wellFounded_of_finiteDimensional _⟩
    · rw [ne_eq, ← WithBot.coe_inj, Module.coe_length, WithBot.coe_top, Order.krullDim_eq_top]
      simp only [not_true_eq_false, IsEmpty.forall_iff]
  · intro H
    obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp H
    rw [← length_compositionSeries s hs₁ hs₂]
    simp

lemma Module.length_ne_top [IsArtinian R M] [IsNoetherian R M] : Module.length R M ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨‹_›, ‹_›⟩

lemma Module.length_submodule {N : Submodule R M} :
    Module.length R N = Order.height N := by
  apply WithBot.coe_injective
  rw [Order.height_eq_krullDim_Iic, coe_length, Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]

lemma Module.length_quotient {N : Submodule R M} :
    Module.length R (M ⧸ N) = Order.coheight N := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici, coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]

lemma LinearEquiv.length_eq {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

@[simp] lemma Module.length_bot :
    Module.length R (⊥ : Submodule R M) = 0 :=
  Module.length_eq_zero

@[simp] lemma Module.length_top :
    Module.length R (⊤ : Submodule R M) = Module.length R M := by
  rw [Module.length_submodule, Module.length_eq_height]

variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
variable (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
variable (H : Function.Exact f g)

include hf hg H in
/-- Length is additive in exact sequences. -/
lemma Module.length_eq_add_of_exact :
    Module.length R M = Module.length R N + Module.length R P := by
  by_cases hP : IsFiniteLength R P
  · by_cases hN : IsFiniteLength R N
    · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
      obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
      let s' : CompositionSeries (Submodule R M) :=
        s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
      let t' : CompositionSeries (Submodule R M) :=
        t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
      have hfg : Submodule.map f ⊤ = Submodule.comap g ⊥ := by
        rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
      let r := t'.smash s' (by simpa [s', t', hs₁, ht₂])
      rw [← Module.length_compositionSeries s hs₁ hs₂,
        ← Module.length_compositionSeries t ht₁ ht₂,
        ← Module.length_compositionSeries r
          (by simpa [r, t', ht₁, -Submodule.map_bot] using Submodule.map_bot f)
          (by simpa [r, s', hs₂, -Submodule.comap_top] using Submodule.comap_top g)]
      rfl
    · have := mt (IsFiniteLength.of_injective · hf) hN
      rw [← Module.length_ne_top_iff, ne_eq, not_not] at hN this
      rw [hN, this, top_add]
  · have := mt (IsFiniteLength.of_surjective · hg) hP
    rw [← Module.length_ne_top_iff, ne_eq, not_not] at hP this
    rw [hP, this, add_top]

include hf in
lemma Module.length_le_of_injective : Module.length R N ≤ Module.length R M := by
  rw [Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact le_self_add

include hg in
lemma Module.length_le_of_surjective : Module.length R P ≤ Module.length R M := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact le_add_self
