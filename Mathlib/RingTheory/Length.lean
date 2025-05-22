/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
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

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

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

@[simp, nontriviality]
lemma Module.length_eq_zero [Subsingleton M] : Module.length R M = 0 :=
  Module.length_eq_zero_iff.mpr ‹_›

@[simp, nontriviality]
lemma Module.length_eq_zero_of_subsingleton_ring [Subsingleton R] : Module.length R M = 0 :=
  have := Module.subsingleton R M
  Module.length_eq_zero

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
    have h' : t'.length = s.length := by simpa using Fintype.card_congr this.symm
    simpa using h.trans h'.le

lemma Module.length_eq_top_iff_infiniteDimensionalOrder :
    length R M = ⊤ ↔ InfiniteDimensionalOrder (Submodule R M) := by
  rw [← WithBot.coe_inj, WithBot.coe_top, coe_length, Order.krullDim_eq_top_iff,
      ← not_finiteDimensionalOrder_iff]

lemma Module.length_ne_top_iff_finiteDimensionalOrder :
    length R M ≠ ⊤ ↔ FiniteDimensionalOrder (Submodule R M) := by
  rw [Ne, length_eq_top_iff_infiniteDimensionalOrder, ← not_finiteDimensionalOrder_iff, not_not]

lemma Module.length_ne_top_iff : Module.length R M ≠ ⊤ ↔ IsFiniteLength R M := by
  refine ⟨fun h ↦ ?_, fun H ↦ ?_⟩
  · rw [length_ne_top_iff_finiteDimensionalOrder] at h
    rw [isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, isArtinian_iff]
    exact ⟨Rel.wellFounded_swap_of_finiteDimensional _, Rel.wellFounded_of_finiteDimensional _⟩
  · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp H
    rw [← length_compositionSeries s hs₁ hs₂]
    simp

lemma Module.length_ne_top [IsArtinian R M] [IsNoetherian R M] : Module.length R M ≠ ⊤ := by
  rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
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

lemma Module.length_bot :
    Module.length R (⊥ : Submodule R M) = 0 :=
  Module.length_eq_zero

@[simp] lemma Module.length_top :
    Module.length R (⊤ : Submodule R M) = Module.length R M := by
  rw [Module.length_submodule, Module.length_eq_height]

lemma Submodule.height_lt_top [IsArtinian R M] [IsNoetherian R M] (N : Submodule R M) :
    Order.height N < ⊤ := by
  simpa only [← Module.length_submodule] using Module.length_ne_top.lt_top

lemma Submodule.height_strictMono [IsArtinian R M] [IsNoetherian R M] :
    StrictMono (Order.height : Submodule R M → ℕ∞) :=
  fun N _ h ↦ Order.height_strictMono h N.height_lt_top

lemma Submodule.length_lt [IsArtinian R M] [IsNoetherian R M] {N : Submodule R M} (h : N ≠ ⊤) :
    Module.length R N < Module.length R M := by
  simpa [← Module.length_top (M := M), Module.length_submodule] using height_strictMono h.lt_top

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
      let r := t'.smash s' (by simpa [s', t', hs₁, ht₂] using hfg)
      rw [← Module.length_compositionSeries s hs₁ hs₂,
        ← Module.length_compositionSeries t ht₁ ht₂,
        ← Module.length_compositionSeries r
          (by simpa [r, t', ht₁, -Submodule.map_bot] using Submodule.map_bot f)
          (by simpa [r, s', hs₂, -Submodule.comap_top] using Submodule.comap_top g)]
      simp_rw [r, RelSeries.smash_length, Nat.cast_add, s', t', RelSeries.map_length]
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

variable (R M N) in
@[simp]
lemma Module.length_prod :
    Module.length R (M × N) = Module.length R M + Module.length R N :=
  Module.length_eq_add_of_exact _ _ LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

variable (R) in
@[simp]
lemma Module.length_pi_of_fintype : ∀ {ι : Type*} [Fintype ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
    Module.length R (Π i, M i) = ∑ i, Module.length R (M i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq, IH, e.sum_comp (length R <| M ·)]
  · intro M _ _
    simp [Module.length_eq_zero]
  · intro ι _ IH M _ _
    rw [(LinearEquiv.piOptionEquivProd _).length_eq, Module.length_prod, IH, add_comm,
      Fintype.sum_option, add_comm]

@[simp]
lemma Module.length_finsupp {ι : Type*} :
    Module.length R (ι →₀ M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp [(Finsupp.linearEquivFunOnFinite R M ι).length_eq]
  nontriviality M
  rw [ENat.card_eq_top_of_infinite, ENat.top_mul length_pos.ne', ENat.eq_top_iff_forall_ge]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι m
  have : length R (s →₀ M) = ↑m * length R M := by
    simp [(Finsupp.linearEquivFunOnFinite R M _).length_eq, hs]
  refine le_trans ?_ (Module.length_le_of_injective (Finsupp.lmapDomain M R ((↑) : s → ι))
    (Finsupp.mapDomain_injective Subtype.val_injective))
  rw [this]
  exact ENat.self_le_mul_right _ length_pos.ne'

@[simp]
lemma Module.length_pi {ι : Type*} :
    Module.length R (ι → M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp
  nontriviality M
  rw [ENat.card_eq_top_of_infinite, ENat.top_mul length_pos.ne', ← top_le_iff]
  refine le_trans ?_ (Module.length_le_of_injective Finsupp.lcoeFun DFunLike.coe_injective)
  simp [ENat.top_mul length_pos.ne']

attribute [nontriviality] rank_subsingleton'

variable (R M) in
lemma Module.length_of_free [Module.Free R M] :
    Module.length R M = (Module.rank R M).toENat * Module.length R R := by
  let b := Module.Free.chooseBasis R M
  nontriviality R
  nontriviality M
  by_cases H : Module.length R R = ⊤
  · rw [b.repr.length_eq, Module.length_finsupp, H, ENat.mul_top', ENat.mul_top']
    congr 1
    simp [ENat.card_eq_zero_iff_empty, rank_pos_of_free.ne']
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at H
  cases H
  let b := Module.Free.chooseBasis R M
  rw [b.repr.length_eq, Module.length_finsupp, Free.rank_eq_card_chooseBasisIndex, ENat.card]

variable (R M) in
lemma Module.length_of_free_of_finite
    [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.length R M = Module.finrank R M * Module.length R R := by
  rw [length_of_free, Cardinal.toENat_eq_nat.mpr (finrank_eq_rank _ _).symm]

lemma Module.length_eq_one_iff :
    Module.length R M = 1 ↔ IsSimpleModule R M := by
  rw [← WithBot.coe_inj, Module.coe_length, WithBot.coe_one,
    Order.krullDim_eq_one_iff_of_boundedOrder]

variable (R M) in
@[simp]
lemma Module.length_eq_one [IsSimpleModule R M] :
    Module.length R M = 1 :=
  Module.length_eq_one_iff.mpr ‹_›

lemma Module.length_eq_rank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] :
    Module.length K M = (Module.rank K M).toENat := by
  simp [Module.length_of_free]

lemma Module.length_eq_finrank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] [Module.Finite K M] :
    Module.length K M = Module.finrank K M := by
  simp [Module.length_of_free]
