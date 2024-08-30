/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

Further results about extended metric spaces.
-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, edist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
      { rw [Nat.Ico_succ_right_eq_insert_Ico hle, Finset.sum_insert, add_comm]; simp }

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ => hd

namespace EMetric

theorem uniformInducing_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  uniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans <| by
      simp only [subset_def, Prod.forall]; rfl

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
nonrec theorem uniformEmbedding_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  (uniformEmbedding_iff _).trans <| and_comm.trans <| Iff.rfl.and uniformInducing_iff

/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`.

In fact, this lemma holds for a `UniformInducing` map.
TODO: generalize? -/
theorem controlled_of_uniformEmbedding [PseudoEMetricSpace β] {f : α → β} (h : UniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (uniformEmbedding_iff.1 h).2.2⟩

/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x, x ∈ t → ∀ y, y ∈ t → edist x y < ε := by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) →
      ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendstoLocallyUniformlyOn_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendstoUniformlyOn_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendstoLocallyUniformly_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, exists_prop, nhdsWithin_univ]

/-- Expressing uniform convergence using `edist`. -/
theorem tendstoUniformly_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

end EMetric

open EMetric

section Pi

open Finset

variable {π : β → Type*} [Fintype β]

-- Porting note: reordered instances
instance [∀ b, EDist (π b)] : EDist (∀ b, π b) where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)

theorem edist_pi_def [∀ b, EDist (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl

theorem edist_le_pi_edist [∀ b, EDist (π b)] (f g : ∀ b, π b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

theorem edist_pi_le_iff [∀ b, EDist (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]

theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl

@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun _ : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEMetricSpacePi [∀ b, PseudoEMetricSpace (π b)] : PseudoEMetricSpace (∀ b, π b) where
  edist_self f := bot_unique <| Finset.sup_le <| by simp
  edist_comm f g := by simp [edist_pi_def, edist_comm]
  edist_triangle f g h := edist_pi_le_iff.2 fun b => le_trans (edist_triangle _ (g b) _)
    (add_le_add (edist_le_pi_edist _ _ _) (edist_le_pi_edist _ _ _))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, PseudoEMetricSpace.uniformity_edist, comap_iInf, gt_iff_lt,
      preimage_setOf_eq, comap_principal, edist_pi_def]
    rw [iInf_comm]; congr; funext ε
    rw [iInf_comm]; congr; funext εpos
    simp [setOf_forall, εpos]

end Pi

namespace EMetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_lt_iff_le']

-- see Note [nolint_ge]
/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchySeq_iff'

theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩

theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩

section Compact

-- Porting note (#11215): TODO: generalize to metrizable spaces
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set. -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
  exact ⟨t, htf.countable, hst.trans <| iUnion₂_mono fun _ _ => ball_subset_closedBall⟩

end Compact

section SecondCountable

open TopologicalSpace

variable (α)

/-- A sigma compact pseudo emetric space has second countable topology. -/
instance (priority := 90) secondCountable_of_sigmaCompact [SigmaCompactSpace α] :
    SecondCountableTopology α := by
  suffices SeparableSpace α by exact UniformSpace.secondCountable_of_separable α
  choose T _ hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine ⟨⟨⋃ n, T n, countable_iUnion hTc, fun x => ?_⟩⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_iUnion _ n) (hsubT _ hn)

variable {α}

theorem secondCountable_of_almost_dense_set
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ ⋃ x ∈ t, closedBall x ε = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : ∀ ε > 0, ∃ t : Set α, Set.Countable t ∧ univ ⊆ ⋃ x ∈ t, closedBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

end SecondCountable

end EMetric

variable {γ : Type w} [EMetricSpace γ]

-- see Note [lower instance priority]
/-- An emetric space is separated -/
instance (priority := 100) EMetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_edist_eq_zero <| inseparable_iff.1 h

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem EMetric.uniformEmbedding_iff' [EMetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ := by
  rw [uniformEmbedding_iff_uniformInducing, uniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoEMetricSpace` is a T₀ space, then it is an `EMetricSpace`. -/
-- Porting note: made `reducible`;
-- Porting note (#11215): TODO: make it an instance?
abbrev EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  .ofT0PseudoEMetricSpace _

section Pi

open Finset

variable {π : β → Type*} [Fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetricSpacePi [∀ b, EMetricSpace (π b)] : EMetricSpace (∀ b, π b) :=
  .ofT0PseudoEMetricSpace _

end Pi

namespace EMetric

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s = closure t := by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

end EMetric

/-!
### Separation quotient
-/

instance [PseudoEMetricSpace X] : EDist (SeparationQuotient X) where
  edist := SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)

@[simp] theorem SeparationQuotient.edist_mk [PseudoEMetricSpace X] (x y : X) :
    edist (mk x) (mk y) = edist x y :=
  rfl

open SeparationQuotient in
instance [PseudoEMetricSpace X] : EMetricSpace (SeparationQuotient X) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
      uniformity_edist := comap_injective (surjective_mk.prodMap surjective_mk) <| by
        simp [comap_mk_uniformity, PseudoEMetricSpace.uniformity_edist] } _
