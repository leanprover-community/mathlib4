/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Defs.Sequences
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Sequences in topological spaces

In this file we prove theorems about relations
between closure/compactness/continuity etc and their sequential counterparts.

## Main definitions

The following notions are defined in `Topology/Defs/Sequences`.
We build theory about these definitions here, so we remind the definitions.

### Set operation
* `seqClosure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `IsSeqClosed s`: predicate saying that a set is sequentially closed, i.e., `seqClosure s ⊆ s`;
* `SeqContinuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `IsSeqCompact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `FrechetUrysohnSpace X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `SequentialSpace X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `SeqCompactSpace X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seqClosure_subset_closure`: closure of a set includes its sequential closure;
* `IsClosed.isSeqClosed`: a closed set is sequentially closed;
* `IsSeqClosed.seqClosure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seqClosure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `FirstCountableTopology.frechetUrysohnSpace`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `FrechetUrysohnSpace.to_sequentialSpace`: every Fréchet-Urysohn space is a sequential space;
* `IsSeqCompact.isCompact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/


open Set Function Filter TopologicalSpace Bornology
open scoped Topology Uniformity

variable {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/

section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem subset_seqClosure {s : Set X} : s ⊆ seqClosure s := fun p hp =>
  ⟨const ℕ p, fun _ => hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem seqClosure_subset_closure {s : Set X} : seqClosure s ⊆ closure s := fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

/-- The sequential closure of a sequentially closed set is the set itself. -/
theorem IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s = s :=
  Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure

/-- If a set is equal to its sequential closure, then it is sequentially closed. -/
theorem isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqClosed s :=
  fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩

/-- A set is sequentially closed iff it is equal to its sequential closure. -/
theorem isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s :=
  ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩

/-- A set is sequentially closed if it is closed. -/
protected theorem IsClosed.isSeqClosed {s : Set X} (hc : IsClosed s) : IsSeqClosed s :=
  fun _u _x hu hx => hc.mem_of_tendsto hx (eventually_of_forall hu)

theorem seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s = closure s :=
  seqClosure_subset_closure.antisymm <| FrechetUrysohnSpace.closure_subset_seqClosure s

/-- In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a limit
of a sequence taking values in this set. -/
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) := by
  rw [← seqClosure_eq_closure]
  rfl

/-- If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then convergence
is equivalent to sequential convergence. See also `Filter.tendsto_iff_seq_tendsto` for a version
that works for any pair of filters assuming that the filter in the domain is countably generated.

This property is equivalent to the definition of `FrechetUrysohnSpace`, see
`FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`. -/
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b) := by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (eventually_of_forall hus)

/-- An alternative construction for `FrechetUrysohnSpace`: if sequential convergence implies
convergence, then the space is a Fréchet-Urysohn space. -/
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h : ∀ (f : X → Prop) (a : X),
      (∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 (f a))) → ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x ∈ s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ ∃ᶠ x in atTop, u x ∈ s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← mem_closure_iff_frequently, hcx, imp_false, not_forall, not_not, not_false_eq_true,
        not_true_eq_false] using h (· ∉ s) x
    rcases extraction_of_frequently_atTop hus with ⟨φ, φ_mono, hφ⟩
    exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_atTop⟩

-- see Note [lower instance priority]
/-- Every first-countable space is a Fréchet-Urysohn space. -/
instance (priority := 100) FirstCountableTopology.frechetUrysohnSpace
    [FirstCountableTopology X] : FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun _ _ => tendsto_iff_seq_tendsto.2

-- see Note [lower instance priority]
/-- Every Fréchet-Urysohn space is a sequential space. -/
instance (priority := 100) FrechetUrysohnSpace.to_sequentialSpace [FrechetUrysohnSpace X] :
    SequentialSpace X :=
  ⟨fun s hs => by rw [← closure_eq_iff_isClosed, ← seqClosure_eq_closure, hs.seqClosure_eq]⟩

theorem Inducing.frechetUrysohnSpace [FrechetUrysohnSpace Y] {f : X → Y} (hf : Inducing f) :
    FrechetUrysohnSpace X := by
  refine ⟨fun s x hx ↦ ?_⟩
  rw [hf.closure_eq_preimage_closure_image, mem_preimage, mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, (· ∘ ·), hvu]

/-- Subtype of a Fréchet-Urysohn space is a Fréchet-Urysohn space. -/
instance Subtype.instFrechetUrysohnSpace [FrechetUrysohnSpace X] {p : X → Prop} :
    FrechetUrysohnSpace (Subtype p) :=
  inducing_subtype_val.frechetUrysohnSpace

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
theorem IsSeqClosed.preimage {f : X → Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun _x _p hx hp => hs hx (hf hp)

-- A continuous function is sequentially continuous.
protected theorem Continuous.seqContinuous {f : X → Y} (hf : Continuous f) : SeqContinuous f :=
  fun _x p hx => (hf.tendsto p).comp hx

/-- A sequentially continuous function defined on a sequential space is continuous. -/
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
theorem continuous_iff_seqContinuous [SequentialSpace X] {f : X → Y} :
    Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩

theorem SequentialSpace.coinduced [SequentialSpace X] (f : X → Y) :
    @SequentialSpace Y (.coinduced f ‹_›) :=
  letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun s hs ↦ isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩

protected theorem SequentialSpace.iSup {ι : Sort*} {t : ι → TopologicalSpace X}
    (h : ∀ i, @SequentialSpace X (t i)) : @SequentialSpace X (⨆ i, t i) := by
  letI : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs ↦ isClosed_iSup_iff.2 fun i ↦ ?_⟩
  letI := t i
  exact IsSeqClosed.isClosed fun u x hus hux ↦ hs hus <| hux.mono_right <| nhds_mono <| le_iSup _ _

protected theorem SequentialSpace.sup {t₁ t₂ : TopologicalSpace X}
    (h₁ : @SequentialSpace X t₁) (h₂ : @SequentialSpace X t₂) :
    @SequentialSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
  exact .iSup <| Bool.forall_bool.2 ⟨h₂, h₁⟩

theorem QuotientMap.sequentialSpace [SequentialSpace X] {f : X → Y} (hf : QuotientMap f) :
    SequentialSpace Y :=
  hf.2.symm ▸ .coinduced f

/-- The quotient of a sequential space is a sequential space. -/
instance Quotient.instSequentialSpace [SequentialSpace X] {s : Setoid X} :
    SequentialSpace (Quotient s) :=
  quotientMap_quot_mk.sequentialSpace

/-- The sum (disjoint union) of two sequential spaces is a sequential space. -/
instance Sum.instSequentialSpace [SequentialSpace X] [SequentialSpace Y] :
    SequentialSpace (X ⊕ Y) :=
  .sup (.coinduced Sum.inl) (.coinduced Sum.inr)

/-- The disjoint union of an indexed family of sequential spaces is a sequential space. -/
instance Sigma.instSequentialSpace {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, SequentialSpace (X i)] : SequentialSpace (Σ i, X i) :=
  .iSup fun _ ↦ .coinduced _

end TopologicalSpace

section SeqCompact

open TopologicalSpace FirstCountableTopology

variable [TopologicalSpace X]

theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := seq_compact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology X]

open FirstCountableTopology

protected theorem IsCompact.isSeqCompact {s : Set X} (hs : IsCompact s) : IsSeqCompact s :=
  fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (eventually_of_forall x_in))
  ⟨a, a_in, tendsto_subseq ha⟩

theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s)
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact.subseq_of_frequently_in hx

theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact hx

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] :
    SeqCompactSpace X :=
  ⟨isCompact_univ.isSeqCompact⟩

theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) :
    ∃ (a : _) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x

end FirstCountableTopology

section Image

/-- Sequential compactness of sets is preserved under sequentially continuous functions. -/
theorem IsSeqCompact.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using fun n ↦ (ys_in_fK n)
  simp only [Set.mem_image, exists_exists_and_eq_and]
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨a, a_in_K, phi, phi_mono, ?_⟩
  exact Filter.Tendsto.congr (fun x ↦ fxs_eq_ys (phi x)) (f_cont xs_phi_lim)

/-- The range of sequentially continuous function on a sequentially compact space is sequentially
compact. -/
theorem isSeqCompact_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SeqCompactSpace X] (f : X → Y) (hf : SeqContinuous f) :
    IsSeqCompact (Set.range f) := by
  rw [← Set.image_univ]
  exact IsSeqCompact.image f hf ((seqCompactSpace_iff X).mp ‹SeqCompactSpace X›)

/-- Sequential compactness of sets is preserved under continuous functions. -/
theorem IsSeqCompact.image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (f_cont : Continuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) :=
  IsSeqCompact.image f (Continuous.seqContinuous f_cont) K_cpt

/-- The range of continuous function on a sequentially compact space is sequentially compact. -/
theorem SeqCompactSpace.range_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SeqCompactSpace X] (f : X → Y) (f_cont : Continuous f) :
    IsSeqCompact (Set.range f) :=
  isSeqCompact_range f (Continuous.seqContinuous f_cont)

end Image

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

theorem IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : ℕ → X}
    (hu : ∃ᶠ n in atTop, u n ∈ s) (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩

theorem IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s)
    (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  hs.exists_tendsto_of_frequently_mem (frequently_of_forall hu) huc

/-- A sequentially compact set in a uniform space is totally bounded. -/
protected theorem IsSeqCompact.totallyBounded (h : IsSeqCompact s) : TotallyBounded s := by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using seq_of_forall_finite_exists h
  refine ⟨u, u_in, fun x _ φ hφ huφ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    huφ.cauchySeq.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)

variable [IsCountablyGenerated (𝓤 X)]

/-- A sequentially compact set in a uniform set with countably generated uniformity filter
is complete. -/
protected theorem IsSeqCompact.isComplete (hs : IsSeqCompact s) : IsComplete s := fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : ∀ n, W n ⊆ V n := fun n ⟨x, y⟩ hx =>
    @hWV n (x, y) ⟨x, refl_mem_uniformity <| hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩ :
      ∃ t : ℕ → Set X, Antitone t ∧ (∀ n, t n ∈ l) ∧ (∀ n, t n ×ˢ t n ⊆ W n) ∧ ∀ n, t n ⊆ s := by
    have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ⊆ s := by
      rw [le_principal_iff] at hls
      have : ∀ n, W n ∩ s ×ˢ s ∈ l ×ˢ l := fun n => inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls)
      simpa only [l.basis_sets.prod_self.mem_iff, true_imp_iff, subset_inter_iff,
        prod_self_subset_prod_self, and_assoc] using this
    choose t htl htW hts using this
    have : ∀ n : ℕ, ⋂ k ≤ n, t k ⊆ t n := fun n => by apply iInter₂_subset; rfl
    exact ⟨fun n => ⋂ k ≤ n, t k, fun m n h =>
      biInter_subset_biInter_left fun k (hk : k ≤ m) => hk.trans h, fun n =>
      (biInter_mem (finite_le_nat n)).2 fun k _ => htl k, fun n =>
      (prod_mono (this n) (this n)).trans (htW n), fun n => (this n).trans (hts n)⟩
  choose u hu using fun n => Filter.nonempty_of_mem (htl n)
  have huc : CauchySeq u := hV.toHasBasis.cauchySeq_iff.2 fun N _ =>
      ⟨N, fun m hm n hn => hWV' _ <| @htW N (_, _) ⟨ht_anti hm (hu _), ht_anti hn (hu _)⟩⟩
  rcases hs.exists_tendsto (fun n => hts n (hu n)) huc with ⟨x, hxs, hx⟩
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.toHasBasis).ge_iff.2 fun N _ => ?_⟩
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N) :=
    ((eventually_ge_atTop N).and (hx <| ball_mem_nhds x (hW N))).exists
  refine mem_of_superset (htl n) fun y hy => hWV N ⟨u n, hn, htW N ?_⟩
  exact ⟨ht_anti hNn (hu n), ht_anti hNn hy⟩

/-- If `𝓤 β` is countably generated, then any sequentially compact set is compact. -/
protected theorem IsSeqCompact.isCompact (hs : IsSeqCompact s) : IsCompact s :=
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩

/-- A version of Bolzano-Weierstrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected theorem UniformSpace.isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩

theorem UniformSpace.compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X := by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, UniformSpace.isCompact_iff_isSeqCompact]

end UniformSpaceSeqCompact
