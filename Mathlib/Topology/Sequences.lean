/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov

! This file was ported from Lean 3 source module topology.sequences
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.MetricSpace.Basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology.

## Main definitions

### Set operation
* `seq_closure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `is_seq_closed s`: predicate saying that a set is sequentially closed, i.e., `seq_closure s ⊆ s`;
* `seq_continuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `is_seq_compact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `frechet_urysohn_space X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `sequential_space X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `seq_compact_space X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seq_closure_subset_closure`: closure of a set includes its sequential closure;
* `is_closed.is_seq_closed`: a closed set is sequentially closed;
* `is_seq_closed.seq_closure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seq_closure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `frechet_urysohn_space.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `topological_space.first_countable_topology.frechet_urysohn_space`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `frechet_urysohn_space.to_sequential_space`: every Fréchet-Urysohn space is a sequential space;
* `is_seq_compact.is_compact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/


open Set Function Filter TopologicalSpace

open Topology Filter

variable {X Y : Type _}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/


section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is the set of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a set is not
guaranteed to be sequentially closed. -/
def seqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) }
#align seq_closure seqClosure

theorem subset_seqClosure {s : Set X} : s ⊆ seqClosure s := fun p hp =>
  ⟨const ℕ p, fun _ => hp, tendsto_const_nhds⟩
#align subset_seq_closure subset_seqClosure

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem seqClosure_subset_closure {s : Set X} : seqClosure s ⊆ closure s := fun p ⟨x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)
#align seq_closure_subset_closure seqClosure_subset_closure

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not guaranteed to be
sequentially closed. -/
def IsSeqClosed (s : Set X) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → Tendsto x atTop (𝓝 p) → p ∈ s
#align is_seq_closed IsSeqClosed

/-- The sequential closure of a sequentially closed set is the set itself. -/
theorem IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s = s :=
  Subset.antisymm (fun p ⟨x, hx, hp⟩ => hs hx hp) subset_seqClosure
#align is_seq_closed.seq_closure_eq IsSeqClosed.seqClosure_eq

/-- If a set is equal to its sequential closure, then it is sequentially closed. -/
theorem isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqClosed s :=
  fun x p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩
#align is_seq_closed_of_seq_closure_eq isSeqClosed_of_seqClosure_eq

/-- A set is sequentially closed iff it is equal to its sequential closure. -/
theorem isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s :=
  ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩
#align is_seq_closed_iff isSeqClosed_iff

/-- A set is sequentially closed if it is closed. -/
protected theorem IsClosed.isSeqClosed {s : Set X} (hc : IsClosed s) : IsSeqClosed s :=
  fun u x hu hx => hc.mem_of_tendsto hx (eventually_of_forall hu)
#align is_closed.is_seq_closed IsClosed.isSeqClosed

/-- A topological space is called a *Fréchet-Urysohn space*, if the sequential closure of any set
is equal to its closure. Since one of the inclusions is trivial, we require only the non-trivial one
in the definition. -/
class FrechetUrysohnSpace (X : Type _) [TopologicalSpace X] : Prop where
  closure_subset_seqClosure : ∀ s : Set X, closure s ⊆ seqClosure s
#align frechet_urysohn_space FrechetUrysohnSpace

theorem seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s = closure s :=
  seqClosure_subset_closure.antisymm <| FrechetUrysohnSpace.closure_subset_seqClosure s
#align seq_closure_eq_closure seqClosure_eq_closure

/-- In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a limit
of a sequence taking values in this set. -/
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) :=
  by
  rw [← seqClosure_eq_closure]
  rfl
#align mem_closure_iff_seq_limit mem_closure_iff_seq_limit

/-- If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then convergence
is equivalent to sequential convergence. See also `filter.tendsto_iff_seq_tendsto` for a version
that works for any pair of filters assuming that the filter in the domain is countably generated.

This property is equivalent to the definition of `frechet_urysohn_space`, see
`frechet_urysohn_space.of_seq_tendsto_imp_tendsto`. -/
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b) :=
  by
  refine'
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iffₓ (nhds_basis_closeds _)).2 _⟩
  rintro s ⟨hbs, hsc⟩
  refine' ⟨closure (f ⁻¹' s), ⟨mt _ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (eventually_of_forall hus)
#align tendsto_nhds_iff_seq_tendsto tendsto_nhds_iff_seq_tendsto

/-- An alternative construction for `frechet_urysohn_space`: if sequential convergence implies
convergence, then the space is a Fréchet-Urysohn space. -/
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h :
      ∀ (f : X → Prop) (a : X),
        (∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 (f a))) → ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine' ⟨fun s x hcx => _⟩
  specialize h (· ∉ s) x
  by_cases hx : x ∈ s; · exact subset_seqClosure hx
  simp_rw [(· ∘ ·), ContinuousAt, hx, not_false_iff, nhds_true, tendsto_pure, eq_true_iff, ←
    mem_compl_iff, eventually_mem_set, ← mem_interior_iff_mem_nhds, interior_compl] at h
  rw [mem_compl_iff, imp_not_comm] at h
  simp only [not_forall, not_eventually, mem_compl_iff, Classical.not_not] at h
  rcases h hcx with ⟨u, hux, hus⟩
  rcases extraction_of_frequently_at_top hus with ⟨φ, φ_mono, hφ⟩
  exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_at_top⟩
#align frechet_urysohn_space.of_seq_tendsto_imp_tendsto FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto

-- see Note [lower instance priority]
/-- Every first-countable space is a Fréchet-Urysohn space. -/
instance (priority := 100) TopologicalSpace.FirstCountableTopology.frechetUrysohnSpace
    [FirstCountableTopology X] : FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun f a => tendsto_iff_seq_tendsto.2
#align topological_space.first_countable_topology.frechet_urysohn_space TopologicalSpace.FirstCountableTopology.frechetUrysohnSpace

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
class SequentialSpace (X : Type _) [TopologicalSpace X] : Prop where
  isClosed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s
#align sequential_space SequentialSpace

-- see Note [lower instance priority]
/-- Every Fréchet-Urysohn space is a sequential space. -/
instance (priority := 100) FrechetUrysohnSpace.to_sequentialSpace [FrechetUrysohnSpace X] :
    SequentialSpace X :=
  ⟨fun s hs => by rw [← closure_eq_iff_isClosed, ← seqClosure_eq_closure, hs.seq_closure_eq]⟩
#align frechet_urysohn_space.to_sequential_space FrechetUrysohnSpace.to_sequentialSpace

/-- In a sequential space, a sequentially closed set is closed. -/
protected theorem IsSeqClosed.isClosed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) :
    IsClosed s :=
  SequentialSpace.isClosed_of_seq s hs
#align is_seq_closed.is_closed IsSeqClosed.isClosed

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩
#align is_seq_closed_iff_is_closed isSeqClosed_iff_isClosed

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SeqContinuous (f : X → Y) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) → Tendsto (f ∘ x) atTop (𝓝 (f p))
#align seq_continuous SeqContinuous

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
theorem IsSeqClosed.preimage {f : X → Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun x p hx hp => hs hx (hf hp)
#align is_seq_closed.preimage IsSeqClosed.preimage

-- A continuous function is sequentially continuous.
protected theorem Continuous.seqContinuous {f : X → Y} (hf : Continuous f) : SeqContinuous f :=
  fun x p hx => (hf.Tendsto p).comp hx
#align continuous.seq_continuous Continuous.seqContinuous

/-- A sequentially continuous function defined on a sequential space is continuous. -/
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun s hs => (hs.IsSeqClosed.Preimage hf).IsClosed
#align seq_continuous.continuous SeqContinuous.continuous

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
theorem continuous_iff_seqContinuous [SequentialSpace X] {f : X → Y} :
    Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩
#align continuous_iff_seq_continuous continuous_iff_seqContinuous

theorem QuotientMap.sequentialSpace [SequentialSpace X] {f : X → Y} (hf : QuotientMap f) :
    SequentialSpace Y :=
  ⟨fun s hs => hf.isClosed_preimage.mp <| (hs.Preimage <| hf.Continuous.SeqContinuous).IsClosed⟩
#align quotient_map.sequential_space QuotientMap.sequentialSpace

/-- The quotient of a sequential space is a sequential space. -/
instance [SequentialSpace X] {s : Setoid X} : SequentialSpace (Quotient s) :=
  quotientMap_quot_mk.SequentialSpace

end TopologicalSpace

section SeqCompact

open TopologicalSpace TopologicalSpace.FirstCountableTopology

variable [TopologicalSpace X]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
#align is_seq_compact IsSeqCompact

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
@[mk_iff]
class SeqCompactSpace (X : Type _) [TopologicalSpace X] : Prop where
  seq_compact_univ : IsSeqCompact (univ : Set X)
#align seq_compact_space SeqCompactSpace

export SeqCompactSpace (seq_compact_univ)

theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩
#align is_seq_compact.subseq_of_frequently_in IsSeqCompact.subseq_of_frequently_in

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := seq_compact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩
#align seq_compact_space.tendsto_subseq SeqCompactSpace.tendsto_subseq

section FirstCountableTopology

variable [FirstCountableTopology X]

open TopologicalSpace.FirstCountableTopology

protected theorem IsCompact.isSeqCompact {s : Set X} (hs : IsCompact s) : IsSeqCompact s :=
  fun x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (eventually_of_forall x_in))
  ⟨a, a_in, tendsto_subseq ha⟩
#align is_compact.is_seq_compact IsCompact.isSeqCompact

theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s)
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.IsSeqCompact.subseq_of_frequently_in hx
#align is_compact.tendsto_subseq' IsCompact.tendsto_subseq'

theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.IsSeqCompact hx
#align is_compact.tendsto_subseq IsCompact.tendsto_subseq

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] :
    SeqCompactSpace X :=
  ⟨isCompact_univ.IsSeqCompact⟩
#align first_countable_topology.seq_compact_of_compact FirstCountableTopology.seq_compact_of_compact

theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) :
    ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x
#align compact_space.tendsto_subseq CompactSpace.tendsto_subseq

end FirstCountableTopology

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

theorem IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : ℕ → X}
    (hu : ∃ᶠ n in atTop, u n ∈ s) (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  let ⟨x, hxs, φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩
#align is_seq_compact.exists_tendsto_of_frequently_mem IsSeqCompact.exists_tendsto_of_frequently_mem

theorem IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s)
    (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  hs.exists_tendsto_of_frequently_mem (frequently_of_forall hu) huc
#align is_seq_compact.exists_tendsto IsSeqCompact.exists_tendsto

/-- A sequentially compact set in a uniform space is totally bounded. -/
protected theorem IsSeqCompact.totallyBounded (h : IsSeqCompact s) : TotallyBounded s :=
  by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V :=
    by
    simp only [not_subset, mem_Union₂, not_exists, exists_prop] at h
    simpa only [forall_and, ball_image_iff, not_and] using seq_of_forall_finite_exists h
  refine' ⟨u, u_in, fun x x_in φ hφ huφ => _⟩
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V
  exact huφ.cauchy_seq.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)
#align is_seq_compact.totally_bounded IsSeqCompact.totallyBounded

variable [IsCountablyGenerated (𝓤 X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A sequentially compact set in a uniform set with countably generated uniformity filter
is complete. -/
protected theorem IsSeqCompact.isComplete (hs : IsSeqCompact s) : IsComplete s :=
  by
  intro l hl hls
  haveI := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : ∀ n, W n ⊆ V n := fun n ⟨x, y⟩ hx =>
    @hWV n (x, y) ⟨x, refl_mem_uniformity <| hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩ :
    ∃ t : ℕ → Set X, Antitone t ∧ (∀ n, t n ∈ l) ∧ (∀ n, t n ×ˢ t n ⊆ W n) ∧ ∀ n, t n ⊆ s :=
    by
    have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ⊆ s :=
      by
      rw [le_principal_iff] at hls
      have : ∀ n, W n ∩ s ×ˢ s ∈ l ×ᶠ l := fun n => inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls)
      simpa only [l.basis_sets.prod_self.mem_iff, true_imp_iff, subset_inter_iff,
        prod_self_subset_prod_self, and_assoc] using this
    choose t htl htW hts
    have : ∀ n, (⋂ k ≤ n, t k) ⊆ t n := fun n => Inter₂_subset _ le_rfl
    exact
      ⟨fun n => ⋂ k ≤ n, t k, fun m n h =>
        bInter_subset_bInter_left fun k (hk : k ≤ m) => hk.trans h, fun n =>
        (bInter_mem (finite_le_nat n)).2 fun k hk => htl k, fun n =>
        (prod_mono (this n) (this n)).trans (htW n), fun n => (this n).trans (hts n)⟩
  choose u hu using fun n => Filter.nonempty_of_mem (htl n)
  have huc : CauchySeq u :=
    hV.to_has_basis.cauchy_seq_iff.2 fun N hN =>
      ⟨N, fun m hm n hn => hWV' _ <| @htW N (_, _) ⟨ht_anti hm (hu _), ht_anti hn (hu _)⟩⟩
  rcases hs.exists_tendsto (fun n => hts n (hu n)) huc with ⟨x, hxs, hx⟩
  refine' ⟨x, hxs, (nhds_basis_uniformity' hV.to_has_basis).ge_iff.2 fun N hN => _⟩
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N)
  exact ((eventually_ge_at_top N).And (hx <| ball_mem_nhds x (hW N))).exists
  refine' mem_of_superset (htl n) fun y hy => hWV N ⟨u n, _, htW N ⟨_, _⟩⟩
  exacts[hn, ht_anti hNn (hu n), ht_anti hNn hy]
#align is_seq_compact.is_complete IsSeqCompact.isComplete

/-- If `𝓤 β` is countably generated, then any sequentially compact set is compact. -/
protected theorem IsSeqCompact.isCompact (hs : IsSeqCompact s) : IsCompact s :=
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.TotallyBounded, hs.IsComplete⟩
#align is_seq_compact.is_compact IsSeqCompact.isCompact

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected theorem UniformSpace.isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.IsSeqCompact, fun H => H.IsCompact⟩
#align uniform_space.is_compact_iff_is_seq_compact UniformSpace.isCompact_iff_isSeqCompact

theorem UniformSpace.compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X := by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, UniformSpace.isCompact_iff_isSeqCompact]
#align uniform_space.compact_space_iff_seq_compact_space UniformSpace.compactSpace_iff_seqCompactSpace

end UniformSpaceSeqCompact

section MetricSeqCompact

variable [PseudoMetricSpace X]

open Metric

theorem SeqCompact.lebesgue_number_lemma_of_metric {ι : Sort _} {c : ι → Set X} {s : Set X}
    (hs : IsSeqCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ δ > 0, ∀ a ∈ s, ∃ i, ball a δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs.IsCompact hc₁ hc₂
#align seq_compact.lebesgue_number_lemma_of_metric SeqCompact.lebesgue_number_lemma_of_metric

variable [ProperSpace X] {s : Set X}

/-- A version of **Bolzano-Weistrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded (hs : Bounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.IsSeqCompact
  have hu' : ∃ᶠ n in atTop, x n ∈ closure s := hx.mono fun n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'
#align tendsto_subseq_of_frequently_bounded tendsto_subseq_of_frequently_bounded

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded (hs : Bounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| frequently_of_forall hx
#align tendsto_subseq_of_bounded tendsto_subseq_of_bounded

end MetricSeqCompact

