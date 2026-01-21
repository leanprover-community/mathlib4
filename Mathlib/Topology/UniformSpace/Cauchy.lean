/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Bases
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/

@[expose] public section

universe u v

open Filter Function TopologicalSpace Topology Set UniformSpace Uniformity
open scoped SetRel

variable {α : Type u} {β : Type v} [uniformSpace : UniformSpace α]

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x

theorem Filter.HasBasis.cauchy_iff {ι} {p : ι → Prop} {s : ι → SetRel α α} (h : (𝓤 α).HasBasis p s)
    {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ i, p i → ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s i :=
  and_congr Iff.rfl <|
    (f.basis_sets.prod_self.le_basis_iff h).trans <| by
      simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, id, forall_mem_comm]

theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

lemma cauchy_iff_le {l : Filter α} [hl : l.NeBot] :
    Cauchy l ↔ l ×ˢ l ≤ 𝓤 α := by
  simp only [Cauchy, hl, true_and]

theorem Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) :
    Cauchy (@Ultrafilter.of _ l h.1 : Filter α) := by
  haveI := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.neBot _, (Filter.prod_mono this this).trans h.2⟩

theorem cauchy_map_iff {l : Filter β} {f : β → α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) := by
  rw [Cauchy, map_neBot_iff, prod_map_map_eq, Tendsto]

theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β → α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α) :=
  cauchy_map_iff.trans <| and_iff_right hl

theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
  ⟨hg, le_trans (Filter.prod_mono h_le h_le) h_c.right⟩

theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (_ : NeBot g) (h_le : g ≤ f) : Cauchy g :=
  h_c.mono h_le

theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_neBot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)

theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β → α} {a : α}
    (h : Tendsto f l (𝓝 a)) : Cauchy (map f l) :=
  cauchy_nhds.mono h

lemma Cauchy.mono_uniformSpace {u v : UniformSpace β} {F : Filter β} (huv : u ≤ v)
    (hF : Cauchy (uniformSpace := u) F) : Cauchy (uniformSpace := v) F :=
  ⟨hF.1, hF.2.trans huv⟩

lemma cauchy_inf_uniformSpace {u v : UniformSpace β} {F : Filter β} :
    Cauchy (uniformSpace := u ⊓ v) F ↔
    Cauchy (uniformSpace := u) F ∧ Cauchy (uniformSpace := v) F := by
  unfold Cauchy
  rw [inf_uniformity (u := u), le_inf_iff, and_and_left]

lemma cauchy_iInf_uniformSpace {ι : Sort*} [Nonempty ι] {u : ι → UniformSpace β}
    {l : Filter β} :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  unfold Cauchy
  rw [iInf_uniformity, le_iInf_iff, forall_and, forall_const]

lemma cauchy_iInf_uniformSpace' {ι : Sort*} {u : ι → UniformSpace β}
    {l : Filter β} [l.NeBot] :
    Cauchy (uniformSpace := ⨅ i, u i) l ↔ ∀ i, Cauchy (uniformSpace := u i) l := by
  simp_rw [cauchy_iff_le (uniformSpace := _), iInf_uniformity, le_iInf_iff]

lemma cauchy_comap_uniformSpace {u : UniformSpace β} {α} {f : α → β} {l : Filter α} :
    Cauchy (uniformSpace := comap f u) l ↔ Cauchy (map f l) := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap]
  rfl

lemma cauchy_prod_iff [UniformSpace β] {F : Filter (α × β)} :
    Cauchy F ↔ Cauchy (map Prod.fst F) ∧ Cauchy (map Prod.snd F) := by
  simp_rw [instUniformSpaceProd, ← cauchy_comap_uniformSpace, ← cauchy_inf_uniformSpace]

theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) :
    Cauchy (f ×ˢ g) := by
  have := hf.1; have := hg.1
  simpa [cauchy_prod_iff, hf.1] using ⟨hf, hg⟩

/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`SequentiallyComplete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) : f ≤ 𝓝 x := by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (SetRel.prodMk_mem_comp hxy (ht <| mk_mem_prod hy hz)) rfl

/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) :
    f ≤ 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, t ×ˢ t ⊆ s := (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_neBot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) :
    f ≤ 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

nonrec theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f)
    (hm : UniformContinuous m) : Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ˢ map m f = map (Prod.map m m) (f ×ˢ f) := Filter.prod_map_map_eq
      _ ≤ Filter.map (Prod.map m m) (𝓤 α) := map_mono hf.right
      _ ≤ 𝓤 β := hm⟩

nonrec theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) [NeBot (comap m f)] :
    Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ˢ comap m f = comap (Prod.map m m) (f ×ˢ f) := prod_comap_comap_eq
      _ ≤ comap (Prod.map m m) (𝓤 β) := comap_mono hf.right
      _ ≤ 𝓤 α := hm⟩

theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : Filter.comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
    (_ : NeBot (Filter.comap m f)) : Cauchy (Filter.comap m f) :=
  hf.comap hm

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)

theorem CauchySeq.tendsto_uniformity [Preorder β] {u : β → α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [Tendsto, prod_map_map_eq', prod_atTop_atTop_eq] using h.right

theorem CauchySeq.nonempty [Preorder β] {u : β → α} (hu : CauchySeq u) : Nonempty β :=
  @nonempty_of_neBot _ _ <| (map_neBot_iff _).1 hu.1

theorem CauchySeq.mem_entourage {β : Type*} [SemilatticeSup β] {u : β → α} (h : CauchySeq u)
    {V : SetRel α α} (hV : V ∈ 𝓤 α) : ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V := by
  haveI := h.nonempty
  have := h.tendsto_uniformity; rw [← prod_atTop_atTop_eq] at this
  simpa [MapsTo] using atTop_basis.prod_self.tendsto_left_iff.1 this V hV

theorem Filter.Tendsto.cauchySeq [SemilatticeSup β] [Nonempty β] {f : β → α} {x}
    (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f :=
  hx.cauchy_map

theorem cauchySeq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun _ : β => x :=
  tendsto_const_nhds.cauchySeq

theorem cauchySeq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
  cauchy_map_iff'.trans <| by simp only [prod_atTop_atTop_eq, Prod.map_def]

theorem CauchySeq.comp_tendsto {γ} [Preorder β] [SemilatticeSup γ] [Nonempty γ] {f : β → α}
    (hf : CauchySeq f) {g : γ → β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  ⟨inferInstance, le_trans (prod_le_prod.mpr ⟨Tendsto.comp le_rfl hg, Tendsto.comp le_rfl hg⟩) hf.2⟩

theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : ℕ → α}
    (hu : CauchySeq u) {f : β → ℕ} (hf : Injective f) : CauchySeq (u ∘ f) :=
  hu.comp_tendsto <| Nat.cofinite_eq_atTop ▸ hf.tendsto_cofinite.mono_left atTop_le_cofinite

theorem Function.Bijective.cauchySeq_comp_iff {f : ℕ → ℕ} (hf : Bijective f) (u : ℕ → α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u := by
  refine ⟨fun H => ?_, fun H => H.comp_injective hf.injective⟩
  lift f to ℕ ≃ ℕ using hf
  simpa only [Function.comp_def, f.apply_symm_apply] using H.comp_injective f.symm.injective

theorem CauchySeq.subseq_subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n := by
  rw [cauchySeq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_atTop hg).comp tendsto_atTop_diagonal).subseq_mem hV

-- todo: generalize this and other lemmas to a nonempty semilattice
theorem cauchySeq_iff' {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∀ᶠ k in atTop, k ∈ Prod.map u u ⁻¹' V :=
  cauchySeq_iff_tendsto

theorem cauchySeq_iff {u : ℕ → α} :
    CauchySeq u ↔ ∀ V ∈ 𝓤 α, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V := by
  simp only [cauchySeq_iff', Filter.eventually_atTop_prod_self', mem_preimage, Prod.map_apply]

theorem CauchySeq.prodMap {γ δ} [UniformSpace β] [Preorder γ] [Preorder δ] {u : γ → α} {v : δ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [CauchySeq, prod_map_map_eq', prod_atTop_atTop_eq] using hu.prod hv

theorem CauchySeq.prodMk {γ} [UniformSpace β] [Preorder γ] {u : γ → α} {v : γ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) :=
  haveI := hu.1.of_map
  (Cauchy.prod hu hv).mono (tendsto_map.prodMk tendsto_map)

theorem CauchySeq.eventually_eventually [Preorder β] {u : β → α} (hu : CauchySeq u)
    {V : SetRel α α} (hV : V ∈ 𝓤 α) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, (u k, u l) ∈ V :=
  eventually_atTop_curry <| hu.tendsto_uniformity hV

theorem UniformContinuous.comp_cauchySeq {γ} [UniformSpace β] [Preorder γ] {f : α → β}
    (hf : UniformContinuous f) {u : γ → α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf

theorem CauchySeq.subseq_mem {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    (hu : CauchySeq u) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V n := by
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n := fun n => by
    rw [cauchySeq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_trans hk hl) _ hk⟩
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u <| φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| Nat.lt_add_one n).le⟩

theorem Filter.Tendsto.subseq_mem_entourage {V : ℕ → SetRel α α} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α}
    {a : α} (hu : Tendsto u atTop (𝓝 a)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ (u (φ 0), a) ∈ V 0 ∧
      ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V (n + 1) := by
  rcases mem_atTop_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases (hu.comp (tendsto_add_atTop_nat n)).cauchySeq.subseq_mem fun n => hV (n + 1) with
    ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
theorem tendsto_nhds_of_cauchySeq_of_subseq [Preorder β] {u : β → α} (hu : CauchySeq u)
    {ι : Type*} {f : ι → β} {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α}
    (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (ha.mapClusterPt.of_comp hf)

/-- Any shift of a Cauchy sequence is also a Cauchy sequence. -/
theorem cauchySeq_shift {u : ℕ → α} (k : ℕ) : CauchySeq (fun n ↦ u (n + k)) ↔ CauchySeq u := by
  constructor <;> intro h
  · rw [cauchySeq_iff] at h ⊢
    intro V mV
    obtain ⟨N, h⟩ := h V mV
    use N + k
    intro a ha b hb
    convert h (a - k) (Nat.le_sub_of_add_le ha) (b - k) (Nat.le_sub_of_add_le hb) <;> lia
  · exact h.comp_tendsto (tendsto_add_atTop_nat k)

theorem Filter.HasBasis.cauchySeq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → SetRel α α} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → (u m, u n) ∈ s i := by
  rw [cauchySeq_iff_tendsto, ← prod_atTop_atTop_eq]
  refine (atTop_basis.prod_self.tendsto_iff h).trans ?_
  simp only [true_and, Prod.forall, mem_prod_eq,
    mem_Ici, and_imp, Prod.map, @forall_swap (_ ≤ _) β]

theorem Filter.HasBasis.cauchySeq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β → α}
    {p : γ → Prop} {s : γ → SetRel α α} (H : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ n ≥ N, (u n, u N) ∈ s i := by
  refine H.cauchySeq_iff.trans ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
    refine (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt ?_, ht' <| hjt ?_⟩
    exacts [hN m hm, hN n hn]

theorem cauchySeq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β → SetRel α α)
    (hU : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) {f : β → α}
    (hf : ∀ ⦃N m n : β⦄, N ≤ m → N ≤ n → (f m, f n) ∈ U N) : CauchySeq f :=
  cauchySeq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map, mem_atTop_sets]
      obtain ⟨N, hN⟩ := hU s hs
      refine ⟨(N, N), fun mn hmn => ?_⟩
      obtain ⟨m, n⟩ := mn
      exact hN (hf hmn.1 hmn.2))

theorem isComplete_iff_clusterPt {s : Set α} :
    IsComplete s ↔ ∀ l, Cauchy l → l ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x l :=
  forall₃_congr fun _ hl _ => exists_congr fun _ => and_congr_right fun _ =>
    le_nhds_iff_adhp_of_cauchy hl

theorem isComplete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ↑l ≤ 𝓟 s → ∃ x ∈ s, ↑l ≤ 𝓝 x := by
  refine ⟨fun h l => h l, fun H => isComplete_iff_clusterPt.2 fun l hl hls => ?_⟩
  haveI := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

theorem isComplete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → s ∈ l → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  isComplete_iff_ultrafilter.trans <| by simp only [le_principal_iff, Ultrafilter.mem_coe]

protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) :
    IsComplete (s ∪ t) := by
  simp only [isComplete_iff_ultrafilter', Ultrafilter.union_mem_iff, or_imp] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.1, hx.2⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.1, hx.2⟩⟩

theorem isComplete_iUnion_separated {ι : Sort*} {s : ι → Set α} (hs : ∀ i, IsComplete (s i))
    {U : SetRel α α} (hU : U ∈ 𝓤 α) (hd : ∀ (i j : ι), ∀ x ∈ s i, ∀ y ∈ s j, (x, y) ∈ U → i = j) :
    IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  obtain ⟨hl_ne, hl'⟩ := cauchy_iff.1 hl
  obtain ⟨t, htS, htl, htU⟩ : ∃ t, t ⊆ S ∧ t ∈ l ∧ t ×ˢ t ⊆ U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    refine ⟨t ∩ S, inter_subset_right, inter_mem htl hls, Subset.trans ?_ htU⟩
    gcongr <;> apply inter_subset_left
  obtain ⟨i, hi⟩ : ∃ i, t ⊆ s i := by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_iUnion.1 (htS hx) with ⟨i, hi⟩
    refine ⟨i, fun y hy => ?_⟩
    rcases mem_iUnion.1 (htS hy) with ⟨j, hj⟩
    rwa [hd i j x hi y hj (htU <| mk_mem_prod hx hy)]
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_iUnion.2 ⟨i, hxs⟩, hlx⟩

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

theorem complete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] :
    IsComplete (univ : Set α) := fun f hf _ => by
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

instance CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] :
    CompleteSpace (α × β) where
  complete hf :=
    let ⟨x1, hx1⟩ := CompleteSpace.complete <| hf.map uniformContinuous_fst
    let ⟨x2, hx2⟩ := CompleteSpace.complete <| hf.map uniformContinuous_snd
    ⟨(x1, x2), by rw [nhds_prod_eq, le_prod]; constructor <;> assumption⟩

lemma CompleteSpace.fst_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty β] :
    CompleteSpace α where
  complete hf :=
    let ⟨y⟩ := h
    let ⟨(a, b), hab⟩ := CompleteSpace.complete <| hf.prod <| cauchy_pure (a := y)
    ⟨a, by simpa only [map_fst_prod, nhds_prod_eq] using map_mono (m := Prod.fst) hab⟩

lemma CompleteSpace.snd_of_prod [UniformSpace β] [CompleteSpace (α × β)] [h : Nonempty α] :
    CompleteSpace β where
  complete hf :=
    let ⟨x⟩ := h
    let ⟨(a, b), hab⟩ := CompleteSpace.complete <| (cauchy_pure (a := x)).prod hf
    ⟨b, by simpa only [map_snd_prod, nhds_prod_eq] using map_mono (m := Prod.snd) hab⟩

lemma completeSpace_prod_of_nonempty [UniformSpace β] [Nonempty α] [Nonempty β] :
    CompleteSpace (α × β) ↔ CompleteSpace α ∧ CompleteSpace β :=
  ⟨fun _ ↦ ⟨.fst_of_prod (β := β), .snd_of_prod (α := α)⟩, fun ⟨_, _⟩ ↦ .prod⟩

@[to_additive]
instance CompleteSpace.mulOpposite [CompleteSpace α] : CompleteSpace αᵐᵒᵖ where
  complete hf :=
    MulOpposite.op_surjective.exists.mpr <|
      let ⟨x, hx⟩ := CompleteSpace.complete (hf.map MulOpposite.uniformContinuous_unop)
      ⟨x, (map_le_iff_le_comap.mp hx).trans_eq <| MulOpposite.comap_unop_nhds _⟩

/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@complete_univ α _, completeSpace_of_isComplete_univ⟩

theorem completeSpace_iff_ultrafilter :
    CompleteSpace α ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ∃ x : α, ↑l ≤ 𝓝 x := by
  simp [completeSpace_iff_isComplete_univ, isComplete_iff_ultrafilter]

theorem cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] :
    Cauchy l ↔ ∃ x, l ≤ 𝓝 x :=
  ⟨CompleteSpace.complete, fun ⟨_, hx⟩ => cauchy_nhds.mono hx⟩

theorem cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β → α} [NeBot l] :
    Cauchy (l.map f) ↔ ∃ x, Tendsto f l (𝓝 x) :=
  cauchy_iff_exists_le_nhds

/-- A Cauchy sequence in a complete space converges -/
theorem cauchySeq_tendsto_of_complete [Preorder β] [CompleteSpace α] {u : β → α}
    (H : CauchySeq u) : ∃ x, Tendsto u atTop (𝓝 x) :=
  CompleteSpace.complete H

/-- If `K` is a complete subset, then any Cauchy sequence in `K` converges to a point in `K` -/
theorem cauchySeq_tendsto_of_isComplete [Preorder β] {K : Set α} (h₁ : IsComplete K)
    {u : β → α} (h₂ : ∀ n, u n ∈ K) (h₃ : CauchySeq u) : ∃ v ∈ K, Tendsto u atTop (𝓝 v) :=
  h₁ _ h₃ <| le_principal_iff.2 <| mem_map_iff_exists_image.2
    ⟨univ, univ_mem, by rwa [image_univ, range_subset_iff]⟩

theorem Cauchy.le_nhds_lim [CompleteSpace α] {f : Filter α} (hf : Cauchy f) :
    haveI := hf.1.nonempty; f ≤ 𝓝 (lim f) :=
  _root_.le_nhds_lim (CompleteSpace.complete hf)

theorem CauchySeq.tendsto_limUnder [Preorder β] [CompleteSpace α] {u : β → α} (h : CauchySeq u) :
    haveI := h.1.nonempty; Tendsto u atTop (𝓝 <| limUnder atTop u) :=
  h.le_nhds_lim

theorem IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s :=
  fun _ cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, isClosed_iff_clusterPt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

namespace DiscreteUniformity

variable [DiscreteUniformity α]

/-- A Cauchy filter in a discrete uniform space is contained in the principal filter
of a point. -/
theorem eq_pure_of_cauchy {f : Filter α} (hf : Cauchy f) : ∃ x : α, f = pure x := by
  rcases hf with ⟨f_ne_bot, f_le⟩
  simp only [DiscreteUniformity.eq_principal_setRelId, le_principal_iff, mem_prod_iff] at f_le
  obtain ⟨S, hS, T, hT, H⟩ := f_le
  obtain ⟨x, rfl, _, _, _⟩ := SetRel.exists_eq_singleton_of_prod_subset_id
    (f_ne_bot.nonempty_of_mem hS) (f_ne_bot.nonempty_of_mem hT) H
  exact ⟨x, f_ne_bot.le_pure_iff.mp <| le_pure_iff.mpr hS⟩

/-- The discrete uniformity makes a space complete. -/
instance : CompleteSpace α where
  complete {f} hf := by
    obtain ⟨x, rfl⟩ := eq_pure_of_cauchy hf
    exact ⟨x, pure_le_nhds x⟩

variable {X}

/-- A constant to which a Cauchy filter in a discrete uniform space converges. -/
noncomputable def cauchyConst {f : Filter α} (hf : Cauchy f) : α :=
  (eq_pure_of_cauchy hf).choose

theorem eq_pure_cauchyConst {f : Filter α} (hf : Cauchy f) : f = pure (cauchyConst hf) :=
  (eq_pure_of_cauchy hf).choose_spec

end DiscreteUniformity

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }

/-- A filter `f` is totally bounded if for every entourage `d`, the `d`-neighborhood of some finite
set is in `f`. -/
protected def Filter.TotallyBounded (f : Filter α) :=
  ∀ d : SetRel α α, d ∈ 𝓤 α → ∃ t : Set α, t.Finite ∧ d.preimage t ∈ f

theorem Filter.totallyBounded_principal_iff {s : Set α} :
    (𝓟 s).TotallyBounded ↔ TotallyBounded s := by
  simp only [Filter.TotallyBounded, mem_principal, SetRel.preimage_eq_biUnion, TotallyBounded]

theorem Filter.TotallyBounded.exists_subset_of_mem {f : Filter α} (hf : f.TotallyBounded)
    {s : Set α} (hs : s ∈ f) {U : SetRel α α} (hU : U ∈ 𝓤 α) :
    ∃ t ⊆ s, Set.Finite t ∧ U.preimage t ∈ f := by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hf r hr with ⟨k, fk, ks⟩
  let u := k ∩ { y | ∃ x ∈ s, (x, y) ∈ r }
  choose g hgs hgr using fun x : u => x.coe_prop.2
  refine ⟨range g, ?_, ?_, ?_⟩
  · exact range_subset_iff.2 hgs
  · haveI : Fintype u := (fk.inter_of_left _).fintype
    exact finite_range g
  · filter_upwards [hs, ks] with x xs ⟨y, hy, xy⟩
    simp_rw [SetRel.preimage, exists_range_iff]
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩
    exact ⟨z, rU ⟨y, xy, rs (hgr z)⟩⟩

theorem TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : SetRel α α}
    (hU : U ∈ 𝓤 α) : ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U } := by
  rw [← Filter.totallyBounded_principal_iff] at hs
  simp_rw [← SetRel.preimage_eq_biUnion]
  exact hs.exists_subset_of_mem (Filter.mem_principal_self s) hU

theorem totallyBounded_iff_subset {s : Set α} :
    TotallyBounded s ↔
      ∀ d ∈ 𝓤 α, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d } :=
  ⟨fun H _ hd ↦ H.exists_subset hd, fun H d hd ↦ let ⟨t, _, ht⟩ := H d hd; ⟨t, ht⟩⟩

theorem Filter.HasBasis.totallyBounded_iff {ι} {p : ι → Prop} {U : ι → SetRel α α}
    (H : (𝓤 α).HasBasis p U) {s : Set α} :
    TotallyBounded s ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U i } :=
  H.forall_iff fun _ _ hUV h =>
    h.imp fun _ ht => ⟨ht.1, ht.2.trans <| iUnion₂_mono fun _ _ _ hy => hUV hy⟩

theorem Filter.HasBasis.filter_totallyBounded_iff {ι} {p : ι → Prop} {U : ι → SetRel α α}
    (H : (𝓤 α).HasBasis p U) {f : Filter α} :
    f.TotallyBounded ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ (U i).preimage t ∈ f :=
  H.forall_iff fun _ _ _ h =>
    h.imp fun _ ht => ⟨ht.1, f.mem_of_superset ht.2 <| by gcongr⟩

theorem totallyBounded_of_forall_isSymm {s : Set α}
    (h : ∀ V ∈ 𝓤 α, SetRel.IsSymm V → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y V) :
    TotallyBounded s :=
  UniformSpace.hasBasis_symmetric.totallyBounded_iff.2 fun V ⟨_, _⟩ => by
    simpa only [ball_eq_of_symmetry] using h V ‹_› ‹_›

theorem TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) (h : TotallyBounded s₂) :
    TotallyBounded s₁ := fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩

theorem Filter.TotallyBounded.mono {f g : Filter α} (h : f ≤ g) (hg : g.TotallyBounded) :
    f.TotallyBounded :=
  fun U hU => (hg U hU).imp fun _ => And.imp_right (@h _)

theorem Filter.TotallyBounded.totallyBounded_setOf_clusterPt {f : Filter α} (h : f.TotallyBounded) :
    TotallyBounded {x | ClusterPt x f} := by
  refine uniformity_hasBasis_closed.totallyBounded_iff.2 fun V hV => ?_
  obtain ⟨t, htf, hst⟩ := h V hV.1
  refine ⟨t, htf, fun x hx => ?_⟩
  rw [← SetRel.preimage_eq_biUnion, id, ← (hV.2.relPreimage_of_finite htf).closure_eq]
  exact hx.mem_closure_of_mem _ hst

/-- The closure of a totally bounded set is totally bounded. -/
theorem TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded (closure s) := by
  rw [closure_eq_cluster_pts]
  exact (Filter.totallyBounded_principal_iff.mpr h).totallyBounded_setOf_clusterPt

@[simp]
lemma totallyBounded_closure {s : Set α} : TotallyBounded (closure s) ↔ TotallyBounded s :=
  ⟨fun h ↦ h.subset subset_closure, TotallyBounded.closure⟩

@[simp]
lemma Filter.totallyBounded_iSup {ι : Sort*} [Finite ι] {f : ι → Filter α} :
    (⨆ i, f i).TotallyBounded ↔ ∀ i, (f i).TotallyBounded := by
  refine ⟨fun h i ↦ h.mono (le_iSup _ _), fun h U hU ↦ ?_⟩
  choose t htf ht using (h · U hU)
  refine ⟨⋃ i, t i, finite_iUnion htf, ?_⟩
  simp_rw [U.preimage_iUnion, ← le_principal_iff, ← iSup_principal] at ht ⊢
  gcongr; apply ht

lemma Filter.totallyBounded_biSup {ι : Type*} {I : Set ι} (hI : I.Finite) {f : ι → Filter α} :
    (⨆ i ∈ I, f i).TotallyBounded ↔ ∀ i ∈ I, (f i).TotallyBounded := by
  have := hI.to_subtype
  rw [iSup_subtype', totallyBounded_iSup, Subtype.forall]

lemma totallyBounded_sSup {S : Set (Filter α)} (hS : S.Finite) :
    (sSup S).TotallyBounded ↔ ∀ f ∈ S, f.TotallyBounded := by
  rw [sSup_eq_iSup, totallyBounded_biSup hS]

/-- A finite indexed union is totally bounded
if and only if each set of the family is totally bounded. -/
@[simp]
lemma totallyBounded_iUnion {ι : Sort*} [Finite ι] {s : ι → Set α} :
    TotallyBounded (⋃ i, s i) ↔ ∀ i, TotallyBounded (s i) := by
  simp_rw [← Filter.totallyBounded_principal_iff, ← Filter.iSup_principal,
    Filter.totallyBounded_iSup]

/-- A union indexed by a finite set is totally bounded
if and only if each set of the family is totally bounded. -/
lemma totallyBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set α} :
    TotallyBounded (⋃ i ∈ I, s i) ↔ ∀ i ∈ I, TotallyBounded (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion, totallyBounded_iUnion, Subtype.forall]

/-- A union of a finite family of sets is totally bounded
if and only if each set of the family is totally bounded. -/
lemma totallyBounded_sUnion {S : Set (Set α)} (hS : S.Finite) :
    TotallyBounded (⋃₀ S) ↔ ∀ s ∈ S, TotallyBounded s := by
  rw [sUnion_eq_biUnion, totallyBounded_biUnion hS]

/-- A finite set is totally bounded. -/
lemma Set.Finite.totallyBounded {s : Set α} (hs : s.Finite) : TotallyBounded s := fun _U hU ↦
  ⟨s, hs, fun _x hx ↦ mem_biUnion hx <| refl_mem_uniformity hU⟩

/-- A subsingleton is totally bounded. -/
lemma Set.Subsingleton.totallyBounded {s : Set α} (hs : s.Subsingleton) :
    TotallyBounded s :=
  hs.finite.totallyBounded

@[simp]
lemma totallyBounded_singleton (a : α) : TotallyBounded {a} := (finite_singleton a).totallyBounded

@[simp]
theorem totallyBounded_empty : TotallyBounded (∅ : Set α) := finite_empty.totallyBounded

@[simp]
theorem Filter.totallyBounded_bot : (⊥ : Filter α).TotallyBounded := by
  rw [← principal_empty, totallyBounded_principal_iff]
  exact totallyBounded_empty

/-- The union of two sets is totally bounded
if and only if each of the two sets is totally bounded. -/
@[simp]
lemma totallyBounded_union {s t : Set α} :
    TotallyBounded (s ∪ t) ↔ TotallyBounded s ∧ TotallyBounded t := by
  rw [union_eq_iUnion, totallyBounded_iUnion]
  simp [and_comm]

/-- The union of two totally bounded sets is totally bounded. -/
protected lemma TotallyBounded.union {s t : Set α} (hs : TotallyBounded s) (ht : TotallyBounded t) :
    TotallyBounded (s ∪ t) :=
  totallyBounded_union.2 ⟨hs, ht⟩

@[simp]
lemma totallyBounded_insert (a : α) {s : Set α} :
    TotallyBounded (insert a s) ↔ TotallyBounded s := by
  simp_rw [← singleton_union, totallyBounded_union, totallyBounded_singleton, true_and]

protected alias ⟨_, TotallyBounded.insert⟩ := totallyBounded_insert

@[simp]
lemma Filter.totallyBounded_sup {f g : Filter α} :
    (f ⊔ g).TotallyBounded ↔ f.TotallyBounded ∧ g.TotallyBounded := by
  rw [sup_eq_iSup, totallyBounded_iSup]
  simp [and_comm]

lemma Filter.TotallyBounded.sup {f g : Filter α} (hf : f.TotallyBounded) (hg : g.TotallyBounded) :
    (f ⊔ g).TotallyBounded :=
  totallyBounded_sup.2 ⟨hf, hg⟩

theorem Filter.TotallyBounded.map [UniformSpace β] {f : α → β} {g : Filter α}
    (hg : g.TotallyBounded) (hf : UniformContinuous f) : (g.map f).TotallyBounded := fun t ht =>
  let ⟨c, hfc, hct⟩ := hg _ (hf ht)
  ⟨f '' c, hfc.image f, by simpa [SetRel.preimage]⟩

/-- The image of a totally bounded set under a uniformly continuous map is totally bounded. -/
theorem TotallyBounded.image [UniformSpace β] {f : α → β} {s : Set α} (hs : TotallyBounded s)
    (hf : UniformContinuous f) : TotallyBounded (f '' s) := by
  simp only [← Filter.totallyBounded_principal_iff, ← Filter.map_principal] at hs ⊢
  exact hs.map hf

theorem Ultrafilter.cauchy_of_totallyBounded' (f : Ultrafilter α) (hf : f.TotallyBounded) :
    Cauchy (f : Filter α) :=
  ⟨f.neBot', fun _ ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, ht'_f⟩ := hf t' ht'₁
    have : ∃ y ∈ i, { x | (x, y) ∈ t' } ∈ f := (Ultrafilter.eventually_exists_mem_iff hi).1 ht'_f
    let ⟨y, _, hif⟩ := this
    have : {x | (x, y) ∈ t'} ×ˢ {x | (x, y) ∈ t'} ⊆ t' ○ t' :=
      fun ⟨_, _⟩ ⟨(h₁ : (_, y) ∈ t'), (h₂ : (_, y) ∈ t')⟩ => ⟨y, h₁, ht'_symm h₂⟩
    mem_of_superset (prod_mem_prod hif hif) (Subset.trans this ht'_t)⟩

theorem Ultrafilter.cauchy_of_totallyBounded {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s)
    (h : ↑f ≤ 𝓟 s) : Cauchy (f : Filter α) :=
  f.cauchy_of_totallyBounded' <| (Filter.totallyBounded_principal_iff.mpr hs).mono h

protected theorem Filter.totallyBounded_iff_filter {g : Filter α} :
    g.TotallyBounded ↔ ∀ f, NeBot f → f ≤ g → ∃ c ≤ f, Cauchy c := by
  constructor
  · exact fun H f hf hfs => ⟨Ultrafilter.of f, Ultrafilter.of_le f,
      (Ultrafilter.of f).cauchy_of_totallyBounded' (H.mono ((Ultrafilter.of_le f).trans hfs))⟩
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, g ⊓ 𝓟 (d.preimage t)ᶜ
    have hb : Antitone fun t : Finset α ↦ g ⊓ 𝓟 (d.preimage t)ᶜ :=
      fun s t (h : s ⊆ t) => by beta_reduce; gcongr
    have : Filter.NeBot f :=
      (Filter.iInf_neBot_iff_of_directed' <| hb.directed_ge).mpr fun t =>
        Filter.notMem_iff_inf_principal_compl.mp <| hd_cover t t.finite_toSet
    have : f ≤ g := iInf_le_of_le ∅ (by simp)
    refine ⟨f, ‹_›, ‹_›, fun c hcf hc => ?_⟩
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩
    rcases hc.1.nonempty_of_mem hm with ⟨y, hym⟩
    have : {x | (x, y) ∈ d}ᶜ ∈ c := by
      simpa [SetRel.preimage] using hcf.trans <| (iInf_le _ {y}).trans inf_le_right
    rcases hc.1.nonempty_of_mem (inter_mem hm this) with ⟨z, hzm, hyz⟩
    exact hyz (hmd ⟨hzm, hym⟩)

protected theorem Filter.totallyBounded_iff_ultrafilter {g : Filter α} :
    g.TotallyBounded ↔ ∀ f : Ultrafilter α, ↑f ≤ g → Cauchy (f : Filter α) := by
  refine ⟨fun hg f hf => f.cauchy_of_totallyBounded' <| hg.mono hf,
    fun H => g.totallyBounded_iff_filter.2 ?_⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩

theorem totallyBounded_iff_filter {s : Set α} :
    TotallyBounded s ↔ ∀ f, NeBot f → f ≤ 𝓟 s → ∃ c ≤ f, Cauchy c := by
  rw [← Filter.totallyBounded_principal_iff, Filter.totallyBounded_iff_filter]

theorem totallyBounded_iff_ultrafilter {s : Set α} :
    TotallyBounded s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → Cauchy (f : Filter α) := by
  rw [← Filter.totallyBounded_principal_iff, Filter.totallyBounded_iff_ultrafilter]

theorem isCompact_iff_totallyBounded_isComplete {s : Set α} :
    IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  ⟨fun hs =>
    ⟨totallyBounded_iff_ultrafilter.2 fun f hf =>
        let ⟨_, _, fx⟩ := isCompact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    isCompact_iff_ultrafilter_le_nhds.2 fun f hf =>
      hc _ (totallyBounded_iff_ultrafilter.1 ht f hf) hf⟩

protected theorem IsCompact.totallyBounded {s : Set α} (h : IsCompact s) : TotallyBounded s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).1

protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2

-- see Note [lower instance priority]
instance (priority := 100) complete_of_compact {α : Type u} [UniformSpace α] [CompactSpace α] :
    CompleteSpace α :=
  ⟨fun hf => by simpa using (isCompact_iff_totallyBounded_isComplete.1 isCompact_univ).2 _ hf⟩

theorem TotallyBounded.isCompact_of_isComplete {s : Set α} (ht : TotallyBounded s)
    (hc : IsComplete s) : IsCompact s := isCompact_iff_totallyBounded_isComplete.mpr ⟨ht, hc⟩

theorem TotallyBounded.isCompact_of_isClosed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s)
    (hc : IsClosed s) : IsCompact s := ht.isCompact_of_isComplete hc.isComplete

@[deprecated (since := "2025-08-30")] alias isCompact_of_totallyBounded_isClosed :=
    TotallyBounded.isCompact_of_isClosed

theorem Filter.TotallyBounded.isCompact_setOf_clusterPt
    [CompleteSpace α] {f : Filter α} (hf : f.TotallyBounded) : IsCompact {x | ClusterPt x f} :=
  hf.totallyBounded_setOf_clusterPt.isCompact_of_isClosed isClosed_setOf_clusterPt

theorem Filter.TotallyBounded.exists_clusterPt
    [CompleteSpace α] {f : Filter α} [f.NeBot] (hf : f.TotallyBounded) : ∃ x, ClusterPt x f := by
  let m := Ultrafilter.of f
  have hmf : m ≤ f := Ultrafilter.of_le f
  have hm := m.cauchy_of_totallyBounded' (hf.mono hmf)
  obtain ⟨x, hx⟩ := CompleteSpace.complete hm
  rw [le_nhds_iff_adhp_of_cauchy hm] at hx
  exact ⟨x, hx.mono hmf⟩

/-- Every Cauchy sequence over `ℕ` is totally bounded. -/
theorem CauchySeq.totallyBounded_range {s : ℕ → α} (hs : CauchySeq s) :
    TotallyBounded (range s) := by
  intro a ha
  obtain ⟨n, hn⟩ := cauchySeq_iff.1 hs a ha
  refine ⟨s '' { k | k ≤ n }, (finite_le_nat _).image _, ?_⟩
  rw [range_subset_iff, biUnion_image]
  intro m
  rw [mem_iUnion₂]
  rcases le_total m n with hm | hm
  exacts [⟨m, hm, refl_mem_uniformity ha⟩, ⟨n, le_refl n, hn m hm n le_rfl⟩]

/-- Given a family of points `xs n`, a family of entourages `V n` of the diagonal and a family of
natural numbers `u n`, the intersection over `n` of the `V n`-neighborhood of `xs 1, ..., xs (u n)`.
Designed to be relatively compact when `V n` tends to the diagonal. -/
def interUnionBalls (xs : ℕ → α) (u : ℕ → ℕ) (V : ℕ → SetRel α α) : Set α :=
  ⋂ n, ⋃ m ≤ u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)

lemma totallyBounded_interUnionBalls {p : ℕ → Prop} {U : ℕ → SetRel α α}
    (H : (uniformity α).HasBasis p U) (xs : ℕ → α) (u : ℕ → ℕ) :
    TotallyBounded (interUnionBalls xs u U) := by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      ⊆ ⋃ m ≤ u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx ↦ Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, fun x hx ↦ ?_⟩
  simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right, Nat.lt_succ_iff]
  exact h_subset hx

/-- The construction `interUnionBalls` is used to have a relatively compact set. -/
theorem isCompact_closure_interUnionBalls {p : ℕ → Prop} {U : ℕ → SetRel α α}
    (H : (uniformity α).HasBasis p U) [CompleteSpace α] (xs : ℕ → α) (u : ℕ → ℕ) :
    IsCompact (closure (interUnionBalls xs u U)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files `Topology/MetricSpace/EmetricSpace`
and `Topology/MetricSpace/Basic`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/


namespace SequentiallyComplete

variable {f : Filter α} (hf : Cauchy f) {U : ℕ → SetRel α α} (U_mem : ∀ n, U n ∈ 𝓤 α)

open Set Finset

noncomputable section

/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
def setSeqAux (n : ℕ) : { s : Set α // s ∈ f ∧ s ×ˢ s ⊆ U n } :=
  Classical.indefiniteDescription _ <| (cauchy_iff.1 hf).2 (U n) (U_mem n)

/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `s n ×ˢ s n ⊆ U`. -/
def setSeq (n : ℕ) : Set α :=
  ⋂ m ∈ Set.Iic n, (setSeqAux hf U_mem m).val

theorem setSeq_mem (n : ℕ) : setSeq hf U_mem n ∈ f :=
  (biInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.1

theorem setSeq_mono ⦃m n : ℕ⦄ (h : m ≤ n) : setSeq hf U_mem n ⊆ setSeq hf U_mem m :=
  biInter_subset_biInter_left <| Iic_subset_Iic.2 h

theorem setSeq_sub_aux (n : ℕ) : setSeq hf U_mem n ⊆ setSeqAux hf U_mem n :=
  biInter_subset_of_mem self_mem_Iic

theorem setSeq_prod_subset {N m n} (hm : N ≤ m) (hn : N ≤ n) :
    setSeq hf U_mem m ×ˢ setSeq hf U_mem n ⊆ U N := fun p hp => by
  refine (setSeqAux hf U_mem N).2.2 ⟨?_, ?_⟩ <;> apply setSeq_sub_aux
  · exact setSeq_mono hf U_mem hm hp.1
  · exact setSeq_mono hf U_mem hn hp.2

/-- A sequence of points such that `seq n ∈ setSeq n`. Here `setSeq` is an antitone
sequence of sets `setSeq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq (n : ℕ) : α :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose

theorem seq_mem (n : ℕ) : seq hf U_mem n ∈ setSeq hf U_mem n :=
  (hf.1.nonempty_of_mem (setSeq_mem hf U_mem n)).choose_spec

theorem seq_pair_mem ⦃N m n : ℕ⦄ (hm : N ≤ m) (hn : N ≤ n) :
    (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
  setSeq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

theorem seq_is_cauchySeq (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s) : CauchySeq <| seq hf U_mem :=
  cauchySeq_of_controlled U U_le <| seq_pair_mem hf U_mem

/-- If the sequence `SequentiallyComplete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
theorem le_nhds_of_seq_tendsto_nhds (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s)
    ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f ≤ 𝓝 a :=
  le_nhds_of_cauchy_adhp_aux
    (fun s hs => by
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_atTop'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine
        ⟨setSeq hf U_mem (max m n), setSeq_mem hf U_mem _, ?_, seq hf U_mem (max m n), ?_,
          seq_mem hf U_mem _⟩
      · have := le_max_left m n
        exact Set.Subset.trans (setSeq_prod_subset hf U_mem this this) hm
      · exact hm (hn _ <| le_max_right m n))

end

end SequentiallyComplete

namespace UniformSpace

open SequentiallyComplete

variable [IsCountablyGenerated (𝓤 α)]

/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences (U : ℕ → SetRel α α) (U_mem : ∀ n, U n ∈ 𝓤 α)
    (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α := by
  obtain ⟨U', -, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, Subset.refl _⟩)
  refine ⟨fun hf => (HU (seq hf Hmem) fun N m n hm hn => ?_).imp <|
    le_nhds_of_seq_tendsto_nhds _ _ fun s hs => ?_⟩
  · exact inter_subset_left (seq_pair_mem hf Hmem hm hn)
  · rcases hU'.1 hs with ⟨N, hN⟩
    exact ⟨N, Subset.trans inter_subset_right hN⟩

/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
theorem complete_of_cauchySeq_tendsto (H' : ∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) :
    CompleteSpace α :=
  let ⟨U', _, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
    H' u <| cauchySeq_of_controlled U' (fun _ hs => hU'.1 hs) hu

variable (α)

-- TODO: move to `Topology.UniformSpace.Basic`
instance (priority := 100) firstCountableTopology : FirstCountableTopology α :=
  ⟨fun a => by rw [nhds_eq_comap_uniformity]; infer_instance⟩

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. -/
instance secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : ℕ → SetRel α α, hto : ∀ i : ℕ, t i ∈ (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
  refine ⟨⟨⋃ x ∈ s, range fun k => ball x (t k), hsc.biUnion fun x _ => countable_range _, ?_⟩⟩
  refine (isTopologicalBasis_of_isOpen_of_nhds ?_ ?_).eq_generateFrom
  · simp only [mem_iUnion₂, mem_range]
    rintro _ ⟨x, _, k, rfl⟩
    exact isOpen_ball x (hto k)
  · intro x V hxV hVo
    simp only [mem_iUnion₂, mem_range, exists_prop]
    rcases UniformSpace.mem_nhds_iff.1 (IsOpen.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩
    rcases comp_symm_of_uniformity hU with ⟨U', hU', _, hUU'⟩
    rcases h_basis.toHasBasis.mem_iff.1 hU' with ⟨k, -, hk⟩
    rcases hsd.inter_open_nonempty (ball x <| t k) (isOpen_ball x (hto k))
        ⟨x, UniformSpace.mem_ball_self _ (ht_mem k)⟩ with
      ⟨y, hxy, hys⟩
    refine ⟨_, ⟨y, hys, k, rfl⟩, (t k).symm hxy, fun z hz => ?_⟩
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz))

variable {α}

theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ U ∈ 𝓤 α, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, ball x U) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  obtain ⟨B, hB, _⟩ := has_seq_basis α
  replace hs (n : ℕ) := hs (B n) (hB.mem n)
  choose t tC ht using hs
  have := fun n => (tC n).to_subtype
  choose o hox hos using fun (n : ℕ) (x : t n) (hx : (ball x.1 (B n) ∩ s).Nonempty) => hx
  refine ⟨⋃ (n) (x), range (o n x), iUnion₂_subset fun _ _ => range_subset_iff.2 (hos _ _),
    countable_iUnion fun _ => countable_iUnion fun _ => countable_range _, fun x hx => ?_⟩
  rw [mem_closure_iff_ball]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨n, hn⟩ := hB.mem_iff.1 hV
  specialize ht n hx
  rw [mem_iUnion₂] at ht
  obtain ⟨y, hy, hyx⟩ := ht
  refine ⟨o n ⟨y, hy⟩ ⟨x, hyx, hx⟩, ?_, ?_⟩
  · apply ball_mono ((SetRel.comp_subset_comp hn hn).trans hVU)
    exact mem_ball_comp (mem_ball_symmetry.2 hyx) (hox n ⟨y, hy⟩ ⟨x, hyx, hx⟩)
  · exact mem_iUnion₂_of_mem ⟨y, hy⟩ (mem_range_self ⟨x, hyx, hx⟩)

theorem secondCountable_of_almost_dense_set
    (hs : ∀ U ∈ 𝓤 α, ∃ t : Set α, t.Countable ∧ ⋃ x ∈ t, ball x U = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : ∀ U ∈ 𝓤 α, ∃ t : Set α, Set.Countable t ∧ univ ⊆ ⋃ x ∈ t, ball x U := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

/-- A totally bounded set is separable in countably generated uniform spaces. This can be obtained
from the more general `UniformSpace.subset_countable_closure_of_almost_dense_set`. -/
lemma _root_.TotallyBounded.isSeparable {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s := by
  obtain ⟨t, -, htc, hts⟩ := subset_countable_closure_of_almost_dense_set s fun U hU => by
    obtain ⟨t, ht, hst⟩ := h (SetRel.inv U)
      (mem_of_superset (symmetrize_mem_uniformity hU) SetRel.symmetrize_subset_inv)
    exact ⟨t, ht.countable, hst⟩
  exact ⟨t, htc, hts⟩

end UniformSpace
