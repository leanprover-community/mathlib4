/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Antichain
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper colorings in the literature).
A graph coloring is the attribution of "colors" to all of its vertices such that adjacent vertices
have different colors.
A coloring can be represented as a homomorphism into a complete graph, whose vertices represent
the colors.

## Main definitions

* `G.Coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.Colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromaticNumber` is the minimal `n` such that `G` is `n`-colorable,
  or `⊤` if it cannot be colored with finitely many colors.
  (Cardinal-valued chromatic numbers are more niche, so we stick to `ℕ∞`.)
  We write `G.chromaticNumber ≠ ⊤` to mean a graph is colorable with finitely many colors.

* `C.colorClass c` is the set of vertices colored by `c : α` in the coloring `C : G.Coloring α`.

* `C.colorClasses` is the set containing all color classes.

## TODO

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)
-/

assert_not_exists Field

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α

variable {G}
variable {α β : Type*} (C : G.Coloring α)

theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h

/-- Construct a term of `SimpleGraph.Coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `SimpleGraph.Hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[match_pattern]
def Coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) :
    G.Coloring α :=
  ⟨color, @valid⟩

/-- The color class of a given color.
-/
def Coloring.colorClass (c : α) : Set V := { v : V | C v = c }

/-- The set containing all color classes. -/
def Coloring.colorClasses : Set (Set V) := (Setoid.ker C).classes

theorem Coloring.mem_colorClass (v : V) : v ∈ C.colorClass (C v) := rfl

theorem Coloring.colorClasses_isPartition : Setoid.IsPartition C.colorClasses :=
  Setoid.isPartition_classes (Setoid.ker C)

theorem Coloring.mem_colorClasses {v : V} : C.colorClass (C v) ∈ C.colorClasses :=
  ⟨v, rfl⟩

theorem Coloring.colorClasses_finite [Finite α] : C.colorClasses.Finite :=
  Setoid.finite_classes_ker _

theorem Coloring.card_colorClasses_le [Fintype α] [Fintype C.colorClasses] :
    Fintype.card C.colorClasses ≤ Fintype.card α := by
  simp only [colorClasses]
  convert Setoid.card_classes_ker_le C

theorem Coloring.not_adj_of_mem_colorClass {c : α} {v w : V} (hv : v ∈ C.colorClass c)
    (hw : w ∈ C.colorClass c) : ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))

theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.colorClass c) :=
  fun _ hv _ hw _ => C.not_adj_of_mem_colorClass hv hw

-- TODO make this computable
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
  change Fintype (RelHom G.Adj (completeGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective

instance [DecidableEq α] {c : α} :
    DecidablePred (· ∈ C.colorClass c) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | C v = c })

variable (G)

/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))

/-- The coloring of an empty graph. -/
def coloringOfIsEmpty [IsEmpty V] : G.Coloring α :=
  Coloring.mk isEmptyElim fun {v} => isEmptyElim v

theorem colorable_of_isEmpty [IsEmpty V] (n : ℕ) : G.Colorable n :=
  ⟨G.coloringOfIsEmpty⟩

theorem isEmpty_of_colorable_zero (h : G.Colorable 0) : IsEmpty V := by
  constructor
  intro v
  obtain ⟨i, hi⟩ := h.some v
  exact Nat.not_lt_zero _ hi

@[simp]
lemma colorable_zero_iff : G.Colorable 0 ↔ IsEmpty V :=
  ⟨G.isEmpty_of_colorable_zero, fun _ ↦ G.colorable_of_isEmpty 0⟩

/-- If `G` is `n`-colorable, then mapping the vertices of `G` produces an `n`-colorable simple
graph. -/
theorem Colorable.map {β : Type*} (f : V ↪ β) [NeZero n] {G : SimpleGraph V} (hc : G.Colorable n) :
    (G.map f).Colorable n := by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, hadj, ha, hb⟩
  rw [← ha, f.injective.extend_apply, ← hb, f.injective.extend_apply]
  exact C.valid hadj

/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def selfColoring : G.Coloring V := Coloring.mk id fun {_ _} => G.ne_of_adj

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chromatic number. -/
noncomputable def chromaticNumber : ℕ∞ := ⨅ n ∈ setOf G.Colorable, (n : ℕ∞)

lemma chromaticNumber_eq_biInf {G : SimpleGraph V} :
    G.chromaticNumber = ⨅ n ∈ setOf G.Colorable, (n : ℕ∞) := rfl

lemma chromaticNumber_eq_iInf {G : SimpleGraph V} :
    G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : ℕ∞) := by
  rw [chromaticNumber, iInf_subtype]

lemma Colorable.chromaticNumber_eq_sInf {G : SimpleGraph V} {n} (h : G.Colorable n) :
    G.chromaticNumber = sInf {n' : ℕ | G.Colorable n'} := by
  rw [ENat.coe_sInf, chromaticNumber]
  exact ⟨_, h⟩

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolorOfEmbedding {α β : Type*} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β where
  toFun C := (Embedding.completeGraph f).toHom.comp C
  inj' := by -- this was strangely painful; seems like missing lemmas about embeddings
    intro C C' h
    dsimp only at h
    ext v
    apply (Embedding.completeGraph f).inj'
    change ((Embedding.completeGraph f).toHom.comp C) v = _
    rw [h]
    rfl

@[simp] lemma coe_recolorOfEmbedding (f : α ↪ β) :
    ⇑(G.recolorOfEmbedding f) = (Embedding.completeGraph f).toHom.comp := rfl

/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolorOfEquiv {α β : Type*} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply

@[simp] lemma coe_recolorOfEquiv (f : α ≃ β) :
    ⇑(G.recolorOfEquiv f) = (Embedding.completeGraph f).toHom.comp := rfl

/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β]
    (hn : Fintype.card α ≤ Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding <| (Function.Embedding.nonempty_of_card_le hn).some

@[simp] lemma coe_recolorOfCardLE [Fintype α] [Fintype β] (hαβ : card α ≤ card β) :
    ⇑(G.recolorOfCardLE hαβ) =
      (Embedding.completeGraph (Embedding.nonempty_of_card_le hαβ).some).toHom.comp := rfl

variable {G}

theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩

theorem Coloring.colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLE (by simp) C⟩

theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.colorable

/-- Noncomputably get a coloring from colorability. -/
noncomputable def Colorable.toColoring [Fintype α] {n : ℕ} (hc : G.Colorable n)
    (hn : n ≤ Fintype.card α) : G.Coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some

theorem Colorable.of_embedding {V' : Type*} {G' : SimpleGraph V'} (f : G ↪g G') {n : ℕ}
    (h : G'.Colorable n) : G.Colorable n :=
  ⟨(h.toColoring (by simp)).comp f⟩

theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
    G.Colorable n ↔ ∃ C : G.Coloring ℕ, ∀ v, C v < n := by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    exact Fin.is_lt (C.1 v)
  · rintro ⟨C, Cf⟩
    refine ⟨Coloring.mk ?_ ?_⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne]
      exact C.valid hvw

theorem colorable_iff_forall_connectedComponents {n : ℕ} :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (c.toSimpleGraph).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v, fun h h1 ↦ C.valid h h1⟩,
   fun h ↦ ⟨G.homOfConnectedComponents (fun c ↦ (h c).some)⟩⟩

theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.Colorable n) :
    { n : ℕ | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩

theorem chromaticNumber_bddBelow : BddBelow { n : ℕ | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le _⟩

theorem Colorable.chromaticNumber_le {n : ℕ} (hc : G.Colorable n) : G.chromaticNumber ≤ n := by
  rw [hc.chromaticNumber_eq_sInf]
  norm_cast
  apply csInf_le chromaticNumber_bddBelow
  exact hc

theorem chromaticNumber_ne_top_iff_exists : G.chromaticNumber ≠ ⊤ ↔ ∃ n, G.Colorable n := by
  rw [chromaticNumber]
  convert_to ⨅ n : {m | G.Colorable m}, (n : ℕ∞) ≠ ⊤ ↔ _
  · rw [iInf_subtype]
  rw [← lt_top_iff_ne_top, ENat.iInf_coe_lt_top]
  simp

theorem chromaticNumber_le_iff_colorable {n : ℕ} : G.chromaticNumber ≤ n ↔ G.Colorable n := by
  refine ⟨fun h ↦ ?_, Colorable.chromaticNumber_le⟩
  have : G.chromaticNumber ≠ ⊤ := (trans h (WithTop.coe_lt_top n)).ne
  rw [chromaticNumber_ne_top_iff_exists] at this
  obtain ⟨m, hm⟩ := this
  rw [hm.chromaticNumber_eq_sInf, Nat.cast_le] at h
  have := Nat.sInf_mem (⟨m, hm⟩ : {n' | G.Colorable n'}.Nonempty)
  rw [Set.mem_setOf_eq] at this
  exact this.mono h

/-- If the chromatic number of `G` is `n + 1`, then `G` is colorable in no fewer than `n + 1`
colors. -/
theorem chromaticNumber_eq_iff_colorable_not_colorable :
    G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n := by
  rw [eq_iff_le_not_lt, not_lt, ENat.add_one_le_iff (ENat.coe_ne_top n), ← not_le,
    chromaticNumber_le_iff_colorable, ← Nat.cast_add_one, chromaticNumber_le_iff_colorable]

theorem colorable_chromaticNumber {m : ℕ} (hc : G.Colorable m) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  classical
  rw [hc.chromaticNumber_eq_sInf, Nat.sInf_def]
  · apply Nat.find_spec
  · exact colorable_set_nonempty_of_colorable hc

theorem colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype

theorem chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] :
    G.chromaticNumber ≤ 1 := by
  rw [← Nat.cast_one, chromaticNumber_le_iff_colorable]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w
  cases Subsingleton.elim v w
  simp

theorem chromaticNumber_eq_zero_of_isempty (G : SimpleGraph V) [IsEmpty V] :
    G.chromaticNumber = 0 := by
  rw [← nonpos_iff_eq_zero, ← Nat.cast_zero, chromaticNumber_le_iff_colorable]
  apply colorable_of_isEmpty

theorem isEmpty_of_chromaticNumber_eq_zero (G : SimpleGraph V) [Finite V]
    (h : G.chromaticNumber = 0) : IsEmpty V := by
  have h' := G.colorable_chromaticNumber_of_fintype
  rw [h] at h'
  exact G.isEmpty_of_colorable_zero h'

theorem chromaticNumber_pos [Nonempty V] {n : ℕ} (hc : G.Colorable n) : 0 < G.chromaticNumber := by
  rw [hc.chromaticNumber_eq_sInf, Nat.cast_pos]
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁ : i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁

theorem colorable_of_chromaticNumber_ne_top (h : G.chromaticNumber ≠ ⊤) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  rw [chromaticNumber_ne_top_iff_exists] at h
  obtain ⟨n, hn⟩ := h
  exact colorable_chromaticNumber hn

theorem Colorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ} (hc : G'.Colorable n) :
    G.Colorable n :=
  ⟨hc.some.comp (.ofLE h)⟩

theorem chromaticNumber_le_of_forall_imp {V' : Type*} {G' : SimpleGraph V'}
    (h : ∀ n, G'.Colorable n → G.Colorable n) :
    G.chromaticNumber ≤ G'.chromaticNumber := by
  rw [chromaticNumber, chromaticNumber]
  simp only [Set.mem_setOf_eq, le_iInf_iff]
  intro m hc
  have := h _ hc
  rw [← chromaticNumber_le_iff_colorable] at this
  exact this

theorem chromaticNumber_mono (G' : SimpleGraph V)
    (h : G ≤ G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h

theorem chromaticNumber_mono_of_embedding {V' : Type*} {G' : SimpleGraph V'}
    (f : G ↪g G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ => Colorable.of_embedding f

lemma card_le_chromaticNumber_iff_forall_surjective [Fintype α] :
    card α ≤ G.chromaticNumber ↔ ∀ C : G.Coloring α, Surjective C := by
  refine ⟨fun h C ↦ ?_, fun h ↦ ?_⟩
  · rw [C.colorable.chromaticNumber_eq_sInf, Nat.cast_le] at h
    intro i
    by_contra! hi
    let D : G.Coloring {a // a ≠ i} := ⟨fun v ↦ ⟨C v, hi v⟩, (C.valid · <| congr_arg Subtype.val ·)⟩
    classical
    exact Nat.notMem_of_lt_sInf ((Nat.sub_one_lt_of_lt <| card_pos_iff.2 ⟨i⟩).trans_le h)
      ⟨G.recolorOfEquiv (equivOfCardEq <| by simp) D⟩
  · simp only [chromaticNumber, Set.mem_setOf_eq, le_iInf_iff, Nat.cast_le]
    rintro i ⟨C⟩
    contrapose! h
    refine ⟨G.recolorOfCardLE (by simpa using h.le) C, fun hC ↦ ?_⟩
    dsimp at hC
    simpa [h.not_ge] using Fintype.card_le_of_surjective _ hC.of_comp

lemma le_chromaticNumber_iff_forall_surjective :
    n ≤ G.chromaticNumber ↔ ∀ C : G.Coloring (Fin n), Surjective C := by
  simp [← card_le_chromaticNumber_iff_forall_surjective]

lemma chromaticNumber_eq_card_iff_forall_surjective [Fintype α] (hG : G.Colorable (card α)) :
    G.chromaticNumber = card α ↔ ∀ C : G.Coloring α, Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq, card_le_chromaticNumber_iff_forall_surjective]

lemma chromaticNumber_eq_iff_forall_surjective (hG : G.Colorable n) :
    G.chromaticNumber = n ↔ ∀ C : G.Coloring (Fin n), Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq, le_chromaticNumber_iff_forall_surjective]

theorem chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 := by
  have : (⊥ : SimpleGraph V).Colorable 1 := ⟨.mk 0 <| by simp⟩
  exact this.chromaticNumber_le.antisymm <| Order.one_le_iff_pos.2 <| chromaticNumber_pos this

@[simp]
theorem chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  rw [chromaticNumber_eq_card_iff_forall_surjective (selfColoring _).colorable]
  intro C
  rw [← Finite.injective_iff_surjective]
  intro v w
  contrapose
  intro h
  exact C.valid h

theorem chromaticNumber_top_eq_top_of_infinite (V : Type*) [Infinite V] :
    (⊤ : SimpleGraph V).chromaticNumber = ⊤ := by
  by_contra hc
  rw [← Ne, chromaticNumber_ne_top_iff_exists] at hc
  obtain ⟨n, ⟨hn⟩⟩ := hc
  exact not_injective_infinite_finite _ hn.injective_of_top_hom

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def CompleteBipartiteGraph.bicoloring (V W : Type*) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)

theorem CompleteBipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  rw [← Nat.cast_two, chromaticNumber_eq_iff_forall_surjective
    (by simpa using (CompleteBipartiteGraph.bicoloring V W).colorable)]
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  by_cases he' : C (Sum.inr w) = b
  · exact ⟨_, he'⟩
  · simpa using two_lt_card_iff.2 ⟨_, _, _, C.valid h, he, he'⟩

/-! ### Cliques -/


theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α]
    (C : G.Coloring α) : s.card ≤ Fintype.card α := by
  rw [isClique_iff_induce_eq] at h
  have f : G.induce ↑s ↪g G := Embedding.comap (Function.Embedding.subtype fun x => x ∈ ↑s) G
  rw [h] at f
  convert Fintype.card_le_of_injective _ (C.comp f.toHom).injective_of_top_hom using 1
  simp

theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) {n : ℕ}
    (hc : G.Colorable n) : s.card ≤ n := by
  convert h.card_le_of_coloring hc.some
  simp

theorem IsClique.card_le_chromaticNumber {s : Finset V} (h : G.IsClique s) :
    s.card ≤ G.chromaticNumber := by
  obtain (hc | hc) := eq_or_ne G.chromaticNumber ⊤
  · rw [hc]
    exact le_top
  · have hc' := hc
    rw [chromaticNumber_ne_top_iff_exists] at hc'
    obtain ⟨n, c⟩ := hc'
    rw [← ENat.coe_toNat_eq_self] at hc
    rw [← hc, Nat.cast_le]
    exact h.card_le_of_colorable (colorable_chromaticNumber c)

protected theorem Colorable.cliqueFree {n m : ℕ} (hc : G.Colorable n) (hm : n < m) :
    G.CliqueFree m := by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)

theorem cliqueFree_of_chromaticNumber_lt {n : ℕ} (hc : G.chromaticNumber < n) :
    G.CliqueFree n := by
  have hne : G.chromaticNumber ≠ ⊤ := hc.ne_top
  obtain ⟨m, hc'⟩ := chromaticNumber_ne_top_iff_exists.mp hne
  have := colorable_chromaticNumber hc'
  refine this.cliqueFree ?_
  rw [← ENat.coe_toNat_eq_self] at hne
  rw [← hne] at hc
  simpa using hc

/--
Given a colouring `α` of `G`, and a clique of size at least the number of colours, the clique
contains a vertex of each colour.
-/
lemma Coloring.surjOn_of_card_le_isClique [Fintype α] {s : Finset V} (h : G.IsClique s)
    (hc : Fintype.card α ≤ s.card) (C : G.Coloring α) : Set.SurjOn C s Set.univ := by
  intro _ _
  obtain ⟨_, hx⟩ := card_le_chromaticNumber_iff_forall_surjective.mp
                    (by simp_all [isClique_iff_induce_eq]) (C.comp (Embedding.induce s).toHom) _
  exact ⟨_, Subtype.coe_prop _, hx⟩

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι → Type*)

/-- The canonical `ι`-coloring of a `completeMultipartiteGraph` with parts indexed by `ι` -/
def coloring : (completeMultipartiteGraph V).Coloring ι := Coloring.mk (fun v ↦ v.1) (by simp)

lemma colorable [Fintype ι] : (completeMultipartiteGraph V).Colorable (Fintype.card ι) :=
  (coloring V).colorable

theorem chromaticNumber [Fintype ι] (f : ∀ (i : ι), V i) :
    (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι := by
  apply le_antisymm (colorable V).chromaticNumber_le
  by_contra! h
  exact not_cliqueFree_of_le_card V f le_rfl <| cliqueFree_of_chromaticNumber_lt h

theorem colorable_of_cliqueFree (f : ∀ (i : ι), V i)
    (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => exact absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf ↦ not_cliqueFree_of_infinite V f hc
  apply (coloring V).colorable.mono
  have := not_cliqueFree_of_le_card V f le_rfl
  contrapose! this
  exact hc.mono this

end completeMultipartiteGraph

/-- If `H` is not `n`-colorable and `G` is `n`-colorable, then `G` is `H.Free`. -/
theorem free_of_colorable {W : Type*} {H : SimpleGraph W}
    (nhc : ¬H.Colorable n) (hc : G.Colorable n) : H.Free G := by
  contrapose! nhc with hc'
  rw [not_free] at hc'
  exact ⟨hc.some.comp hc'.some.toHom⟩

end SimpleGraph
