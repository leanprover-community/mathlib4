/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
--import Mathlib.Combinatorics.SimpleGraph.Brooks.ColoringComponents
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
/-!
Develop partial colorings of a `G : SimpleGraph α` using the`SimpleGraph.Coloring` API.

We want a partial `β`-coloring of `G` to be a map `C : α → β` that is valid on a given
subset of the vertices `s : Set α`. Where valid means `∀ a b ∈ s, G.Adj a b → C a ≠ C b`.

So given `G` and `s` we need a `SimpleGraph α` on which `SimpleGraph.Coloring`s look like this.

The obvious choice is `(G.induce s).spanningCoe` but an alternative choice is
`(⊤ : Subgraph G).induce s).spanningCoe`.

Propositionally these are the same thing but `(⊤ : Subgraph G).induce s).spanningCoe` has nicer
definitional properties.

If  `H := (⊤ : Subgraph G).induce s).spanningCoe` then `H.Adj a b` is `a ∈ s ∧ b ∈ s ∧ G.Adj a b`
while if `H := (G.induce s).spanningCoe` then `H.Adj a b` is
`(G.comap (Function.Embedding.subtype s)).map (Function.Embedding.subtype _).Adj a b`.
-/

namespace SimpleGraph
open Subgraph

variable {α : Type*} (G : SimpleGraph α)

lemma induce_spanningCoe_eq_top_subgraph_induce_spanningCoe (s : Set α) :
    (G.induce s).spanningCoe = ((⊤ : Subgraph G).induce s).spanningCoe := by
  ext; simp [and_left_comm]

lemma induce_spanningCoe_adj (s : Set α) (a b : α) : (G.induce s).spanningCoe.Adj a b ↔
    ((G.comap (Function.Embedding.subtype s)).map (Function.Embedding.subtype _)).Adj a b := Iff.rfl

lemma top_subgraph_induce_spanningCoe_adj (s : Set α) (a b : α) :
    ((⊤ : Subgraph G).induce s).spanningCoe.Adj a b ↔ a ∈ s ∧ b ∈ s ∧ G.Adj a b := Iff.rfl

/- The neighbors of `a` in `G.induce s` as a `SimpleGraph α` -/
@[simp]
abbrev neighborSetIn (s : Set α) (a : α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.neighborSet a

@[simp]
lemma mem_neighborSetIn {s : Set α} {a v : α} :
  v ∈ G.neighborSetIn s a ↔ a ∈ s ∧ v ∈ s ∧ G.Adj a v := by simp

lemma neighborSetIn_eq_inter_of_mem {s : Set α} {a : α} (ha : a ∈ s) :
    G.neighborSetIn s a = G.neighborSet a ∩ s := by
  aesop

@[simp]
lemma neighborSetIn_insert_eq (s : Set α) (a : α) :
    G.neighborSetIn (insert a s) a = {x | x ∈ s ∧ G.Adj a x} := by
  rw [neighborSetIn_eq_inter_of_mem _ (Set.mem_insert ..)]
  aesop

section withDecRel

variable [DecidableRel G.Adj] {s : Set α} [DecidablePred (· ∈ s)]

/-- If a graph is locally finite at a vertex, then so is any subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)


/-- If a graph is locally finite at a vertex, then so is any spanningCoe of a
subgraph of that graph. -/
instance finiteAtCoe {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.spanningCoe.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

abbrev neighborFinsetIn (s : Set α) (a : α) [Fintype (G.neighborSetIn s a)] :=
  ((⊤ : Subgraph G).induce s).spanningCoe.neighborFinset a

@[simp]
lemma neighborFinsetIn_insert_eq (s : Set α) (a : α) [DecidablePred (· ∈ s)] [DecidableEq α]
    [Fintype (G.neighborSet a)] :
    G.neighborFinsetIn (insert a s) a = (G.neighborFinset a).filter (· ∈ s) := by
  ext x; simp only [mem_neighborFinset, spanningCoe_adj, induce_adj, Set.mem_insert_iff, true_or,
    Subgraph.top_adj, true_and, Finset.mem_filter]
  constructor <;> intro h
  · cases h.1 with
    | inl h' => subst x; exact (G.loopless _ h.2).elim
    | inr h' => exact ⟨h.2, h'⟩
  · exact ⟨Or.inr h.2, h.1⟩


abbrev degreeIn (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)]  :=
  ((⊤ : Subgraph G).induce s).spanningCoe.degree a

lemma degreeIn_eq (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)] :
  G.degreeIn s a = ((⊤ : Subgraph G).induce s).degree a := by simp

open Finset
@[simp]
lemma degreeIn_insert_eq (s : Set α) (a : α) [DecidablePred (· ∈ s)] [DecidableEq α]
    [Fintype (G.neighborSet a)] :
    G.degreeIn (insert a s) a = #((G.neighborFinset a).filter (· ∈ s)) := by
  rw [← neighborFinsetIn_insert_eq]
  rfl

lemma degreeIn_insert_lt_degree {s : Set α} {a v : α} (h : G.Adj a v) (hv : v ∉ s)
  [DecidablePred (· ∈ s)] [DecidableEq α] [Fintype (G.neighborSet a)] :
    G.degreeIn (insert a s) a < G.degree a := by
  rw [degreeIn_insert_eq, ← card_neighborFinset_eq_degree]
  exact card_lt_card <| filter_ssubset.2 ⟨v, (G.mem_neighborFinset ..).2 h, hv⟩

variable {t : Set α} [DecidablePred (· ∈ t)] {a : α} [Fintype (G.neighborSet a)]

lemma degreeIn_mono (h : s ⊆ t) : G.degreeIn s a ≤ G.degreeIn t a := by
  rw [degreeIn_eq, degreeIn_eq]
  exact (degree_le' _ _ (induce_mono_right h) a)

variable (a) in
lemma degreeIn_le_degree : G.degreeIn s a ≤ G.degree a := by
  rw [degreeIn_eq]
  exact degree_le _ _

lemma neighborSet_subset_of_degree_le_degreeIn (h : G.degree a ≤ G.degreeIn s a) :
      G.neighborSet a ⊆ s := by
  rw [degree, degreeIn_eq, ← finset_card_neighborSet_eq_degree] at h
  intro v ha
  apply ((⊤ : Subgraph G).induce s).neighborSet_subset_verts a
  rwa [← Set.mem_toFinset, eq_of_subset_of_card_le (fun v ↦ by simp) h, mem_neighborFinset]

lemma degreeIn_lt_degree {v : α} (hv : v ∈ G.neighborSet a ∧ v ∉ s) :
    G.degreeIn s a < G.degree a :=
  lt_of_le_of_ne (G.degreeIn_le_degree a)
    fun h ↦ hv.2 <| G.neighborSet_subset_of_degree_le_degreeIn h.symm.le hv.1

end withDecRel
/--
A `PartColoring β s` of `G : SimpleGraph α` is an `β`-coloring of all vertices of `G` that is
a valid coloring on the set `s` -/
abbrev PartColoring (β : Type*) (s : Set α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.Coloring β

variable {s t u : Set α} {β : Type*} {G}
/--
`C₂ : G.PartColoring β t` extends `C₁ : G.PartColoring β s` if `s ⊆ t` and `C₂` agrees with `C₁`
on `s`
-/
protected def PartColoring.extends (C₂ : G.PartColoring β t) (C₁ : G.PartColoring β s) : Prop :=
  s ⊆ t ∧ ∀ ⦃v⦄, v ∈ s → C₂ v = C₁ v

namespace PartColoring

@[refl, simp]
lemma extends_refl {C₁ : G.PartColoring β s} : C₁.extends C₁ := ⟨subset_refl _, fun _ _ ↦ rfl⟩

@[trans, simp]
lemma extends_trans {C₃ : G.PartColoring β u} {C₂ : G.PartColoring β t} {C₁ : G.PartColoring β s}
    (h1 : C₂.extends C₁) (h2: C₃.extends C₂) : C₃.extends C₁ := by
  refine ⟨subset_trans h1.1 h2.1,?_⟩
  intro v hv
  rw [← h1.2 hv, h2.2 (h1.1 hv)]

/-- Construct a `G.PartColoring β t` from `C : G.PartColoring β s` and proof that `s = t` -/
@[simp]
def copy (C : G.PartColoring β s) (h : s = t) : G.PartColoring β t where
  toFun := C.toFun
  map_rel' := by
    subst h
    exact C.map_rel'

@[simp]
theorem copy_rfl  (C : G.PartColoring β s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartColoring β s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_def (C: G.PartColoring β s) (h : s = t) {v : α} :
  (C.copy h) v  = C v := rfl

@[simp]
lemma copy_extends {C₂ : G.PartColoring β t} {C₁ : G.PartColoring β s} (hc : C₂.extends C₁)
  {h : t = u} : (C₂.copy h).extends C₁ :=
    ⟨fun _ hx ↦ h ▸ hc.1 hx, fun _ hv ↦ by rw [copy_def]; exact hc.2 hv⟩

/-- A `G.PartColoring β Set.univ` is a `G.Coloring (Fin n)` -/
def toColoring (C : G.PartColoring β Set.univ) : G.Coloring β :=
    ⟨C, fun h ↦ C.valid (by simpa using h)⟩

end PartColoring

variable (G)

/-- We can color `{a}` with any color -/
def partColoringOfSingleton {β : Type*} (a : α) (c : β) : G.PartColoring β ({a} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by simp

@[simp]
lemma partColoringOfSingleton_def {β : Type*} {a v : α} {c : β} :
  G.partColoringOfSingleton a c v = c := rfl

/-- If `¬ G.Adj a b` then we can color `{a, b}` with any single color -/
def partColoringOfNotAdj {β : Type*} {a b : α} (h : ¬ G.Adj a b) (c : β) :
    G.PartColoring β ({a, b} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by
    intro x y hadj he
    cases hadj.1 <;> cases hadj.2.1 <;> subst_vars
    · exact G.loopless _ hadj.2.2
    · exact h hadj.2.2
    · exact h hadj.2.2.symm
    · exact G.loopless _ hadj.2.2

/-- `G.PartColorable n s` is the predicate for existence of a `PartColoring (Fin n) s` of `G`, i.e.
the subgraph of `G` induced by `s` is `n`-colorable. -/
abbrev PartColorable (n : ℕ) (s : Set α) := Nonempty (G.PartColoring (Fin n) s)

variable {G} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]

/--
We can combine colorings `C₁` of `s` and `C₂` of `t` if they are compatible i.e.
`∀ v w, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w` to get a coloring of `s ∪ t`.
This will extend `C₁` and, if `Disjoint s t`, it will also extend `C₂`.
-/
def PartColoring.union (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : G.PartColoring β (s ∪ t) where
  toFun := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  map_rel' := by
      simp only [spanningCoe_adj, induce_adj, Set.mem_union, Subgraph.top_adj, top_adj, ne_eq,
        and_imp]
      intro v w hv' hw' hadj hf
      by_cases hv : v ∈ s
      · by_cases hws : w ∈ s
        · rw [if_pos hv, if_pos hws] at hf
          exact C₁.valid (by simpa using ⟨hv, hws, hadj⟩) hf
        · by_cases hw : w ∈ t
          · rw [if_pos hv, if_neg hws] at hf
            exact h hv ⟨hw, hws⟩ hadj hf
          · exact hws <| Or.resolve_right hw' hw
      · by_cases hws : w ∈ s
        · rw [if_neg hv, if_pos hws] at hf
          exact h hws ⟨Or.resolve_left hv' hv, hv⟩ hadj.symm hf.symm
        · by_cases hw : w ∈ t
          · rw [if_neg hv, if_neg hws] at hf
            exact C₂.valid (by simpa using ⟨Or.resolve_left hv' hv, hw, hadj⟩) hf
          · exact hw <| Or.resolve_left hw' hws

@[simp]
lemma PartColoring.union_def {v : α} (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
  (C₁.union C₂ h) v = ite (v ∈ s) (C₁ v) (C₂ v) := rfl

@[simp]
lemma PartColoring.union_extends (C₁ : G.PartColoring β s) (C₂ : G.PartColoring β t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : (C₁.union C₂ h).extends C₁ :=
  ⟨Set.subset_union_left, fun _ hv ↦ by rw [union_def, if_pos hv]⟩

@[simp]
lemma PartColoring.union_extends_disjoint (hd : Disjoint s t) (C₁ : G.PartColoring β s)
    (C₂ : G.PartColoring β t) (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
    (C₁.union C₂ h).extends C₂ :=
  ⟨Set.subset_union_right, fun _ hv ↦ by rw [union_def, if_neg (hd.not_mem_of_mem_right hv)]⟩


variable [DecidableEq α]

/-- The extension of a coloring of `s` to `insert a s` using a color `c` that is not used by `C₁` to
color a neighbor of `a` in `s` -/
protected def PartColoring.insert (a : α) (c : β) (C₁ : G.PartColoring β s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) : G.PartColoring β (insert a s) :=
  ((G.partColoringOfSingleton a c).union C₁ (by
    simp only [Set.mem_singleton_iff, Set.mem_diff, and_imp]
    rintro _ _ rfl h' h1 had h2
    exact h h' had h2.symm)).copy (by simp [Set.union_comm])

variable {a v : α} {c : β}

@[simp]
lemma PartColoring.insert_def (C₁ : G.PartColoring β s) (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) :
    (C₁.insert a c h) v = ite (v = a) c (C₁ v) := by
  rw [PartColoring.insert, copy_def, union_def]
  simp

@[simp]
lemma PartColoring.insert_extends {c : β} (C₁ : G.PartColoring β s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) :
    (C₁.insert a c h).extends (G.partColoringOfSingleton a c) := copy_extends (union_extends ..)

@[simp]
lemma PartColoring.insert_extends_not_mem (C₁ : G.PartColoring β s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) (ha : a ∉ s) : (C₁.insert a c h).extends C₁ :=
  copy_extends <| union_extends_disjoint (Set.disjoint_singleton_left.mpr ha) ..

open Finset
section greedy
/-!
Greedy colorings with infinitely many colors are not very interesting so we restrict
to `Fintype β`.
-/
variable [Fintype β] [DecidableEq β] [LinearOrder β]
/-- If there is an unused color in the neighborhood of `a` under the coloring of `s` by `C₁` then
we can color `insert a s` greedily. -/
abbrev PartColoring.greedy (C₁ : G.PartColoring β s) (a : α) [Fintype (G.neighborSet a)]
    (h : (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty) :
    G.PartColoring β (insert a s) := by
  have h' : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ (min' _ h) := by
    intro _ hv had he
    apply mem_compl.1 <| min'_mem _ h
    exact mem_image.2 ⟨_, mem_filter.2 ⟨(G.mem_neighborFinset ..).2 had, hv⟩, he⟩
  exact C₁.insert a (min' _ h) h'

@[simp]
lemma PartColoring.greedy_extends_not_mem (C₁ : G.PartColoring β s) (ha : a ∉ s)
    [Fintype (G.neighborSet a)] (h) : (C₁.greedy a h).extends C₁ := C₁.insert_extends_not_mem _ ha

@[simp]
lemma PartColoring.greedy_extends (C₁ : G.PartColoring β s) [Fintype (G.neighborSet a)] (h) :
  (C₁.greedy a h).extends (G.partColoringOfSingleton a (min' _ h)) := C₁.insert_extends _

omit [LinearOrder β] in
lemma PartColoring.nonempty_of_degreeIn_lt [DecidableRel G.Adj] (C₁ : G.PartColoring β s) (a : α)
    [Fintype (G.neighborSet a)] (h : G.degreeIn (insert a s) a < Fintype.card β) :
    (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty := by
  contrapose! h
  simp only [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at h
  have := card_image_le (f := C₁) (s := {x ∈ G.neighborFinset a | x ∈ s})
  simp only [h, card_univ, Fintype.card_fin] at this
  rwa [degreeIn_insert_eq]

omit [DecidableEq α]
variable {n : ℕ}
lemma part_colorable_succ_finset_of_forall_degree_le [LocallyFinite G] (h : ∀ v, G.degree v ≤ n)
  (s : Finset α) : G.PartColorable (n + 1) s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ 0, by simp⟩
  | @insert a _ _ hC₁ =>
    have := hC₁.some.nonempty_of_degreeIn_lt a ((degreeIn_le_degree ..).trans_lt
      ((Fintype.card_fin _).symm ▸ Nat.lt_add_one_iff.mpr (h a)))
    exact ⟨(hC₁.some.greedy a this).copy (by simp)⟩

/--
Every graph with `∀ v, G.degree v ≤ k` is `k + 1`-colorable.
-/
theorem colorable_succ_of_forall_degree_le [LocallyFinite G] {k : ℕ} (h : ∀ v, G.degree v ≤ k) :
    G.Colorable (k + 1) := by
  apply nonempty_hom_of_forall_finite_subgraph_hom
  intro G' hf
  classical
  have h' : ∀ v, G'.coe.degree v ≤ k := by
    intro v; rw [Subgraph.coe_degree]; exact (Subgraph.degree_le ..).trans (h ..)
  haveI : Fintype ↑G'.verts := hf.fintype
  exact ((part_colorable_succ_finset_of_forall_degree_le h' univ).some.copy coe_univ).toColoring


--- We now look at more elaborate greedy colorings that will allow us to prove Brook's theorem.
omit [LinearOrder β] in
lemma PartColoring.nonempty_of_degreeIn_le_not_inj {u v : α} [DecidableRel G.Adj] [DecidableEq α]
    (C₁ : G.PartColoring β s) (a : α) [Fintype (G.neighborSet a)]
    (h : G.degreeIn (insert a s) a ≤ Fintype.card β) (hus : u ∈ s) (hvs : v ∈ s)
    (hu : G.Adj a u) (hv : G.Adj a v) (hne : u ≠ v) (heq : C₁ u = C₁ v) :
    (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty := by
  cases h.lt_or_eq with
  | inl h => exact C₁.nonempty_of_degreeIn_lt a h
  | inr h =>
  contrapose! hne
  simp only [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at hne
  rw [degreeIn_insert_eq,  ← card_univ] at h
  exact card_image_iff.1 (h ▸ congr_arg card hne) (by simp [*]) (by simp [*]) heq

open Walk List
/-- We can color greedily along a path to extend a coloring of `s` to a coloring of
`s ∪ p.support.tail` if the vertices in the path have bounded degree -/
def PartColoring.of_tail_path {u v : α} {p : G.Walk u v} [LocallyFinite G] (C₁ : G.PartColoring β s)
    (hp : p.IsPath) (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) : G.PartColoring β (s ∪ {a | a ∈ p.support.tail}) := by
  match p with
  | .nil => exact C₁.copy (by simp)
  | .cons h p =>
    classical
    rename_i _ v
    rw [cons_isPath_iff] at hp
    simp_rw [support_cons, List.tail, List.mem_cons] at *
    have hd := disj.mono_right (fun _ hx ↦ Or.inr hx)
    have hs := disj.mono_right (fun _ hx ↦ Or.inl hx)
    let C₂ := C₁.of_tail_path hp.1 (fun x hx ↦ hbd _ <| Or.inr hx) hd
    have hu : u ∉ s ∪ { a | a ∈ p.support.tail} := by
      intro hf; apply hp.2
      have := hf.resolve_left (fun hu ↦ hs.not_mem_of_mem_left hu rfl)
      exact mem_of_mem_tail this
    have h' : G.degreeIn (insert v (s ∪ {a | a ∈ p.support.tail})) v < Fintype.card β :=
      (G.degreeIn_insert_lt_degree h.symm hu).trans_le (hbd v (Or.inr p.start_mem_support))
    exact (C₂.greedy v (C₂.nonempty_of_degreeIn_lt v h')).copy (by
      ext x; rw [support_eq_cons]; simp [or_left_comm])

variable [DecidableEq α] in
lemma PartColoring.of_tail_path_extends {u v : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring β s) (hp : p.IsPath)
    (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) : (C₁.of_tail_path hp hbd disj).extends C₁ := by
  cases p with
  | nil => exact copy_extends <| extends_refl ..
  | cons h p =>
    rename_i _ v
    have hps : p.support = v :: p.support.tail := by nth_rw 1 [support_eq_cons]
    apply copy_extends
    · apply extends_trans
      · apply C₁.of_tail_path_extends hp.of_cons
        · intro _ hx; apply hbd
          rw [support_cons]
          exact mem_cons_of_mem _ hx
        · simp_rw [support_cons, List.mem_cons] at disj
          apply disj.mono_right (fun _ hx ↦ Or.inr hx)
      · apply greedy_extends_not_mem _
        intro hf
        cases hf with
        | inl hf =>
          apply disj.not_mem_of_mem_left hf
          simp
        | inr hf =>
          have := hp.of_cons.support_nodup ;
          rw [support_eq_cons] at this
          apply this.not_mem (by simpa using hf)
    · rw [support_cons, support_eq_cons]
      ext; simp [or_left_comm]

/-- We can color greedily along a path to extend a coloring of `s` to a coloring of
`s ∪ {a | a ∈ p.support}` if the vertices in the path have bounded degree and the start of the path
has two neighbors in `s` that are already colored with the same color. -/
def PartColoring.of_path_not_inj {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring β s) (hp : p.IsPath)
    (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x)
    (huy : G.Adj u y) (hne : x ≠ y) (heq : C₁ x = C₁ y)  :
    G.PartColoring β (s ∪ {a | a ∈ p.support}) := by
  let C₂ := C₁.of_tail_path hp hbd disj
  have he : C₂ x = C₂ y := by
    rwa [(C₁.of_tail_path_extends hp hbd disj).2 hxs, (C₁.of_tail_path_extends hp hbd disj).2 hys]
  classical
  exact (C₂.greedy u (C₂.nonempty_of_degreeIn_le_not_inj u
        ((degreeIn_le_degree ..).trans (hbd u p.start_mem_support)) (Or.inl hxs) (Or.inl hys)
        hux huy hne he)).copy (by ext; rw [support_eq_cons]; simp [or_left_comm])

variable [DecidableEq α]
lemma PartColoring.of_path_not_inj_extends {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring β s) (hp : p.IsPath)
    (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x)
    (huy : G.Adj u y) (hne : x ≠ y) (heq : C₁ x = C₁ y) :
    (C₁.of_path_not_inj hp hbd disj hxs hys hux huy hne heq).extends C₁ := by
  apply copy_extends
  · apply extends_trans (C₁.of_tail_path_extends hp hbd disj)
    apply (C₁.of_tail_path hp hbd disj).greedy_extends_not_mem
    intro hf
    cases hf with
    | inl hf => exact disj.not_mem_of_mem_left hf (by simp)
    | inr hf =>
      have := hp.support_nodup ;
      rw [support_eq_cons] at this
      exact this.not_mem (by simpa using hf)
  · nth_rw 2 [support_eq_cons]
    ext; simp [or_left_comm]

end greedy
end SimpleGraph
