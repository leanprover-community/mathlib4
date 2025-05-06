/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
--import Mathlib.Combinatorics.SimpleGraph.Brooks.ColoringComponents
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Brooks.PartColoring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
Develop Greedy colorings of a `G : SimpleGraph α` using the`SimpleGraph.PartColoring`.

Prove the basic greedy coloring bound `∀ v, G.degree v ≤ n → G.Colorable (n + 1)`

Develop greedy partial colorings along paths to enable a proof of Brooks theorem.

Given `C`, a `β` - coloring of `G.induce s`, (where `Fintype β`) the set of `valid` colors
that we can use to extend `C` to `s.insert a` is:
 `(((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ`, so we need this to be Nonempty inorder
 to proceed.
-/


namespace SimpleGraph
open Subgraph PartColoring

variable {α β : Type*} {G : SimpleGraph α} {s : Set α} [DecidablePred (· ∈ s)]

open Finset
section greedy

-- variable {γ : Type*} [DecidableEq γ] [LT γ]
-- noncomputable abbrev PartColoring.greedyWF (C₁ : G.PartColoring γ s) (a : α)
--     (hwf : WellFounded ((· < ·) : γ → γ → Prop)) [Fintype (G.neighborSet a)]
--     (h : ((((G.neighborFinset a).filter (· ∈ s)).image C₁) : Set γ)ᶜ.Nonempty) :
--     G.PartColoring γ  (insert a s) := by
--   have h' : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ hwf.min _  h := by
--     intro _ hv had he
--     apply mem_compl.1 <| hwf.min_mem _ h
--     exact mem_image.2 ⟨_, mem_filter.2 ⟨(G.mem_neighborFinset ..).2 had, hv⟩, he⟩
--   exact C₁.insert a (hwf.min _ h) h'


variable [Fintype β] [DecidableEq β]

section DecEq

variable [DecidableEq α]
/-- If we have a `β` - coloring of `G.induce s` and `G` has less than `|β|` neighbors in `s` then
the set of valid colors at `a` is nonempty.
-/
lemma PartColoring.nonempty_of_degreeInduce_lt [DecidableRel G.Adj] (C : G.PartColoring β s) (a : α)
    [Fintype (G.neighborSet a)] (h : G.degreeInduce (insert a s) a < Fintype.card β) :
    (((G.neighborFinset a).filter (· ∈ s)).image C)ᶜ.Nonempty := by
  contrapose! h
  simp only [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at h
  have := card_image_le (f := C) (s := {x ∈ G.neighborFinset a | x ∈ s})
  simp only [h, card_univ, Fintype.card_fin] at this
  rwa [degreeInduce_insert_eq]

/-- If we have a `β` - coloring `C` of `G.induce s` and `G` has at most `|β|` neighbors in `s` *and*
at least two of these neighbors received the same color in `C` then the set of valid colors at `a`
is nonempty.
-/
lemma PartColoring.nonempty_of_degreeInduce_le_not_inj {u v : α} [DecidableRel G.Adj]
    (C : G.PartColoring β s) (a : α) [Fintype (G.neighborSet a)]
    (h : G.degreeInduce (insert a s) a ≤ Fintype.card β) (hus : u ∈ s) (hvs : v ∈ s)
    (hu : G.Adj a u) (hv : G.Adj a v) (hne : u ≠ v) (heq : C u = C v) :
    (((G.neighborFinset a).filter (· ∈ s)).image C)ᶜ.Nonempty := by
  cases h.lt_or_eq with
  | inl h => exact C.nonempty_of_degreeInduce_lt a h
  | inr h =>
  contrapose! hne
  simp only [not_nonempty_iff_eq_empty, compl_eq_empty_iff] at hne
  rw [degreeInduce_insert_eq,  ← card_univ] at h
  exact card_image_iff.1 (h ▸ congr_arg card hne) (by simp [*]) (by simp [*]) heq

variable [LinearOrder β]
/-- If there is an unused color in the neighborhood of `a` under the coloring of `s` by `C` then
we can color `insert a s` greedily. -/
abbrev PartColoring.greedy (C : G.PartColoring β s) (a : α) [Fintype (G.neighborSet a)]
    (h : (((G.neighborFinset a).filter (· ∈ s)).image C)ᶜ.Nonempty) :
    G.PartColoring β (insert a s) := by
  have h' : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C v ≠ (min' _ h) := by
    intro _ hv had he
    apply mem_compl.1 <| min'_mem _ h
    exact mem_image.2 ⟨_, mem_filter.2 ⟨(G.mem_neighborFinset ..).2 had, hv⟩, he⟩
  exact C.insert a h'

variable {a : α}
@[simp]
lemma PartColoring.greedy_extends_not_mem (C : G.PartColoring β s) (ha : a ∉ s)
    [Fintype (G.neighborSet a)] (h) : (C.greedy a h).Extends C := C.insert_extends_not_mem _ ha

@[simp]
lemma PartColoring.greedy_extends (C : G.PartColoring β s) [Fintype (G.neighborSet a)] (h) :
  (C.greedy a h).Extends (G.partColoringOfSingleton a (min' _ h)) := C.insert_extends _

end DecEq

variable {n : ℕ}
lemma part_colorable_succ_finset_of_forall_degree_le [LocallyFinite G] (h : ∀ v, G.degree v ≤ n)
  (s : Finset α) : G.PartColorable (n + 1) s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ 0, by simp⟩
  | @insert a _ _ hC =>
    have := hC.some.nonempty_of_degreeInduce_lt a ((degreeInduce_le_degree ..).trans_lt
      ((Fintype.card_fin _).symm ▸ Nat.lt_add_one_iff.mpr (h a)))
    exact ⟨(hC.some.greedy a this).copy (by simp)⟩

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


/-!

We now look at more elaborate greedy colorings that will allow us to prove Brook's theorem.

-/

open Walk List
variable [LinearOrder β] [DecidableEq α]
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
    have h' : G.degreeInduce (insert v (s ∪ {a | a ∈ p.support.tail})) v < Fintype.card β :=
      (G.degreeInduce_insert_lt_degree h.symm hu).trans_le (hbd v (Or.inr p.start_mem_support))
    exact (C₂.greedy v (C₂.nonempty_of_degreeInduce_lt v h')).copy (by
      ext x; rw [support_eq_cons]; simp [or_left_comm])

lemma PartColoring.of_tail_path_extends {u v : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring β s) (hp : p.IsPath)
    (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) : (C₁.of_tail_path hp hbd disj).Extends C₁ := by
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
  exact (C₂.greedy u (C₂.nonempty_of_degreeInduce_le_not_inj u
        ((degreeInduce_le_degree ..).trans (hbd u p.start_mem_support)) (Or.inl hxs) (Or.inl hys)
        hux huy hne he)).copy (by ext; rw [support_eq_cons]; simp [or_left_comm])

lemma PartColoring.of_path_not_inj_extends {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring β s) (hp : p.IsPath)
    (hbd : ∀ x, x ∈ p.support → G.degree x ≤ Fintype.card β)
    (disj : Disjoint s {a | a ∈ p.support}) (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x)
    (huy : G.Adj u y) (hne : x ≠ y) (heq : C₁ x = C₁ y) :
    (C₁.of_path_not_inj hp hbd disj hxs hys hux huy hne heq).Extends C₁ := by
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
