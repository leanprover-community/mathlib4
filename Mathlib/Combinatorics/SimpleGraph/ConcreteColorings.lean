/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finite.Card
import Mathlib.Logic.Equiv.Fin

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

namespace SimpleGraph

/-- Bicoloring of a path graph -/
def pathGraph.bicoloring (n : ℕ) :
    Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/-- Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤ n` -/
def pathGraph_two_embedding (n : ℕ) (h : 2 ≤ n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covBy_iff]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · simpa only [pathGraph_two_eq_top, chromaticNumber_top] using
      chromaticNumber_mono_of_embedding (pathGraph_two_embedding n h)

theorem Coloring.even_length_iff_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Even p.length ↔ (c u ↔ c v) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      exact c.valid h
    tauto

theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd, c.even_length_iff_congr p]
  tauto

theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := Classical.by_contradiction <| by
  intro h
  have h' : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one <| not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_congr p).mp hOdd
  simp_all

def greedyColoringFn : {n : ℕ} → (G : SimpleGraph (Fin n)) → [DecidableRel G.Adj] → Fin n → ℕ
  | 0, _, _ => nofun
  | n' + 1, G, _ =>
    let G' : SimpleGraph (Fin n') := G.comap (Fin.castLEEmb (by omega))
    let c := greedyColoringFn G'
    fun v =>
      if hv : v.1 < n' then
        c ⟨v, hv⟩
      else
        let used := (G.neighborFinset v).image fun w =>
          if hw : w.1 < n' then c ⟨w.1, hw⟩
          else 0 -- doesn't happen
        Nat.find (p := fun k => k ∉ used) (Infinite.exists_not_mem_finset used)

def greedyColoring {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Coloring G ℕ :=
  Coloring.mk (greedyColoringFn G) <| by
    induction n with
    | zero => rintro ⟨_, ⟨⟩⟩
    | succ n ih =>
      intro ⟨v, hv⟩ ⟨w, hw⟩
      wlog hvw : v < w
      · obtain rfl | hvw := eq_or_lt_of_not_lt hvw
        · intro h; exact (G.irrefl h).elim
        · intro h; exact (this _ ih _ _ _ _ _ hvw h.symm).symm
      rw [Nat.lt_succ_iff_lt_or_eq] at hv hw
      obtain hv | rfl := hv <;> obtain hw | rfl := hw
      · intro ha
        have := @ih (G.comap (Fin.castLEEmb (by omega))) _ ⟨v, hv⟩ ⟨w, hw⟩
        simpa [greedyColoringFn, hv, hw, ha] using this
      · intro ha
        simp [greedyColoringFn, hv]
        generalize_proofs _ _ hpf
        have := Nat.find_spec hpf
        specialize this ⟨v, _⟩ ha.symm
        simpa [hv] using this
      · exfalso; omega
      · simp

lemma comap_neighborFinset_subset_neighborSet {V W} (G : SimpleGraph W) [LocallyFinite G]
    (f : V ↪ W) [LocallyFinite (G.comap f)] (v : V) :
    Finset.map f ((G.comap f).neighborFinset v) ⊆ G.neighborFinset (f v) := by
  intro w
  simp
  intros
  subst_vars
  assumption

lemma comap_degree_le_degree {V W} (G : SimpleGraph W) [LocallyFinite G]
    (f : V ↪ W) [LocallyFinite (G.comap f)] (v : V) :
    (G.comap f).degree v ≤ G.degree (f v) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  rw [← Finset.card_map f]
  convert Finset.card_le_card (comap_neighborFinset_subset_neighborSet G f v)

lemma comap_degree_eq_degree {V W} (G : SimpleGraph W) [LocallyFinite G]
    (f : V ≃ W) [LocallyFinite (G.comap f)] (v : V) :
    (G.comap f).degree v = G.degree (f v) := by
  apply le_antisymm
  · have : (SimpleGraph.comap (f.toEmbedding) G).LocallyFinite := by assumption
    convert comap_degree_le_degree G f.toEmbedding v
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  rw [← Finset.card_map f.toEmbedding]
  apply Finset.card_le_card
  intro x
  simp

theorem greedyColoring_prop {n d} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ v, G.degree v ≤ d) :
    ∀ v, G.greedyColoring v ≤ d := by
  induction n with
  | zero => rintro ⟨_, ⟨⟩⟩
  | succ n ih =>
    let G' : SimpleGraph (Fin n) := G.comap (Fin.castLEEmb (by omega))
    specialize ih G'
    intro ⟨v, hv⟩
    change G.greedyColoringFn _ ≤ _
    simp only [greedyColoringFn]
    obtain hv | rfl := Nat.lt_succ_iff_lt_or_eq.mp hv
    · simp [hv]
      apply ih
      intro w
      specialize h ⟨w, by omega⟩
      refine le_trans ?_ h
      apply comap_degree_le_degree
    · simp only [lt_self_iff_false, ↓reduceDIte]
      specialize ih ?_
      · intro w
        refine le_trans ?_ (h ⟨w.1, by omega⟩)
        apply comap_degree_le_degree
      simp only [Nat.find_le_iff]
      let used := (G.neighborFinset v).image fun w =>
        if hw : w.1 < v then G'.greedyColoringFn ⟨w.1, hw⟩ else 0
      have key1 : used ⊆ Finset.Iic d := by
        intro x
        simp only [Finset.mem_image, mem_neighborFinset, Finset.mem_Iio, forall_exists_index,
          and_imp, used]
        intro ⟨y, hy⟩
        obtain hy | rfl := Nat.lt_succ_iff_lt_or_eq.mp hy
        · simp [hy]
          rintro _ rfl
          apply ih
        · intro h
          convert_to G.Adj y y at h
          · ext; simp
          exact (G.irrefl h).elim
      have key2 : used.card ≤ d := by
        refine le_trans ?_ (h ⟨v, hv⟩)
        rw [← card_neighborFinset_eq_degree]
        refine le_of_le_of_eq Finset.card_image_le ?_
        congr!
        simp
      have key3 : used ⊂ Finset.Iic d := by
        rw [Finset.ssubset_def]
        refine ⟨key1, ?_⟩
        intro h
        have := Finset.card_le_card h
        simp at this
        omega
      rw [Finset.ssubset_iff] at key3
      obtain ⟨m, hm, hm'⟩ := key3
      refine ⟨m, ?_, ?_⟩
      · specialize hm' (Finset.mem_insert_self _ _)
        simpa using hm'
      simpa [used] using hm

theorem greedyColoring_le_maxDegree {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ v, G.greedyColoring v ≤ G.maxDegree :=
  greedyColoring_prop G (degree_le_maxDegree G)

noncomputable def greedyColoring' {V} [Finite V] (G : SimpleGraph V) : Coloring G ℕ :=
  haveI := Classical.dec
  letI e : V ≃ Fin (Nat.card V) := Finite.equivFin V
  (greedyColoring _).comp (Iso.comap e.symm G).symm.toHom

theorem greedyColoring'_le_maxDegree {V} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : G.greedyColoring' v ≤ G.maxDegree := by
  rw [greedyColoring']
  simp
  let e : V ≃ Fin (Nat.card V) := Finite.equivFin V
  have := greedyColoring_le_maxDegree (G.comap e.symm) (e v)
  convert this
  simp only [maxDegree, comap_degree_eq_degree]
  congr!
  change _ = Finset.univ.image ((G.degree ·) ∘ (e.symm ·) : Fin (Nat.card V) → ℕ)
  classical
  rw [← Finset.image_image]
  simp

noncomputable def greedyColoring'' {V} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Coloring G (Fin (G.maxDegree + 1)) :=
  Coloring.mk (fun v =>
      ⟨G.greedyColoring' v, by have := greedyColoring'_le_maxDegree G v; omega⟩) <| by
    simp only [ne_eq, Fin.mk.injEq]
    intros
    apply Coloring.valid
    assumption

end SimpleGraph
