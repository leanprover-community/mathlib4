import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Brooks.First
import Mathlib.Combinatorics.SimpleGraph.Brooks.DegreeOn

namespace SimpleGraph
section partialcol
variable {α : Type*} {G : SimpleGraph α}
open Finset
variable (G)
@[ext]
structure PartialColoring (s : Finset α)  where
col : α → ℕ
valid : ∀ ⦃v w⦄, v ∈ s → w ∈ s → G.Adj v w → col v ≠ col w

instance (s : Finset α): FunLike (G.PartialColoring s) α  ℕ where
  coe := PartialColoring.col
  coe_injective' := fun _ _ h ↦ PartialColoring.ext h

def ofEmpty : G.PartialColoring ∅ where
  col := fun _ ↦ 0
  valid := fun _ _ h  _ ↦ False.elim <| not_mem_empty _ h

def ofNotAdj [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) : G.PartialColoring {u, v} where
  col := fun _ ↦ 0
  valid := fun x y hx hy hadj heq ↦ by
    simp only [mem_insert, mem_singleton] at hx hy
    cases hx <;> cases hy <;> subst_vars
    · exact G.loopless _ hadj
    · exact h hadj
    · exact h hadj.symm
    · exact G.loopless _ hadj

namespace PartialColoring
@[simp]
lemma ofEmpty_eq (v : α): G.ofEmpty v = 0 := rfl
variable {G}

@[simp]
lemma ofNotAdj_eq [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) (w : α): (G.ofNotAdj h) w = 0 := rfl

protected def copy {s t} (c : G.PartialColoring s) (h : s = t) : G.PartialColoring t where
  col := c.col
  valid := fun _ _ hv hw hadj => c.valid (h ▸ hv) (h ▸ hw) hadj

@[simp]
theorem copy_rfl {s} (c : G.PartialColoring s)  : c.copy rfl = c := rfl

@[simp]
theorem copy_copy {s t u} (c : G.PartialColoring s) (hs : s = t) (ht : t = u) :
    (c.copy hs).copy ht = c.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_eq {s t} (c : G.PartialColoring s) (hs : s = t) (v : α) : (c.copy hs) v = c v := rfl
variable [DecidableEq α]
open Finset
variable {s : Finset α} {b : ℕ} {i : α}

/-- If `C` is a PartialColoring of `s` and `b` is not adjacent to anything
in `s` then we can color `b` with the color of `a` to give a PartialColoring of `insert b s`.
(Note: this is mainly useful when `a ∈ s` and `b ∉ s`.) -/
def insertNotAdj {b : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj v b) (a : α) :
    G.PartialColoring (insert b s) where
  col   := fun v ↦ ite (v = b) (C a) (C v)
  valid := by
    simp only [mem_insert, ne_eq]
    intro _ _ hv hw hadj hf
    cases hv with
    | inl hv =>
      rw [if_pos hv] at hf
      cases hw with
      | inl hw => exact (G.loopless _ (hv ▸ hw ▸ hadj)).elim
      | inr hw =>
        split_ifs at hf
        · subst_vars
          exact (G.loopless _ hadj).elim
        · exact h _ hw (hv ▸ hadj.symm)
    | inr hv =>
      cases hw with
      | inl hw => exact h _ hv (hw ▸ hadj)
      | inr hw =>
        split_ifs at hf with h1 h2 h3
        · exact (G.loopless _ (h1 ▸ h2 ▸ hadj)).elim
        · exact h _ hw (h1 ▸ hadj.symm)
        · exact h _ hv (h3 ▸ hadj)
        · exact C.valid hv hw hadj hf
@[simp]
lemma ofinsertNotAdj {a b v : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj v b) :
    (C.insertNotAdj h a) v = ite  (v = b) (C a) (C v) := rfl

lemma ofinsertNotAdj_new {a b : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj v b) :
   (C.insertNotAdj h a) b = C a := if_pos rfl

lemma ofinsertNotAdj_old {a b v : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj v b)
    (hv : v ≠ b) : (C.insertNotAdj h a) v = (C v) := if_neg hv

variable [Fintype α] [DecidableRel G.Adj]

/-- A PartialColoring of `univ` is a Coloring -/
def toColoring (C : G.PartialColoring univ) : G.Coloring ℕ :=
    ⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩

lemma next (C : G.PartialColoring s) (a : α)  :
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [card_range, degreeOn]
  apply Nat.lt_succ_of_le le_rfl

def extend (C : G.PartialColoring s) (a : α) : ℕ := min' _ <| C.next a

lemma extend_def (C : G.PartialColoring s) (a : α) : C.extend a =
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).min' (C.next a) := rfl

@[simp]
lemma copy_extend (C : G.PartialColoring s) {t : Finset α} (a : α) (h : s = t) :
     (C.copy h).extend a = C.extend a := by
  rw [extend_def, extend_def]
  congr <;>
  exact h.symm

lemma extend_le_degreeOn (C : G.PartialColoring s) (a : α) : C.extend a ≤ G.degreeOn s a := by
  have ⟨h1, _⟩ := mem_sdiff.1 <| min'_mem _ <| C.next a
  simpa [Nat.lt_succ] using h1

lemma extend_lt_degree (C : G.PartialColoring s) {a v : α} (h1 : G.Adj a v) (h2 : v ∉ s) :
    C.extend a < G.degree a :=
  (extend_le_degreeOn _ _).trans_lt (degreeOn_lt_degree ⟨(mem_neighborFinset ..).2 h1, h2⟩)

lemma extend_not_mem_image (C : G.PartialColoring s) (a : α) :
    C.extend a ∉ ((G.neighborFinset a) ∩ s).image C := by
  have ⟨_, h2⟩ := mem_sdiff.1 <| min'_mem _ <| C.next a
  exact h2


def insert_extend (C : G.PartialColoring s) (a : α) : G.PartialColoring (insert a s) where
  col   := fun v ↦ ite (v = a) (C.extend a) (C v)
  valid := by
    intro x y hx hy hadj
    dsimp
    split_ifs with hxi hyi hyi
    · subst_vars; intro hf; apply G.loopless _ hadj
    · intro hf; apply C.extend_not_mem_image a
      simp_rw [mem_image, mem_inter, mem_neighborFinset];
      use y
      exact ⟨⟨(hxi ▸ hadj), mem_of_mem_insert_of_ne hy hyi⟩,hf.symm⟩
    · intro hf; apply C.extend_not_mem_image a
      simp_rw [mem_image, mem_inter, mem_neighborFinset];
      use x
      exact ⟨⟨(hyi ▸ hadj.symm),mem_of_mem_insert_of_ne hx hxi⟩, hf⟩
    · exact C.valid (mem_of_mem_insert_of_ne hx hxi) (mem_of_mem_insert_of_ne hy hyi) hadj


lemma ofInsert (C : G.PartialColoring s) (a : α) (v : α) :
    (C.insert_extend a) v = ite (v = a) (C.extend a) (C v) := rfl

def Greedy (C : G.PartialColoring s) (l : List α)  : G.PartialColoring (s ∪ l.toFinset) :=
match l with
| [] => C.copy (by simp)
| a :: l => ((C.Greedy l).insert_extend a).copy (by simp)

@[simp]
lemma Greedy_nil (C : G.PartialColoring s)  : C.Greedy []  = C.copy (by simp)  :=
  by rfl

lemma Greedy_cons  (C : G.PartialColoring s)  (l : List α) (a : α) (v : α) :
    (C.Greedy (a :: l)) v = ite (v = a) ((C.Greedy l).extend a)
      ((C.Greedy l) v) := rfl

@[simp]
lemma Greedy_head (C : G.PartialColoring s) (l : List α) (a : α) :
    (C.Greedy (a :: l)) a = extend (C.Greedy l) a := by
  rw [Greedy_cons, if_pos rfl]

lemma Greedy_tail (C : G.PartialColoring s) (l : List α) (a : α) {v : α} (hv : v ≠ a) :
    (C.Greedy (a :: l)) v = (C.Greedy l) v := by
  rw [Greedy_cons, if_neg hv]

lemma Greedy_not_mem {C : G.PartialColoring s} {l : List α} {v : α} (hv : v ∉ l) :
    (C.Greedy l) v = C v := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [Greedy_cons]
    split_ifs with h
    · subst_vars; simp at hv
    · exact ih <| fun hf ↦ hv (List.mem_cons_of_mem _ hf)

open Walk
variable {k : ℕ} {u v w x : α}
#check List.Disjoint

/-
If `C` is a `k` coloring of `s`, all degrees are at most `k`, and  `p` is a path disjoint
from `s` then we have `k`-coloring of `s ∪ p.support.tail` that extends `C`.
-/
theorem Greedy_of_tail_path (C : G.PartialColoring s) {p : G.Walk u v}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hlt : ∀ y, C y < k)
    (hdisj : Disjoint s p.support.toFinset) (x : α) :
    (C.Greedy p.support.tail) x < k := by
  induction p with
  | nil => simpa using hlt x
  | @cons _ v _ h p ih =>
    rw [support_cons, List.tail_cons, support_eq_cons]
    by_cases hx : x = v
    · subst v
      rw [Greedy_head]
      apply (hbdd x).trans_lt' <| extend_lt_degree (C.Greedy p.support.tail) h.symm _
      intro hf
      rw [mem_union] at hf
      cases hf with
      | inl hf =>
        exact disjoint_left.1 hdisj hf <| List.mem_toFinset.2 (start_mem_support ..)
      | inr hf =>
        exact ((cons_isPath_iff ..).1 hp).2 <| List.mem_of_mem_tail (List.mem_toFinset.1 hf)
    · rw [Greedy_tail _ _ _ hx]
      apply ih hp.of_cons (disjoint_of_subset_right _ hdisj)
      rw [support_cons]
      exact fun y hy ↦ List.mem_toFinset.2 <| List.mem_cons_of_mem _ <| List.mem_toFinset.1 hy



theorem Greedy_of_concat_path (C : G.PartialColoring s) {p : G.Walk u v} {h : G.Adj v w}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : (p.concat h).IsPath) (hlt : ∀ y, C y < k)
    (hdisj : Disjoint s (p.concat h).support.toFinset) :
    (C.Greedy p.reverse.support) x < k := by
  rw [← reverse_reverse (p.concat h)] at *
  rw [reverse_concat, isPath_reverse_iff ] at *
  apply Greedy_of_tail_path C hbdd hp hlt _
  rwa [support_reverse, List.toFinset_reverse] at hdisj


lemma insert_lt_of_lt {k : ℕ} {C : G.PartialColoring s} {a : α} (h : ∀ v,  C v < k)
    (hg : C.extend a < k) (w : α) : (C.insert_extend a).col w < k := by
  rw [insert_extend]; dsimp
  by_cases ha : w = a
  · rwa [if_pos ha]
  · rw [if_neg ha]; exact h w

lemma extend_eq_degreeOn {C : G.PartialColoring s} {a : α} (h : C.extend a = G.degreeOn s a) :
     ((G.neighborFinset a ∩ s) : Set α).InjOn C := by
  let t := range (G.degreeOn s a + 1)
  let u := (G.neighborFinset a ∩ s).image C
  have hmax := max'_le _ (C.next a) _ <| fun y hy ↦ mem_range_succ_iff.1 <| (mem_sdiff.1 hy).1
  have hs : ∀ i, i ∈ t \ u → i = G.degreeOn s a :=
    fun i hi ↦ le_antisymm ((le_max' _ _ hi ).trans hmax)  (h ▸ min'_le _ _ hi)
  have h1 := card_eq_one.2 ⟨_, eq_singleton_iff_nonempty_unique_mem.2 ⟨C.next a, hs⟩⟩
  have : #t - #u ≤ 1 :=  (h1 ▸ le_card_sdiff _ _)
  rw [card_range] at this
  have h3 : G.degreeOn s a ≤ #u := by
    rwa [Nat.sub_le_iff_le_add, add_comm 1, Nat.succ_le_succ_iff] at this
  rw [← coe_inter]
  exact injOn_of_card_image_eq <| le_antisymm card_image_le h3
-- --       <| (card_le_card inter_subset_left).trans h3
--   have hs : G.neighborFinset a ⊆ s:= by
--     have h3 := h3.trans (card_image_le (s := G.neighborFinset a ∩ s) (f := C))
--     rw [← coe_inter] at hinj1
--     have h4 :=card_image_of_injOn hinj1
--     have h5 := (le_antisymm (by rwa [degree] at h3)  (card_le_card inter_subset_left)).le
--     contrapose! h5
--     exact card_lt_card ⟨inter_subset_left,fun h ↦ h5 fun x hx ↦ (mem_of_mem_inter_right (h hx))⟩
--   exact ⟨by rwa [← coe_inter, inter_eq_left.mpr hs] at hinj1, hs⟩

/-- If two neighbors of `a` have the same color in `s` then greedily coloring `a` uses a color
less-than the `degreeOn s` of `a` -/
lemma extend_lt_of_not_injOn {C : G.PartialColoring s} {a : α} {u v : α} (hus : u ∈ s) (hvs : v ∈ s)
    (hu : G.Adj a u) (hv : G.Adj a v) (hne : u ≠ v) (hc : C u = C v) :
    C.extend a < G.degreeOn s a := by
    apply lt_of_le_of_ne (C.extend_le_degreeOn _)
    intro hf
    apply hne
    apply extend_eq_degreeOn hf <;> simp_all

/- If `a` has an uncolored neighbor then greedily coloring `a` uses a color less-than
  the degree of `a`-/
-- lemma extend_lt_of_not_colored {C : G.PartialColoring s} {a : α} {u : α} (hu : G.Adj a u)
--     (h : u ∉ s) : C.extend a < G.degree a := lt_of_le_of_ne (C.extend_le_degree _)
--         fun hf ↦ h <| (next_eq_degree hf).2 <| (mem_neighborFinset ..).mpr hu
theorem Greedy_of_path_notInj {x y a : α} (C : G.PartialColoring s)
    {p : G.Walk u v} (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hlt : ∀ y, C y < k)
    (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x) (huy : G.Adj u y) (hne : x ≠ y)
    (heq : C x = C y) (hdisj : Disjoint s p.support.toFinset) :
    (C.Greedy p.support) a < k := by
  have hnx := fun hf ↦ disjoint_left.1 hdisj hxs <| List.mem_toFinset.2 <| List.mem_of_mem_tail hf
  have hny := fun hf ↦ disjoint_left.1 hdisj hys <| List.mem_toFinset.2 <| List.mem_of_mem_tail hf
  by_cases ha : a ∈ p.support
  · have := Greedy_of_tail_path C hbdd hp hlt hdisj
    rw [support_eq_cons]
    rw [Greedy_cons]
    by_cases hu : a = u
    · rw [if_pos hu]
      have heq : (C.Greedy p.support.tail) x = (C.Greedy p.support.tail) y := by
        rwa [Greedy_not_mem hnx, Greedy_not_mem hny]
      apply (extend_lt_of_not_injOn (mem_union_left _ hxs) (mem_union_left _ hys)
        hux huy hne heq).trans_le <| (degreeOn_le_degree ..).trans (hbdd _)
    ·  exact (if_neg hu) ▸ (this a)
  · rw [Greedy_not_mem ha]
    exact hlt a

/- If `a` has an uncolored neighbor then greedily coloring `a` uses a color less-than
  the degree of `a`-/
-- lemma extend_lt_of_not_colored {C : G.PartialColoring s} {a : α} {u : α} (hu : G.Adj a u)
--     (h : u ∉ s) : C.extend a < G.degree a := lt_of_le_of_ne (C.extend_le_degree _)
--         fun hf ↦ h <| (next_eq_degree hf).2 <| (mem_neighborFinset ..).mpr hu
theorem Greedy_of_path_concat_notInj {x y a : α} (C : G.PartialColoring s) {p : G.Walk u v}
{h : G.Adj v w}(hbdd : ∀ v, G.degree v ≤ k) (hp : (p.concat h).IsPath) (hlt : ∀ y, C y < k)
    (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj w x) (huy : G.Adj w y) (hne : x ≠ y)
    (heq : C x = C y) (hdisj : Disjoint s (p.concat h).support.toFinset) :
    (C.Greedy (p.concat h).reverse.support) a < k := by
  apply Greedy_of_path_notInj C hbdd hp.reverse hlt hxs hys hux huy hne heq
  rwa [support_reverse, List.toFinset_reverse]

theorem Greedy_of_path_concat_notAdj {x y a : α} {p : G.Walk u v} (hk : 0 < k)
{h : G.Adj v w} (hbdd : ∀ v, G.degree v ≤ k) (hp : (p.concat h).IsPath)
   (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj w x) (huy : G.Adj w y) (hne : x ≠ y)
    (heq : ¬ G.Adj x y) (hdisj : Disjoint s (p.concat h).support.toFinset) :
    ((G.ofNotAdj heq).Greedy (p.concat h).reverse.support) a < k := by
  apply Greedy_of_path_notInj (G.ofNotAdj heq) hbdd hp.reverse _ (by simp) (by simp)
    hux huy hne rfl
  · rw [support_reverse, List.toFinset_reverse]
    apply disjoint_of_subset_left _ hdisj
    intro _ hz
    rw [mem_insert, mem_singleton] at hz
    cases hz <;> subst_vars <;> assumption
  · intro y
    rwa [ofNotAdj_eq heq]

#check Walk.reverse_concat
end PartialColoring
end partialcol
end SimpleGraph
