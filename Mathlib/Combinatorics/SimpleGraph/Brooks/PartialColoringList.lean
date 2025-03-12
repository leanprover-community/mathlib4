import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Brooks.First
import Mathlib.Combinatorics.SimpleGraph.Brooks.DegreeOn

namespace SimpleGraph
section partialcol
variable {α : Type*} {G : SimpleGraph α}
open Finset
variable (G)
@[ext]
structure PartialColoringL (s : List α)  where
col : α → ℕ
valid : ∀ ⦃v w⦄, v ∈ s → w ∈ s → G.Adj v w → col v ≠ col w

instance (s : List α): FunLike (G.PartialColoringL s) α  ℕ where
  coe := PartialColoringL.col
  coe_injective' := fun _ _ h ↦ PartialColoringL.ext h

def ofNil : G.PartialColoringL [] where
  col := fun _ ↦ 0
  valid := fun _ _ h  _ ↦ False.elim <| not_mem_empty _ h

def ofNotAdj [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) : G.PartialColoringL [u, v] where
  col := fun _ ↦ 0
  valid := fun x y hx hy hadj heq ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    cases hx <;> cases hy <;> subst_vars
    · exact G.loopless _ hadj
    · exact h hadj
    · exact h hadj.symm
    · exact G.loopless _ hadj

namespace PartialColoringL
@[simp]
lemma ofNil_eq (v : α): G.ofNil v = 0 := rfl
variable {G}

@[simp]
lemma ofNotAdj_eq [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) (w : α): (G.ofNotAdj h) w = 0 := rfl

protected def copy {s t} (c : G.PartialColoringL s) (h : s = t) : G.PartialColoringL t where
  col := c.col
  valid := fun _ _ hv hw hadj => c.valid (h ▸ hv) (h ▸ hw) hadj

@[simp]
theorem copy_rfl {s} (c : G.PartialColoringL s)  : c.copy rfl = c := rfl

@[simp]
theorem copy_copy {s t u} (c : G.PartialColoringL s) (hs : s = t) (ht : t = u) :
    (c.copy hs).copy ht = c.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_eq {s t} (c : G.PartialColoringL s) (hs : s = t) (v : α) : (c.copy hs) v = c v := rfl


variable [Fintype α] [DecidableRel G.Adj]
open Finset
variable {s : Finset α} {b : ℕ} {i : α}

/-- A PartialColoringL of `univ` is a Coloring -/
def toColoring (C : G.PartialColoringL univ) : G.Coloring ℕ :=
    ⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩

variable [DecidableEq α]
lemma next (C : G.PartialColoringL s) (a : α)  :
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [card_range, degreeOn]
  apply Nat.lt_succ_of_le le_rfl

def extend (C : G.PartialColoringL s) (a : α) : ℕ := min' _ <| C.next a

lemma extend_def (C : G.PartialColoringL s) (a : α) : C.extend a =
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).min' (C.next a) := rfl

@[simp]
lemma copy_extend (C : G.PartialColoringL s) {t : Finset α} (a : α) (h : s = t) :
     (C.copy h).extend a = C.extend a := by
  rw [extend_def, extend_def]
  congr <;>
  exact h.symm

lemma extend_le_degreeOn (C : G.PartialColoringL s) (a : α) : C.extend a ≤ G.degreeOn s a := by
  have ⟨h1, _⟩ := mem_sdiff.1 <| min'_mem _ <| C.next a
  simpa [Nat.lt_succ] using h1

lemma extend_lt_degree (C : G.PartialColoringL s) {a v : α} (h1 : G.Adj a v) (h2 : v ∉ s) :
    C.extend a < G.degree a :=
  (extend_le_degreeOn _ _).trans_lt (degreeOn_lt_degree ⟨(mem_neighborFinset ..).2 h1, h2⟩)

lemma extend_not_mem_image (C : G.PartialColoringL s) (a : α) :
    C.extend a ∉ ((G.neighborFinset a) ∩ s).image C := by
  have ⟨_, h2⟩ := mem_sdiff.1 <| min'_mem _ <| C.next a
  exact h2

protected def insert (C : G.PartialColoringL s) (a : α) : G.PartialColoringL (insert a s) where
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


lemma ofInsert (C : G.PartialColoringL s) (a : α) (v : α) :
    (C.insert a) v = ite (v = a) (C.extend a) (C v) := rfl

def Greedy_extend (C : G.PartialColoringL s) (l : List α)  : G.PartialColoringL (s ∪ l.toFinset) :=
match l with
| [] => C.copy (by simp)
| a :: l => ((C.Greedy_extend l).insert a).copy (by simp)

@[simp]
lemma Greedy_extend_nil (C : G.PartialColoringL s)  : C.Greedy_extend []  = C.copy (by simp)  :=
  by rfl

lemma Greedy_extend_cons  (C : G.PartialColoringL s)  (l : List α) (a : α) (v : α) :
    (C.Greedy_extend (a :: l)) v = ite (v = a) ((C.Greedy_extend l).extend a)
      ((C.Greedy_extend l) v) := rfl

@[simp]
lemma Greedy_extend_head (C : G.PartialColoringL s) (l : List α) (a : α) :
    (C.Greedy_extend (a :: l)) a = extend (C.Greedy_extend l) a := by
  rw [Greedy_extend_cons, if_pos rfl]

lemma Greedy_extend_tail (C : G.PartialColoringL s) (l : List α) (a : α) {v : α} (hv : v ≠ a) :
    (C.Greedy_extend (a :: l)) v = (C.Greedy_extend l) v := by
  rw [Greedy_extend_cons, if_neg hv]

lemma Greedy_extend_not_mem {C : G.PartialColoringL s} {l : List α} {v : α} (hv : v ∉ l) :
    (C.Greedy_extend l) v = C v := by
  induction l with
  | nil => simp-- [Greedy_extend_nil]
  | cons head tail ih =>
    rw [Greedy_extend_cons]
    split_ifs with h
    · subst_vars; simp at hv
    · apply ih
      simp_all

lemma Greedy_extend_mem (C : G.PartialColoringL s) (l : List α) {v : α} (hv : v ∈ l) (hnd : l.Nodup):
    ∃ k m : List α, l = k ++ v :: m ∧ (C.Greedy_extend l) v = extend (C.Greedy_extend m) v := by
  obtain ⟨k, m, h⟩ := List.mem_iff_append.mp hv
  use k, m, h
  subst_vars
  induction k with
  | nil => simp
  | cons head tail ih =>
    have : v ≠ head := by rintro rfl; simp at hnd
    rw [List.cons_append, Greedy_extend_tail _ _ _ this]
    cases hv with
    | head as =>
      simp at hnd
    | tail b hv =>
      apply ih hv
      rw [List.cons_append,List.nodup_cons] at hnd
      exact hnd.2

open Walk
variable {k : ℕ} {u v w x : α}
#check List.Disjoint
/-
If `C` is a `k` coloring of `s`, all degrees are at most `k`, and  `p.cons h` is a path disjoint
from `s` then we have `k`-coloring of `s ∪ p.support` that extends `C`.
-/
theorem Greedy_extend_of_cons_path (C : G.PartialColoringL s) {h : G.Adj u v} {p : G.Walk v w}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : (p.cons h).IsPath) (hlt : ∀ y, C y < k)
    (hdisj : Disjoint s (p.cons h).support.toFinset) : (C.Greedy_extend p.support) x < k := by
  by_cases hx : x ∈ p.support
  · induction p generalizing s u  with
  | nil =>
    rw [mem_support_nil_iff, support_nil, Greedy_extend, copy_eq, ofInsert,if_pos hx] at *
    apply lt_of_lt_of_le (extend_lt_degree _ h.symm _) (hbdd _)
    rw [support_cons, support_nil, List.toFinset_cons,
      disjoint_insert_right] at hdisj
    simp [hdisj.1]
  | cons h p ih =>
    rename_i u' v' w' huv
    rw [support_cons,  Greedy_extend_cons] at *
    cases hx with
    | head as =>
      rw [if_pos rfl]
      apply lt_of_lt_of_le _ (hbdd x)
      apply extend_lt_degree (C.Greedy_extend p.support) h.symm
      intro hf
      rw [mem_union] at hf
      cases hf with
      | inl hf =>
        apply disjoint_left.1 hdisj hf
        simp
      | inr hf =>
        rw [cons_isPath_iff] at hp
        apply hp.2
        rw [support_cons]
        rw [List.mem_toFinset] at hf
        right; exact hf
    | tail b hb =>
      have : x ≠ u' := by
        rw [cons_isPath_iff,cons_isPath_iff] at hp
        intro hf
        subst x
        exact hp.1.2 hb
      rw [if_neg this]
      apply ih C hp.of_cons hlt _ hb
      apply disjoint_of_subset_right _ hdisj
      rw [support_cons]
      intro z hz; simp_all
  · rw [Greedy_extend_not_mem hx]
    exact hlt x


theorem Greedy_extend_of_concat_path (C : G.PartialColoringL s) {p : G.Walk u v} {h : G.Adj v w}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : (p.concat h).IsPath) (hlt : ∀ y, C y < k)
    (hdisj : Disjoint s (p.concat h).support.toFinset) :
    (C.Greedy_extend p.reverse.support) x < k := by
  rw [← reverse_reverse (p.concat h)] at *
  rw [reverse_concat, isPath_reverse_iff ] at *
  apply Greedy_extend_of_cons_path C hbdd hp hlt _
  rwa [support_reverse, List.toFinset_reverse] at hdisj

lemma insert_lt_of_lt {k : ℕ} {C : G.PartialColoringL s} {a : α} (h : ∀ v, v ∈ s → C v < k)
    (hg : C.extend a < k) {w : α} (hw : w ∈ insert a s) : (C.insert a).col w < k := by
  rw [PartialColoringL.insert]; dsimp
  by_cases ha : w = a
  · rwa [if_pos ha]
  · cases mem_insert.1 hw with
    |inl hw => contradiction
    |inr hw => rw [if_neg ha]; exact h w hw

lemma extend_eq_degreeOn {C : G.PartialColoringL s} {a : α} (h : C.extend a = G.degreeOn s a) :
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
lemma extend_lt_of_not_injOn {C : G.PartialColoringL s} {a : α} {u v : α} (hus : u ∈ s) (hvs : v ∈ s)
    (hu : G.Adj a u) (hv : G.Adj a v) (hne : u ≠ v) (hc : C u = C v) :
    C.extend a < G.degreeOn s a := by
    apply lt_of_le_of_ne (C.extend_le_degreeOn _)
    intro hf
    apply hne
    apply extend_eq_degreeOn hf <;> simp_all

/- If `a` has an uncolored neighbor then greedily coloring `a` uses a color less-than
  the degree of `a`-/
-- lemma extend_lt_of_not_colored {C : G.PartialColoringL s} {a : α} {u : α} (hu : G.Adj a u)
--     (h : u ∉ s) : C.extend a < G.degree a := lt_of_le_of_ne (C.extend_le_degree _)
--         fun hf ↦ h <| (next_eq_degree hf).2 <| (mem_neighborFinset ..).mpr hu

end PartialColoringL
end partialcol
end SimpleGraph
