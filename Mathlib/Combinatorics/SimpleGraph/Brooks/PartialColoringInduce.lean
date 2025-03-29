import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Brooks.DegreeOn
set_option linter.style.header false
namespace SimpleGraph
section partialcol
variable {α β: Type*} {G : SimpleGraph α} {s t : Set α}

open Set
abbrev PartialColoring (G : SimpleGraph α) (s : Set α) (β : Type*) :=
   (G.induce s).spanningCoe.Coloring β

lemma induce_spanningCoe_adj (G : SimpleGraph α) (s : Set α) {u v : α} :
    (G.induce s).spanningCoe.Adj u v ↔ G.Adj u v ∧ u ∈ s ∧ v ∈ s := by simp

variable {v w : α} {s : Set α} {C : G.PartialColoring s β}
theorem PartialColoring.valid  (hv : v ∈ s) (hw : w ∈ s) (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel (by simp [hv, hw, h])

def PartialColoring.mk (color : α → β)
    (valid : ∀ {v w : α}, v ∈ s → w ∈ s → G.Adj v w → color v ≠ color w) :
     G.PartialColoring s β :=
  ⟨color, by intro v w h h'; rw [induce_spanningCoe_adj] at h; exact valid h.2.1 h.2.2 h.1 h'⟩

/-- Whether a graph can be colored by at most `n` colors. -/
abbrev PartialColorable (s : Set α) (n : ℕ) : Prop := Nonempty (G.PartialColoring s (Fin n))

namespace PartialColoring

variable (n : ℕ) (G)
def ofEmpty : G.PartialColoring ∅ (Fin (n + 1)) :=
  PartialColoring.mk (fun _ ↦ 0) (fun h ↦ False.elim <| not_mem_empty _ h)

def ofNotAdj {u v : α} (h : ¬ G.Adj u v) : G.PartialColoring {u, v} (Fin (n + 1)) :=
  PartialColoring.mk (fun _ ↦ 0) (by
    intro x y hx hy hadj heq
    simp only [mem_insert_iff, mem_singleton_iff] at hx hy
    cases hx <;> cases hy <;> subst_vars
    · exact G.loopless _ hadj
    · exact h hadj
    · exact h hadj.symm
    · exact G.loopless _ hadj)

@[simp]
lemma ofEmpty_eq : ∀ v, ofEmpty G n v = 0 := fun _ ↦ rfl

variable {G}

@[simp]
lemma ofNotAdj_eq [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) : ∀ w, (ofNotAdj G n h) w = 0 :=
  fun _ ↦ rfl

protected def copy {s t} (c : G.PartialColoring s β) (h : s = t) : G.PartialColoring t β :=
  PartialColoring.mk (c) (fun hv hw hadj ↦  c.valid (h ▸ hv) (h ▸ hw) hadj)

@[simp]
theorem copy_rfl {s} (c : G.PartialColoring s β)  : c.copy rfl = c := rfl

@[simp]
theorem copy_copy {s t u} (c : G.PartialColoring s β) (hs : s = t) (ht : t = u) :
    (c.copy hs).copy ht = c.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_eq {s t} (c : G.PartialColoring s β) (hs : s = t) : ⇑(c.copy hs) = c  := rfl

variable [DecidableEq α] {b : ℕ} {i : α}

/-- If `C` is a PartialColoring of `s` and `b` is not adjacent to anything
in `s` then we can color `b` with the color of `a` to give a PartialColoring of `insert b s`.
(Note: this is mainly useful when `a ∈ s` and `b ∉ s`.) -/
def insertNotAdj {b : α} (C : G.PartialColoring s β) (h : ∀ v, v ∈ s → ¬ G.Adj b v) (a : α) :
    G.PartialColoring (insert b s) β :=
  PartialColoring.mk (fun v ↦ ite (v = b) (C a) (C v)) (by
    intro v w hv hw hadj hf
    dsimp at hf
    simp only [mem_insert_iff] at hv hw
    cases hv with
    | inl hv =>
      rw [if_pos hv] at hf
      cases hw with
      | inl hw => exact (G.loopless _ (hv ▸ hw ▸ hadj)).elim
      | inr hw =>
        split_ifs at hf
        · subst_vars
          exact (G.loopless _ hadj).elim
        · exact h _ hw (hv ▸ hadj)
    | inr hv =>
      cases hw with
      | inl hw => exact h _ hv (hw ▸ hadj.symm)
      | inr hw =>
        split_ifs at hf with h1 h2 h3
        · exact (G.loopless _ (h1 ▸ h2 ▸ hadj)).elim
        · exact h _ hw (h1 ▸ hadj)
        · exact h _ hv (h3 ▸ hadj.symm)
        · exact C.valid hv hw hadj hf)
@[simp]
lemma ofinsertNotAdj {a b v : α} (C : G.PartialColoring s β) (h : ∀ v, v ∈ s → ¬ G.Adj b v) :
    (C.insertNotAdj h a) v = ite (v = b) (C a) (C v) := rfl

@[simp]
lemma eq_ofinsertNotAdj  {a b : α} (C : G.PartialColoring s β) (h : ∀ v, v ∈ s → ¬ G.Adj b v) :
    (C.insertNotAdj h a) b = (C.insertNotAdj h a) a := by simp

-- lemma lt_of_insertNotAdj_lt {b : α} {k : ℕ} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v)
--     (a : α) (hlt : ∀  v, C v < k) (v : α) : (C.insertNotAdj h a) v < k := by
--   rw [ofinsertNotAdj]
--   split_ifs <;> exact hlt _

def join (C₁ : G.PartialColoring s β) (C₂ : G.PartialColoring t β) [DecidablePred (· ∈ s)]
    (h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w) : G.PartialColoring (s ∪ t) β :=
  PartialColoring.mk (fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)) (by
  simp only [mem_union, ne_eq]
  intro v w hv hw hadj hf
  cases hv with
  | inl hv =>
    cases hw with
    | inl hw => rw [if_pos hv, if_pos hw] at hf; exact C₁.valid hv hw hadj hf
    | inr hw => exact h _  hv _ hw hadj
  | inr hv =>
    cases hw with
    | inl hw => exact h _  hw _ hv hadj.symm
    | inr hw =>
      split_ifs at hf with h1 h2 h3
      · exact h _  h1 _ hw hadj
      · exact h _  h1 _ hw hadj
      · exact h _  h3 _ hv hadj.symm
      · exact C₂.valid hv hw hadj hf)

variable [DecidablePred (· ∈ s)]
lemma join_eq (C₁ : G.PartialColoring s β) (C₂ : G.PartialColoring t β)
    (h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w) :
    (C₁.join C₂ h) v = ite (v ∈ s) (C₁ v) (C₂ v) := rfl

-- lemma join_lt_of_lt {k : ℕ} {C₁ : G.PartialColoring s} {C₂ : G.PartialColoring t}
--     {h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w} (h1 : ∀  v, C₁ v < k) (h2 : ∀  v, C₂ v < k) :
--    ∀ v, (C₁.join C₂ h) v < k := by
--   intro v
--   rw [join_eq]
--   split_ifs
--   · exact h1 _
--   · exact h2 _


/-- A PartialColoring of `univ` is a Coloring -/
def toColoring (C : G.PartialColoring univ β) : G.Coloring β :=
    ⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩

variable [DecidableEq β]
lemma unused' (C : G.Coloring β) {a : α} [Fintype (G.neighborSet a)] (h : G.degree a < ENat.card β) :
     ∃ c, c ∉ (G.neighborFinset a).image C := by
  by_cases h' : Infinite β
  · exact Infinite.exists_not_mem_finset (Finset.image (⇑C) (G.neighborFinset a))
  · by_contra! hf
    have : Fintype β := fintypeOfNotInfinite h'
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_lt] at h
    classical
    rw [degree] at h
    have ⟨h1, h2⟩: Finset.image (fun v ↦ C v) (G.neighborFinset a) ⊂  (Finset.univ : Finset β) := by
      constructor
      · intro v hv ; exact Finset.mem_univ _
      · intro hf
        apply h.not_le
        rw [← Finset.card_univ]
        apply le_trans
        apply Finset.card_le_card hf
        exact Finset.card_image_le
    apply h2
    intro b hb
    exact hf b

--   -- rw [Fintype.card_eq_nat_card ]
--   -- rw [degree]
--   -- apply Nat.card_image_le
--   -- exact Finset.card_le_of_subset (image_subset_range _ _)
--  -- apply Finset.card_pos.1 --<| (Nat.sub_pos_of_lt _).trans_le -- <| le_card_sdiff _ _
--   apply Finset.card_image_le.trans_lt
--   rw [card_range, degreeOn]
--   apply Nat.lt_succ_of_le le_rfl

/-- Should say: given a PartialColoring s β and a vertex `a` whose degree is < β.card
there is an unused color. This should really be a result about Colorings  -/
lemma unused (C : G.PartialColoring s β) (a : α) :
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [card_range, degreeOn]
  apply Nat.lt_succ_of_le le_rfl

def extend (C : G.PartialColoring s) (a : α) : ℕ := min' _ <| C.unused a

lemma extend_def (C : G.PartialColoring s) (a : α) : C.extend a =
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).min' (C.unused a) := rfl

@[simp]
lemma copy_extend (C : G.PartialColoring s) {t : Finset α} (a : α) (h : s = t) :
     (C.copy h).extend a = C.extend a := by
  simp_rw [extend_def]
  congr <;> exact h.symm

lemma extend_le_degreeOn (C : G.PartialColoring s) (a : α) : C.extend a ≤ G.degreeOn s a := by
  have ⟨h1, _⟩ := mem_sdiff.1 <| min'_mem _ <| C.unused a
  simpa [Nat.lt_succ] using h1

lemma extend_lt_degree (C : G.PartialColoring s) {a v : α} (h1 : G.Adj a v) (h2 : v ∉ s) :
    C.extend a < G.degree a :=
  (extend_le_degreeOn _ _).trans_lt (degreeOn_lt_degree ⟨(mem_neighborFinset ..).2 h1, h2⟩)

lemma extend_not_mem_image (C : G.PartialColoring s) (a : α) :
    C.extend a ∉ ((G.neighborFinset a) ∩ s).image C := (mem_sdiff.1 <| min'_mem _ <| C.unused a).2

def insert' (C : G.PartialColoring s) (a : α) : G.PartialColoring (insert a s) where
  col   := fun v ↦ ite (v = a) (C.extend a) (C v)
  valid := by
    intro _ _ hx hy hadj
    dsimp
    split_ifs with hxi hyi hyi
    · subst_vars; intro hf; apply G.loopless _ hadj
    · intro hf; apply C.extend_not_mem_image a
      simp_rw [mem_image, mem_inter, mem_neighborFinset]
      exact ⟨_, ⟨(hxi ▸ hadj), mem_of_mem_insert_of_ne hy hyi⟩, hf.symm⟩
    · intro hf; apply C.extend_not_mem_image a
      simp_rw [mem_image, mem_inter, mem_neighborFinset]
      exact ⟨_, ⟨(hyi ▸ hadj.symm), mem_of_mem_insert_of_ne hx hxi⟩, hf⟩
    · exact C.valid (mem_of_mem_insert_of_ne hx hxi) (mem_of_mem_insert_of_ne hy hyi) hadj

variable {k : ℕ} {a u v w x y : α} {C : G.PartialColoring s}

lemma insert_lt_of_lt (h : ∀ v,  C v < k) (hg : C.extend a < k) : ∀ w, (C.insert' a).col w < k := by
  intro w
  rw [insert']; dsimp
  by_cases ha : w = a
  · rwa [if_pos ha]
  · rw [if_neg ha]; exact h w

lemma extend_eq_degreeOn (h : C.extend a = G.degreeOn s a) :
    ((G.neighborFinset a ∩ s) : Set α).InjOn C := by
  let t := range (G.degreeOn s a + 1)
  let u := (G.neighborFinset a ∩ s).image C
  have hmax := max'_le _ (C.unused a) _ <| fun y hy ↦ mem_range_succ_iff.1 <| (mem_sdiff.1 hy).1
  have hs : ∀ i, i ∈ t \ u → i = G.degreeOn s a :=
    fun i hi ↦ le_antisymm ((le_max' _ _ hi ).trans hmax)  (h ▸ min'_le _ _ hi)
  have h1 := card_eq_one.2 ⟨_, eq_singleton_iff_nonempty_unique_mem.2 ⟨C.unused a, hs⟩⟩
  have : #t - #u ≤ 1 :=  (h1 ▸ le_card_sdiff _ _)
  rw [card_range] at this
  have h3 : G.degreeOn s a ≤ #u := by
    rwa [Nat.sub_le_iff_le_add, add_comm 1, Nat.succ_le_succ_iff] at this
  rw [← coe_inter]
  exact injOn_of_card_image_eq <| le_antisymm card_image_le h3

/-- If two neighbors of `a` have the same color in `s` then greedily coloring `a` uses a color
less-than the `degreeOn s` of `a` -/
lemma extend_lt_of_not_injOn (hus : u ∈ s) (hvs : v ∈ s) (hu : G.Adj a u) (hv : G.Adj a v)
    (hne : u ≠ v) (hc : C u = C v) : C.extend a < G.degreeOn s a := by
    apply lt_of_le_of_ne (C.extend_le_degreeOn _)
    intro hf
    apply hne
    apply extend_eq_degreeOn hf <;> simp_all


def Greedy (C : G.PartialColoring s) (l : List α) : G.PartialColoring (s ∪ l.toFinset) :=
match l with
| [] => C.copy (by simp)
| a :: l => ((C.Greedy l).insert' a).copy (by simp)

@[simp]
lemma Greedy_nil (C : G.PartialColoring s)  : C.Greedy []  = C.copy (by simp)  := rfl

lemma Greedy_cons  (C : G.PartialColoring s)  (l : List α) (a : α) (v : α) :
    (C.Greedy (a :: l)) v = ite (v = a) ((C.Greedy l).extend a) ((C.Greedy l) v) := rfl

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
  | cons _ _ ih =>
    rw [Greedy_cons]
    split_ifs with h
    · subst_vars; simp at hv
    · exact ih <| fun hf ↦ hv (List.mem_cons_of_mem _ hf)

open Walk

/-
If `C` is a `k` coloring of `s`, all degrees are at most `k`, and  `p` is a path disjoint
from `s` then we have `k`-coloring of `s ∪ p.support.tail` by extending `C` greedily
-/
theorem Greedy_of_tail_path (C : G.PartialColoring s) {p : G.Walk u v} (hbdd : ∀ v, G.degree v ≤ k)
    (hp : p.IsPath) (hlt : ∀ y, C y < k) (hdisj : Disjoint s p.support.toFinset) (x : α) :
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
      cases mem_union.1 hf with
      | inl hf =>
        exact disjoint_left.1 hdisj hf <| List.mem_toFinset.2 (start_mem_support ..)
      | inr hf =>
        exact ((cons_isPath_iff ..).1 hp).2 <| List.mem_of_mem_tail (List.mem_toFinset.1 hf)
    · rw [Greedy_tail _ _ _ hx]
      apply ih hp.of_cons (disjoint_of_subset_right _ hdisj)
      rw [support_cons]
      exact fun _ hy ↦ List.mem_toFinset.2 <| List.mem_cons_of_mem _ <| List.mem_toFinset.1 hy

theorem Greedy_of_path_notInj (C : G.PartialColoring s) {p : G.Walk u v}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hlt : ∀ y, C y < k) (hxs : x ∈ s) (hys : y ∈ s)
    (hux : G.Adj u x) (huy : G.Adj u y) (hne : x ≠ y) (heq : C x = C y)
    (hdisj : Disjoint s p.support.toFinset) (a : α) : (C.Greedy p.support) a < k := by
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

theorem Greedy_of_path_concat_notInj {x y a : α} (C : G.PartialColoring s) {p : G.Walk u v}
{h : G.Adj v w}(hbdd : ∀ v, G.degree v ≤ k) (hp : (p.concat h).IsPath) (hlt : ∀ y, C y < k)
    (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj w x) (huy : G.Adj w y) (hne : x ≠ y)
    (heq : C x = C y) (hdisj : Disjoint s (p.concat h).support.toFinset) :
    (C.Greedy (p.concat h).reverse.support) a < k := by
  apply C.Greedy_of_path_notInj hbdd hp.reverse hlt hxs hys hux huy hne heq
  rwa [support_reverse, List.toFinset_reverse]

end PartialColoring
open Walk Finset PartialColoring

variable {G} {s : Finset α} {k : ℕ} [Fintype α] [DecidableRel G.Adj] [DecidableEq α]
/-- Essentially the first main case of Brooks theorem, applied with `s = {x₁, x₃}`
This gives a `k`-coloring of `s ∪ p.support.toFinset ∪ {x₂}` -/
theorem Brooks1 {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄} (hk : 0 < k)
    (hc : G.Adj xⱼ x₂) (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support)
    (hs1 : x₁ ∈ s) (hs3 : x₃ ∈ s) (h21 : G.Adj x₂ x₁) (h23 : G.Adj x₂ x₃)
    (hne : x₁ ≠ x₃) (heq : ¬ G.Adj x₁ x₃) (hdisj : Disjoint s p.support.toFinset)
    (h2disjp : x₂ ∉ p.support) (a : α) :
    ((G.ofNotAdj heq).Greedy (p.dropUntil _ hj).support.tail).Greedy
        ((p.takeUntil _ hj).concat hc).reverse.support a < k := by
  have hx1p : x₁ ∉ p.support := fun hf ↦ (disjoint_left.1 hdisj hs1 (List.mem_toFinset.2 hf))
  have hx3p : x₃ ∉ p.support := fun hf ↦ (disjoint_left.1 hdisj hs3 (List.mem_toFinset.2 hf))
  have htp := (concat_isPath_iff _ hc).2 ⟨hp.takeUntil hj,
      fun a ↦ h2disjp ((support_takeUntil_subset p hj) a)⟩
  let C₁ := (G.ofNotAdj heq).Greedy (p.dropUntil _ hj).support.tail
  have (x) : C₁ x < k := by
    have hd : ∀ y, y ∈ (p.dropUntil _ hj).support.toFinset → y ∈ p.support.toFinset := by
      intro y hy; rw [List.mem_toFinset] at *
      apply support_dropUntil_subset p hj hy
    have hd' : ∀ y : α, y ∈ ({x₁, x₃} : Finset α) → y ∈ s := by
      intro y hy; simp only [mem_insert, mem_singleton] at hy
      cases hy <;> subst_vars <;> assumption
    apply (G.ofNotAdj heq).Greedy_of_tail_path hbdd (hp.dropUntil hj)
      (fun y ↦ by rwa [ofNotAdj_eq heq])
    exact disjoint_of_subset_left hd' <| (disjoint_of_subset_right hd) hdisj
  let C₂ := C₁.Greedy ((p.takeUntil _ hj).concat hc).reverse.support
  have hc13 : C₁ x₁ = C₁ x₃ := by
    rw [Greedy_not_mem (fun hf ↦ hx3p <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)),
        Greedy_not_mem (fun hf ↦ hx1p <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf))]
    rfl
  apply C₁.Greedy_of_path_concat_notInj hbdd htp this _ _ h21 h23 hne hc13
  · simp_all only [ne_eq, concat_isPath_iff, insert_union, support_concat, List.concat_eq_append,
    List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
    disjoint_union_right, disjoint_insert_left, List.mem_toFinset, disjoint_union_left,
    disjoint_singleton_left, List.disjoint_toFinset_iff_disjoint, disjoint_singleton_right,
    mem_insert, mem_union, mem_singleton, not_or]
    exact ⟨⟨fun hf ↦ hx1p <| (support_takeUntil_subset _ hj) hf,  fun hf ↦ hx3p <|
    (support_takeUntil_subset _ hj) hf, (hp.support_takeUntil_disjoint_dropUntil_tail hj).symm⟩,
    ⟨h21.ne, h23.ne, fun hf ↦ h2disjp <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)⟩⟩
  · exact mem_union_left _ (by simp)
  · exact mem_union_left _ (by simp)

theorem Brooks1' {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} (p : G.Walk xᵣ x₄) (hk : 3 ≤ k) (hc : G.Adj xⱼ x₂)
    (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support) (h21 : G.Adj x₂ x₁)
    (h23 : G.Adj x₂ x₃) (hne : x₁ ≠ x₃) (heq : ¬ G.Adj x₁ x₃)
    (h1d : Disjoint {x₁, x₃} p.support.toFinset) (h2d : x₂ ∉ p.support) :
  ∃ (C : G.PartialColoring ({x₁, x₂, x₃} ∪ p.support.toFinset)), ∀ a, C a < k := by
  let C := ((G.ofNotAdj heq).Greedy (p.dropUntil _ hj).support.tail).Greedy
        ((p.takeUntil _ hj).concat hc).reverse.support
  have st : {x₁, x₃} ∪ (p.dropUntil xⱼ hj).support.tail.toFinset ∪
  ((p.takeUntil xⱼ hj).concat hc).reverse.support.toFinset = {x₁, x₂, x₃} ∪ p.support.toFinset := by
    rw [support_reverse, List.toFinset_reverse, support_concat]
    nth_rw 3 [← take_spec p hj]
    rw [support_append, union_assoc, union_comm (p.dropUntil _ hj).support.tail.toFinset,
        ← union_assoc, List.concat_eq_append, List.toFinset_append, union_comm
        (p.takeUntil _ hj).support.toFinset,  List.toFinset_append, ← union_assoc, ← union_assoc,
        List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, insert_union]
    congr
    ext; simp_rw [mem_union, mem_singleton, mem_insert, mem_singleton]
    rw [or_comm]
  use C.copy st
  rw [copy_eq]
  exact Brooks1 (Nat.zero_lt_of_lt hk) hc hbdd hp hj (by simp) (by simp) h21 h23 hne heq h1d h2d

end partialcol
end SimpleGraph
