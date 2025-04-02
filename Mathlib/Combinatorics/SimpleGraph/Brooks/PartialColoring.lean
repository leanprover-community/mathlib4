import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
set_option linter.style.header false

namespace SimpleGraph
variable {α : Type*} (G : SimpleGraph α)
open Finset

section degreeOn
open Finset

variable [DecidableEq α] [LocallyFinite G]

section withDecRel
variable [DecidableRel G.Adj]

/-- `G.degreeOn s a` is the number of neighbors of `a` in `s` -/
abbrev degreeOn (s : Finset α) (a : α) : ℕ := #(G.neighborFinset a ∩ s)

end withDecRel

variable {G}
lemma degreeOn.mono {s t : Finset α} {a : α} (h : s ⊆ t) : G.degreeOn s a ≤ G.degreeOn t a :=
    card_le_card fun _ hv ↦ mem_inter.2 ⟨(mem_inter.1 hv).1, h (mem_inter.1 hv).2⟩

lemma degreeOn_erase (s : Finset α) (a : α) : G.degreeOn (s.erase a) a = G.degreeOn s a := by
  apply le_antisymm (degreeOn.mono <| erase_subset ..)
  apply card_le_card
  intro v hv
  rw [mem_inter, mem_neighborFinset] at *
  use hv.1, mem_erase_of_ne_of_mem (fun hf ↦ G.loopless _ (hf ▸ hv.1)) hv.2

lemma degreeOn_le_degree (s : Finset α) (a : α) : G.degreeOn s a ≤ G.degree a := by
  rw [degreeOn, degree]
  apply card_le_card
  intro m hm
  simp only [mem_inter, mem_neighborFinset] at *
  exact hm.1

lemma degree_le_degreeOn_iff (s : Finset α) (a : α) :
    G.degree a ≤ G.degreeOn s a ↔ G.neighborFinset a ⊆ s := by
  constructor <;> rw [degree, degreeOn]
  · intro heq _ hx
    exact (mem_inter.1 ((eq_of_subset_of_card_le (inter_subset_left) heq).symm ▸ hx)).2
  · intro hs
    apply card_le_card fun _ hx ↦ mem_inter.2 ⟨hx, hs hx⟩

lemma degreeOn_lt_degree {a v : α} {s : Finset α} (hv : v ∈ G.neighborFinset a ∧ v ∉ s) :
    G.degreeOn s a < G.degree a :=
  lt_of_le_of_ne (degreeOn_le_degree s a) fun hf ↦
     hv.2 ((degree_le_degreeOn_iff ..).1 hf.symm.le hv.1)

end degreeOn

open Finset

@[ext]
structure PartialColoring (s : Finset α) where
col : α → ℕ
valid : ∀ ⦃v w⦄, v ∈ s → w ∈ s → G.Adj v w → col v ≠ col w

instance (s : Finset α) : FunLike (G.PartialColoring s) α  ℕ where
  coe := PartialColoring.col
  coe_injective' := fun _ _ h ↦ PartialColoring.ext h

/-- If no two vertices in `s` are adjacent then we can color `s` with zero -/
def partialColoringOfForAllNotAdj (s : Finset α) (h : ∀ ⦃u v⦄, u ∈ s → v ∈ s → ¬ G.Adj u v) :
    G.PartialColoring s where
  col := fun _ ↦ 0
  valid := fun _ _ hx hy hadj _ ↦ h hx hy hadj

def partialColoringOfEmpty : G.PartialColoring ∅ where
  col := fun _ ↦ 0
  valid := fun _ _ h  _ ↦ False.elim <| not_mem_empty _ h

def partialColoringOfNotAdj [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) :
    G.PartialColoring {u, v} where
  col := fun _ ↦ 0
  valid := fun x y hx hy hadj heq ↦ by
    simp only [mem_insert, mem_singleton] at hx hy
    cases hx <;> cases hy <;> subst_vars
    · exact G.loopless _ hadj
    · exact h hadj
    · exact h hadj.symm
    · exact G.loopless _ hadj

namespace PartialColoring

variable {G} in

abbrev IsPartialKColoring {s : Finset α} (C : G.PartialColoring s) (k : ℕ) := ∀ v, C v < k

@[simp]
lemma ofEmpty_eq : ∀ v, G.partialColoringOfEmpty v = 0 := fun _ ↦ rfl

variable {G}

@[simp]
lemma ofNotAdj_eq [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) :
    ∀ w, (G.partialColoringOfNotAdj h) w = 0 :=
  fun _ ↦ rfl

protected def copy {s t} (C : G.PartialColoring s) (h : s = t) : G.PartialColoring t where
  col := C.col
  valid := fun _ _ hv hw hadj => C.valid (h ▸ hv) (h ▸ hw) hadj

@[simp]
theorem copy_rfl {s} (C : G.PartialColoring s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartialColoring s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_eq {s t} (C : G.PartialColoring s) (hs : s = t) : ⇑(C.copy hs) = C  := rfl

@[simp]
lemma copy_isK {s t} {k : ℕ} {C : G.PartialColoring s} {hs : s = t} (h : C.IsPartialKColoring k) :
   (C.copy hs).IsPartialKColoring k := by
   intro v; rw [copy_eq]; exact h v

variable [DecidableEq α] {s t : Finset α} {b : ℕ} {i : α}

/-- If `C` is a PartialColoring of `s` and `b` is not adjacent to anything
in `s` then we can color `b` with the color of `a` to give a PartialColoring of `insert b s`.
(This is useful when `a ∈ s`, `b ∉ s` and we have `c ∉ s` that is adjacent to both
`a` and `b`, since both `a` and `b` receive the same color we will have more choice as to the color
of `c`.) -/
def insertNotAdj {b : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v) (a : α) :
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
        · exact h _ hw (hv ▸ hadj)
    | inr hv =>
      cases hw with
      | inl hw => exact h _ hv (hw ▸ hadj.symm)
      | inr hw =>
        split_ifs at hf with h1 h2 h3
        · exact (G.loopless _ (h1 ▸ h2 ▸ hadj)).elim
        · exact h _ hw (h1 ▸ hadj)
        · exact h _ hv (h3 ▸ hadj.symm)
        · exact C.valid hv hw hadj hf
@[simp]
lemma ofinsertNotAdj {a b v : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v) :
    (C.insertNotAdj h a) v = ite (v = b) (C a) (C v) := rfl

@[simp]
lemma eq_ofinsertNotAdj  {a b : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v) :
    (C.insertNotAdj h a) b = (C.insertNotAdj h a) a := by simp

lemma lt_of_insertNotAdj_lt {b : α} {k : ℕ} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v)
    (a : α) (h' : C.IsPartialKColoring k) : (C.insertNotAdj h a).IsPartialKColoring k := by
  intro v
  rw [ofinsertNotAdj]
  split_ifs <;> exact h' _

def join (C₁ : G.PartialColoring s) (C₂ : G.PartialColoring t)
    (h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w) : G.PartialColoring (s ∪ t) where
  col   := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  valid := by
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
        · exact C₂.valid hv hw hadj hf

lemma join_eq {v : α} (C₁ : G.PartialColoring s) (C₂ : G.PartialColoring t)
    (h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w) :
    (C₁.join C₂ h) v = ite (v ∈ s) (C₁ v) (C₂ v) := rfl

@[simp]
lemma join_isK_of_isK {k : ℕ} {C₁ : G.PartialColoring s} {C₂ : G.PartialColoring t}
    {h : ∀ v, v ∈ s → ∀ w, w ∈ t → ¬ G.Adj v w} (h1 : C₁.IsPartialKColoring k)
    (h2 : C₂.IsPartialKColoring k) : (C₁.join C₂ h).IsPartialKColoring k := by
  intro v
  rw [join_eq]
  split_ifs
  · exact h1 _
  · exact h2 _

variable [LocallyFinite G]

/-- A PartialColoring of `univ` is a Coloring -/
def toColoring [Fintype α] (C : G.PartialColoring univ) : G.Coloring ℕ :=
    ⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩

def toKColoring {k : ℕ} [Fintype α] {C : G.PartialColoring univ} (h : C.IsPartialKColoring k) :
  G.Coloring (Fin k) := ⟨fun v ↦ ⟨C v, h v⟩,
  fun hab heq ↦ C.valid (mem_univ _) (mem_univ _) hab (by simpa using heq)⟩

lemma unused (C : G.PartialColoring s) (a : α) :
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [card_range, degreeOn]
  apply Nat.lt_succ_of_le le_rfl

/-- The color used by the greedy algorithm to extend `C` from `s` to `insert a s` -/
def extend (C : G.PartialColoring s) (a : α) : ℕ := min' _ <| C.unused a

lemma extend_le_degreeOn (C : G.PartialColoring s) (a : α) : C.extend a ≤ G.degreeOn s a := by
  have ⟨h1, _⟩ := mem_sdiff.1 <| min'_mem _ <| C.unused a
  simpa [Nat.lt_succ] using h1

lemma extend_lt_degree (C : G.PartialColoring s) {a v : α} (h1 : G.Adj a v) (h2 : v ∉ s) :
    C.extend a < G.degree a :=
  (extend_le_degreeOn _ _).trans_lt (degreeOn_lt_degree ⟨(mem_neighborFinset ..).2 h1, h2⟩)

lemma extend_not_mem_image (C : G.PartialColoring s) (a : α) :
    C.extend a ∉ ((G.neighborFinset a) ∩ s).image C := (mem_sdiff.1 <| min'_mem _ <| C.unused a).2

/-- The greedy coloring of `insert a s` given a coloring of `s` -/
protected def insert (C : G.PartialColoring s) (a : α) : G.PartialColoring (insert a s) where
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

lemma insert_eq (C : G.PartialColoring s) (a : α) :
    C.insert a = fun v ↦ ite (v = a) (C.extend a) (C v) := rfl

variable {k : ℕ} {a u v w x y : α} {C : G.PartialColoring s}

/-- If `C` is a `k`-coloring of `s` and the greedy extend uses a color < k then -/
lemma insert_of_lt (h : C.IsPartialKColoring k) (hg : C.extend a < k) :
    (C.insert a).IsPartialKColoring k := by
  rw [IsPartialKColoring, insert_eq]
  intro w; dsimp
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
  have : #t - #u ≤ 1 :=  (h1 ▸ le_card_sdiff ..)
  rw [card_range] at this
  have h3 : G.degreeOn s a ≤ #u := by
    rwa [Nat.sub_le_iff_le_add, add_comm 1, Nat.succ_le_succ_iff] at this
  rw [← coe_inter]
  exact injOn_of_card_image_eq <| le_antisymm card_image_le h3

/-- If two neighbors of `a` have the same color in `s` then greedily coloring `a` uses a color
less-than the `degreeOn s` of `a` -/
lemma extend_lt_of_not_injOn (hus : u ∈ s) (hvs : v ∈ s) (hu : G.Adj a u) (hv : G.Adj a v)
    (hne : u ≠ v) (hj2 : C u = C v) : C.extend a < G.degreeOn s a := by
    apply (C.extend_le_degreeOn _).lt_of_ne
    intro hf
    apply hne
    apply extend_eq_degreeOn hf <;> simp_all


open Walk List
/-- The greedy extension of a `PartialColoring s` to a list of vertices `l`. -/
def Greedy (C : G.PartialColoring s) (l : List α) : G.PartialColoring (s ∪ l.toFinset) :=
match l with
| [] => C.copy (by simp)
| a :: l => ((C.Greedy l).insert a).copy (by simp)

@[simp]
lemma Greedy_nil (C : G.PartialColoring s)  : C.Greedy []  = C.copy (by simp)  := rfl

lemma Greedy_cons (C : G.PartialColoring s) (l : List α) (a : α) (v : α) :
    (C.Greedy (a :: l)) v = ite (v = a) ((C.Greedy l).extend a) ((C.Greedy l) v) := rfl

@[simp]
lemma Greedy_head (C : G.PartialColoring s) (l : List α) (a : α) :
    (C.Greedy (a :: l)) a = (C.Greedy l).extend a := by
  rw [Greedy_cons, if_pos rfl]

@[simp]
lemma Greedy_tail (C : G.PartialColoring s) (l : List α) (a : α) {v : α} (hv : v ≠ a) :
    (C.Greedy (a :: l)) v = (C.Greedy l) v := by
  rw [Greedy_cons, if_neg hv]

@[simp]
lemma Greedy_not_mem {C : G.PartialColoring s} {l : List α} {v : α} (hv : v ∉ l) :
    (C.Greedy l) v = C v := by
  induction l with
  | nil => simp
  | cons _ _ ih =>
    rw [Greedy_cons]
    split_ifs with h
    · subst_vars; simp at hv
    · exact ih <| fun hf ↦ hv (mem_cons_of_mem _ hf)

variable {x y a : α} {C : G.PartialColoring s} {p : G.Walk u v}
/-
If `C` is a `k` coloring of `s`, all degrees are at most `k`, and  `p` is a path disjoint
from `s` then we have `k`-coloring of `s ∪ p.support.tail` by extending `C` greedily
-/
theorem Greedy_of_tail_path (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath)
    (hlt : C.IsPartialKColoring k) (hdisj : Disjoint s p.support.toFinset) :
    (C.Greedy p.support.tail).IsPartialKColoring k := by
  induction p with
  | nil => simpa using hlt
  | @cons _ v _ h p ih =>
    intro x
    rw [support_cons, List.tail_cons, support_eq_cons]
    by_cases hx : x = v
    · subst v
      rw [Greedy_head]
      apply (hbdd x).trans_lt' <| extend_lt_degree (C.Greedy p.support.tail) h.symm _
      intro hf
      obtain (hf | hf) := mem_union.1 hf
      · exact disjoint_left.1 hdisj hf <| mem_toFinset.2 <| start_mem_support ..
      · exact ((cons_isPath_iff ..).1 hp).2 <| mem_of_mem_tail <| mem_toFinset.1 hf
    · rw [Greedy_tail _ _ _ hx]
      apply ih hp.of_cons (disjoint_of_subset_right _ hdisj)
      rw [support_cons]
      exact fun _ hy ↦ mem_toFinset.2 <| mem_cons_of_mem _ <| mem_toFinset.1 hy

theorem Greedy_of_path_notInj (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath)
    (hlt : C.IsPartialKColoring k) (hxs : x ∈ s) (hys : y ∈ s)
    (hux : G.Adj u x) (huy : G.Adj u y) (hne : x ≠ y) (heq : C x = C y)
    (hdisj : Disjoint s p.support.toFinset) : (C.Greedy p.support).IsPartialKColoring k := by
  have hnx := fun hf ↦ disjoint_left.1 hdisj hxs <| mem_toFinset.2 <| mem_of_mem_tail hf
  have hny := fun hf ↦ disjoint_left.1 hdisj hys <| mem_toFinset.2 <| mem_of_mem_tail hf
  intro a
  by_cases ha : a ∈ p.support
  · have := Greedy_of_tail_path hbdd hp hlt hdisj
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

theorem Greedy_of_path_concat_notInj {h : G.Adj v w} (hbdd : ∀ v, G.degree v ≤ k)
    (hp : (p.concat h).IsPath) (hlt : C.IsPartialKColoring k)
    (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj w x) (huy : G.Adj w y) (hne : x ≠ y)
    (heq : C x = C y) (hdisj : Disjoint s (p.concat h).support.toFinset) :
    (C.Greedy (p.concat h).reverse.support).IsPartialKColoring k := by
  apply C.Greedy_of_path_notInj hbdd hp.reverse hlt hxs hys hux huy hne heq
  rwa [support_reverse, toFinset_reverse]

end PartialColoring
open Walk Finset PartialColoring

variable [DecidableEq α] {G} {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄}
/-- Get the vertex set of the coloring we use in the 1st part of Brooks theorem into the appropriate
form -/
theorem Brooks1_copy_eq (hj : xⱼ ∈ p.support) (hj2 : G.Adj xⱼ x₂) :
    {x₁, x₃} ∪ (p.dropUntil _ hj).support.tail.toFinset ∪
    ((p.takeUntil _ hj).concat hj2).reverse.support.toFinset =
    p.support.toFinset ∪ {x₃, x₂, x₁} := by
    rw [union_comm p.support.toFinset, pair_comm, support_reverse, List.toFinset_reverse,
        support_concat]
    nth_rw 3 [← take_spec p hj]
    rw [support_append,union_right_comm , List.concat_eq_append, List.toFinset_append,
        union_comm _ ([x₂].toFinset), List.toFinset_append, ← union_assoc, ← union_assoc,
        List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, insert_union]
    congr
    ext; rw [pair_comm, mem_union, mem_singleton, mem_insert]

variable {k : ℕ} [Fintype α] [DecidableRel G.Adj]

theorem Brooks1_exists {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄} (hk : 3 ≤ k)
    (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support) (hj2 : G.Adj xⱼ x₂)
    (h21 : G.Adj x₂ x₁) (h23 : G.Adj x₂ x₃) (hne : x₁ ≠ x₃) (h13 : ¬ G.Adj x₁ x₃)
    (h1 : x₁ ∉ p.support) (h2 : x₂ ∉ p.support) (h3 : x₃ ∉ p.support) :
  ∃ (C : G.PartialColoring (p.support.toFinset ∪ {x₃, x₂, x₁} )), C.IsPartialKColoring k := by
  use (((G.partialColoringOfNotAdj h13).Greedy (p.dropUntil _ hj).support.tail).Greedy
        ((p.takeUntil _ hj).concat hj2).reverse.support).copy (Brooks1_copy_eq hj hj2)
  have htp := (concat_isPath_iff _ hj2).2 ⟨hp.takeUntil hj,
      fun a ↦ h2 ((support_takeUntil_subset p hj) a)⟩
  let C₁ := (G.partialColoringOfNotAdj h13).Greedy (p.dropUntil _ hj).support.tail
  have : C₁.IsPartialKColoring k := by
    have hd : ∀ y, y ∈ (p.dropUntil _ hj).support.toFinset → y ∈ p.support.toFinset := by
      intro y hy; rw [List.mem_toFinset] at *
      apply support_dropUntil_subset p hj hy
    apply (G.partialColoringOfNotAdj h13).Greedy_of_tail_path hbdd (hp.dropUntil hj)
      (fun y ↦ by rw [ofNotAdj_eq h13]; exact Nat.zero_lt_of_lt hk)
    simp_rw [disjoint_insert_left, disjoint_singleton_left, List.mem_toFinset]
    exact ⟨fun hf ↦ h1 <| (support_dropUntil_subset _ _) hf,
      fun hf ↦ h3 <| (support_dropUntil_subset _ _) hf⟩
  let C₂ := C₁.Greedy ((p.takeUntil _ hj).concat hj2).reverse.support
  have hj213 : C₁ x₁ = C₁ x₃ := by
    rw [Greedy_not_mem (fun hf ↦ h3 <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf)),
        Greedy_not_mem (fun hf ↦ h1 <| (support_dropUntil_subset _ hj) (List.mem_of_mem_tail hf))]
    rfl
  apply C₁.Greedy_of_path_concat_notInj hbdd htp this (mem_union_left _ (mem_insert_self ..))
    (mem_union_left _ (mem_insert_of_mem <| mem_singleton.mpr rfl)) h21 h23 hne hj213
  simpa using ⟨⟨fun h ↦ h1 <| (support_takeUntil_subset _ hj) h, fun h ↦ h3 <|
    (support_takeUntil_subset ..) h, (hp.support_takeUntil_disjoint_dropUntil_tail hj).symm⟩,
    ⟨h21.ne, h23.ne, fun h ↦ h2 <| (support_dropUntil_subset ..) (List.mem_of_mem_tail h)⟩⟩

end SimpleGraph
