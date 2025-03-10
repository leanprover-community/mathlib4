import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Brooks.First
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
open Finset
section Walks
namespace Walk
-- #check List.takeWhile
-- variable [LocallyFinite G] [DecidableEq α]
-- lemma exists_max_cycle_of_max_path {u v : α} {p : G.Walk u v} (hp : p.IsPath)
--   (hmax : G.neighborFinset u ⊆ p.support.toFinset) (h1 : 1 < G.degree u) :
--     ∃ x, ∃ (had : G.Adj x u), ∃ (hx : x ∈ p.support), ((p.takeUntil x hx).cons had).IsCycle
--     ∧ G.neighborFinset u ⊆ ((p.takeUntil x hx).cons had).support.toFinset := by
--   sorry
variable [DecidableEq α] [LocallyFinite G]
lemma exists_maximal_path_subset {u v : α} (s : Finset α) {q : G.Walk u v} (hq : q.IsPath)
    (hs : q.support.toFinset ⊆ s): ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧
  (p.append q).support.toFinset ⊆ s ∧ G.neighborFinset x ∩ s ⊆ (p.append q).support.toFinset := by
  by_contra! hf
  have : ∀ n, ∃ x, ∃ p : G.Walk x u, (p.append q).IsPath ∧ (p.append q).support.toFinset ⊆ s ∧
    n ≤ (p.append q).length := by
    intro n
    induction n with
    | zero =>
      use u, Walk.nil; simpa using ⟨hq, hs⟩
    | succ n ih =>
      obtain ⟨x, p, hp, hs, hc⟩ := ih
      obtain ⟨y, hy⟩ := not_subset.mp <| hf x p hp hs
      rw [mem_inter, mem_neighborFinset] at hy
      use y, p.cons hy.1.1.symm
      simp_all only [length_append, cons_append, cons_isPath_iff, mem_support_append_iff, not_or,
      true_and,  support_cons, List.toFinset_cons, length_cons, Nat.add_le_add_iff_right, and_true]
      simp_all only [List.mem_toFinset, mem_support_append_iff, not_or, not_false_eq_true, and_self,
         true_and]
      intro z hz;
      cases mem_insert.1 hz with
      | inl hz => exact hz ▸ hy.1.2
      | inr hz => exact hs hz
  obtain ⟨w, _, hp, hc⟩ := this #s
  have := (List.toFinset_card_of_nodup hp.2) ▸ (card_le_card hc.1)
  rw [length_support] at this
  exact Nat.lt_irrefl _ <| hc.2.trans_lt this

end Walk
end Walks

section degreeOn

variable  [DecidableRel G.Adj] [Fintype α]
open Finset
/-

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

-/


variable [DecidableEq α]
variable (G) in
abbrev degreeOn (s : Finset α) (a : α) : ℕ := #(G.neighborFinset a ∩ s)

lemma degreeOn.mono {s t : Finset α} {a : α} (h : s ⊆ t) : G.degreeOn s a ≤ G.degreeOn t a :=
    card_le_card fun _ hv ↦ mem_inter.2 ⟨(mem_inter.1 hv).1, h (mem_inter.1 hv).2⟩

lemma degreeOn_erase (s : Finset α) (a : α) : G.degreeOn (s.erase a) a = G.degreeOn s a := by
  apply le_antisymm (degreeOn.mono <| erase_subset _ _)
  apply card_le_card
  intro v hv
  rw [mem_inter, mem_neighborFinset] at *
  use hv.1, mem_erase_of_ne_of_mem (fun hf ↦ G.loopless _ (hf ▸ hv.1)) hv.2

lemma degreeOn_le_degree (s : Finset α) (a : α) :
    G.degreeOn s a ≤ G.degree a := by
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
/-!
## Brooks' Theorem (a version of)
If `G : SimpleGraph α` and `Δ ≥ 3` is a natural number such that `G` is `Δ + 1`-clique free and
`∀ v, G.degree v ≤ Δ` then for any `s : Finset α` there exists a partial coloring of `s` that uses
at most `Δ` colors.

[Note below: `G.Greedy l` colors `[]` by `c v = 0` for all `v : α` and given `C := G.Greedy l` it
colors `(a :: l)` by `c v := ite (v = a) (greedy C a) (C v)` where `greedy C a` is the smallest
color not used by the neighbors of `a` in `C`. In particular it assigns `0` to any vertex not in `l`
and then uses the smallest color possible at each step.]

Proof: By strong induction on `#s`:

`ih : ∀ s, #s < n → ∃ C, G.PartialColoring s, ∀ v, C v < Δ`.

Now suppose we have `#s = n`.

If `∃ v ∈ s` such that `s ∩ Γ(v) < Δ` then apply `ih s.erase v` to obtain
`C : G.PartialColoring s.erase v`then use `C.insert a`
(the coloring of `s` given by greedyily extending `C`) to complete the proof.

So wlog every vertex in `s` has exactly `Δ` neighbors in `s` (and hence no neighbors outside `s`).

Since `G` has no `Δ + 1`-clique so `s` contains no `Δ + 1`-clique.
Thus if `v₃ ∈ s` then `v₂` has neighbors `v₁` and `v₃` such that `v₁` and `v₃` are not neighbors.
Let `v₁v₂v₃⋯vᵣ₊₁` be a maximal path in `G`, so `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}.

We consider two cases:

1. We have `{v₁,…,vᵣ₊₁} = s`.
   Let `vⱼ ∈ Γ(v₂) \ {v₁,v₃}`. So `j ≥ 4`
   So `r + 1 = n`. Let `l = [v₁,v₃,v₄,…,vⱼ₋₁,vₙ,vₙ₋₁,…,vⱼ,v₂]` and check that `Greedy l` works.
   This is true since `c v₁ = c v₃ = 0` (they are not adjacent). Then `c vᵢ < Δ` for each
   `4 ≤ i ≤ j - 1` since when we color `vᵢ` its neighbor `vᵢ₊₁` is uncolored. The same is true for
   `n ≥ i ≥ j + 1` since `vᵢ` has a neighbor `vᵢ₋₁` that is uncolored.
   Finally `vⱼ` has uncolored neighbor `v₂` and finally `v₂` has two neigbors of the same color,
   namely `v₁` and `v₃`.

2. We have `{v₁,…,vᵣ₊₁} ≠ s`.
   In this case  let `j = min {i | vᵢ ∈ Γ(vᵣ₊₁)}`, so `j ≤ r - 1`.
   Let `t = s \ {vⱼ,…,vᵣ₊₁}` and `l` be the list given by `ih t`. Then `l` is a listing of `t` such
   that `G.Greedy l'` uses at most `Δ` colors.
   If there is no edge between `t` and `u := {vⱼ,…,vᵣ₊₁}` then we can apply `ih u` to get a listing
   `k` of `u` such that `G.Greedy k` uses at most `Δ` colors and `l ++ k` is the desired listing of
   `s`. Otherwise let `m := max {i | j ≤ i ≤ r + 1, Γ(vᵢ) ∩ t ≠ ∅}` and let `w ∈ Γ(vₘ) ∩ t`.
   Note that `m < r + 1` since `Γ(vᵣ₊₁) ⊆ {v₁,…,vᵣ}`. Note `vₘ₊₁` has no neighbor in `t` so we can
   set `c vₘ₊₁ = c w` [Problem : this is not greedy anymore!].
   Now let `k = [vₘ₊₂,…,vᵣ,vⱼ,…,vₘ₋₁,vₘ]`. Note that the only possible problem for coloring
   `k` greedily is at `vₘ`, but this is fine since `vₘ` has 2 neighbors of the same color, namely
   `w` and `vₘ₊₁`.
--------------------------------------------/

section partialcol
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

@[simp]
lemma ofNotAdj_eq [DecidableEq α] {u v : α} (h : ¬ G.Adj u v) (w : α): (G.ofNotAdj h) w = 0 := rfl

variable {G}
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

variable [Fintype α] [DecidableRel G.Adj]
open Finset
variable {β : Type*} {s : Finset α} {b : ℕ} {i : α}

/-- A PartialColoring of `univ` is a Coloring  -/
def toColoring (C : G.PartialColoring univ) : G.Coloring ℕ :=
    ⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩

variable [DecidableEq α]
lemma next (C : G.PartialColoring s) (a : α)  :
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [card_range, degreeOn]
  apply Nat.lt_succ_of_le le_rfl

def extend (C : G.PartialColoring s) (a : α) : ℕ := min' _ <| C.next a

lemma extend_def (C : G.PartialColoring s) (a : α) : C.extend a =
    (range (G.degreeOn s a + 1) \ (((G.neighborFinset a) ∩ s).image C)).min' (C.next a) := rfl

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

protected def insert (C : G.PartialColoring s) (a : α) : G.PartialColoring (insert a s) where
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
    (C.insert a) v = ite (v = a) (C.extend a) (C v) := rfl

def Greedy_extend (C : G.PartialColoring s) (l : List α)  : G.PartialColoring (s ∪ l.toFinset) :=
match l with
| [] => C.copy (by simp)
| a :: l => ((C.Greedy_extend l).insert a).copy (by simp)

@[simp]
lemma Greedy_extend_nil (C : G.PartialColoring s) (v : α) : (C.Greedy_extend []) v = C v := by rfl

lemma Greedy_extend_cons  (C : G.PartialColoring s)  (l : List α) (a : α) (v : α) :
    (C.Greedy_extend (a :: l)) v = ite (v = a) ((C.Greedy_extend l).extend a)
      ((C.Greedy_extend l) v) := rfl

@[simp]
lemma Greedy_extend_head (C : G.PartialColoring s) (l : List α) (a : α) :
    (C.Greedy_extend (a :: l)) a = extend (C.Greedy_extend l) a := by
  rw [Greedy_extend_cons, if_pos rfl]

lemma Greedy_extend_tail (C : G.PartialColoring s) (l : List α) (a : α) {v : α} (hv : v ≠ a) :
    (C.Greedy_extend (a :: l)) v = (C.Greedy_extend l) v := by
  rw [Greedy_extend_cons, if_neg hv]

lemma Greedy_extend_not_mem {C : G.PartialColoring s} {l : List α} {v : α} (hv : v ∉ l) :
    (C.Greedy_extend l) v = C v := by
  induction l with
  | nil => rw [Greedy_extend_nil]
  | cons head tail ih =>
    rw [Greedy_extend_cons]
    split_ifs with h
    · subst_vars; simp at hv
    · apply ih
      simp_all

lemma Greedy_extend_mem (C : G.PartialColoring s) (l : List α) {v : α} (hv : v ∈ l) (hnd : l.Nodup):
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

/--
If `C` is a `k` coloring of `s`, all degrees are at most `k`, and  `p.cons h` is a path disjoint
from `s` then we have `k`-coloring of `s ∪ p.support` that extends `C`.
-/
theorem Greedy_extend_of_path {C : G.PartialColoring s} (h : G.Adj u v) {p : G.Walk v w}
    (hbdd : ∀ v, G.degree v ≤ k) (hp : (p.cons h).IsPath) (hlt : ∀ x, C x < k)
    (hdisj : Disjoint s (p.cons h).support.toFinset) : (C.Greedy_extend p.support) x < k := by
  by_cases hx : x ∈ p.support
  · induction p generalizing s u  with
  | nil =>
    rename_i y
    simp only [support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [support_nil, Greedy_extend_cons, if_pos hx]
    subst_vars
    apply lt_of_lt_of_le _ (hbdd y)
    apply extend_lt_degree _ h.symm
    simp only [support_cons, support_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
      disjoint_insert_right, disjoint_singleton_right] at hdisj
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
      apply ih huv _ hlt _ hb
      · exact hp.of_cons
      · apply disjoint_of_subset_right _ hdisj
        rw [support_cons]
        intro z hz; simp_all
  · rw [Greedy_extend_not_mem hx]
    exact hlt x

-- def ofWalk (C : G.PartialColoring s) {u v w : α} (p : G.Walk u v) (h : G.Adj v w)
--     : G.PartialColoring (s ∪ p.support.toFinset) :=
--   match p with
--    | nil  => by
--       convert C.insert u using 1;
--       simp only [support_nil, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq]
--       rw [union_comm]
--       rfl
--    | Walk.cons h' p => by
--       convert (C.ofWalk p h).insert u using 1
--       simp

lemma insert_lt_of_lt {k : ℕ} {C : G.PartialColoring s} {a : α} (h : ∀ v, v ∈ s → C v < k)
    (hg : C.extend a < k) {w : α} (hw : w ∈ insert a s) : (C.insert a).col w < k := by
  rw [PartialColoring.insert]; dsimp
  by_cases ha : w = a
  · rwa [if_pos ha]
  · cases mem_insert.1 hw with
    |inl hw => contradiction
    |inr hw => rw [if_neg ha]; exact h w hw

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
less-than the `degreeOn s` of `a`-/
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
#check Walk.mem_support_append_iff


#check List.card_toFinset
variable {k : ℕ}
theorem BrooksPartial (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k)
    (s : Finset α) : ∃ C : G.PartialColoring s, ∀ v, v ∈ s → C v < k := by
  have H  (n : ℕ) (hn : #s ≤ n) : ∃ C : G.PartialColoring s, ∀ v, v ∈ s → C v < k := by
    induction n using Nat.strong_induction_on generalizing s with
    | h n ih =>
    by_cases hd : ∃ v ∈ s, G.degreeOn (s.erase v) v < k
    · obtain ⟨v, hv, hlt⟩ := hd
      obtain ⟨C, hC⟩:= ih _ (Nat.lt_of_lt_of_le (card_erase_lt_of_mem hv) hn) _ le_rfl
      have hvlt : C.extend v < k := (C.extend_le_degreeOn _).trans_lt hlt
      have (w : α) (hw : w ∈ insert v (s.erase v)) := insert_lt_of_lt hC hvlt hw
      use (C.insert v).copy (by simp_all)
      convert this
      rw [insert_erase hv]
    push_neg at hd
    replace hd : ∀ v ∈ s, G.degreeOn (s.erase v) v = k := by
      intro v hv
      apply le_antisymm ((degreeOn_le_degree _ _).trans (hbdd v)) <| hd _ hv
    have hins : ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s := by
      by_contra! hf
      obtain ⟨v, hv, w, ha, hns⟩ := hf
      have := degreeOn_lt_degree ⟨by rwa [← mem_neighborFinset] at ha, hns⟩
      rw [← degreeOn_erase, hd _ hv] at this
      exact this.not_le (hbdd v)
/-

lemma degreeOn_lt_degree {a v : α} {s : Finset α} (hv : v ∈ G.neighborFinset a ∧ v ∉ s) :
    G.degreeOn s a < G.degree a :=
  lt_of_le_of_ne (degreeOn_le_degree s a) fun hf ↦
     hv.2 ((degree_le_degreeOn_iff ..).1 hf.symm.le hv.1)
-/  --
    by_cases hem : s.Nonempty
    · obtain ⟨v₂, hv₂⟩ := hem
      have nc := hc <| insert v₂ (G.neighborFinset v₂ ∩ s)
      have ⟨v₁, v₃, h1, h3, hne, hnadj⟩ : ∃ v₁ v₃, v₁ ∈ G.neighborFinset v₂ ∩ s ∧
          v₃ ∈ G.neighborFinset v₂ ∩ s ∧ v₁ ≠ v₃ ∧ ¬ G.Adj v₁ v₃ := by
        contrapose! nc
        apply IsNClique.insert
          ⟨fun _ ha _ hb hne ↦ nc _ _ ha hb hne, by rw [← hd _ hv₂, degreeOn_erase]⟩
        intro b hb; rw [mem_inter, mem_neighborFinset] at hb
        exact hb.1
      -- have ⟨v₄, hv₄⟩ : ∃ v₄, G.Adj v₃ v₄ ∧ v₄ ≠ v₂ := by
      --   simp_rw [← mem_neighborFinset, Ne, ← mem_singleton, ← mem_sdiff]
      --   apply card_pos.1
      --   apply lt_of_lt_of_le _ (le_card_sdiff {v₂} (G.neighborFinset v₃))


      --   sorry
      rw [mem_inter, mem_neighborFinset] at h1 h3
      rw [adj_comm] at h3
      let v31 := (Walk.cons h1.1 nil).cons h3.1
      have h31 : v31.IsPath := by
        rw [cons_isPath_iff]
        simp only [cons_isPath_iff, isPath_iff_eq_nil, support_nil, List.mem_cons,
          List.not_mem_nil, or_false, true_and, support_cons, not_or]
        exact ⟨h1.1.ne, h3.1.ne, hne.symm⟩
      obtain ⟨vᵣ, q, hq, hss, hmax⟩ : ∃ vᵣ, ∃ q : G.Walk vᵣ v₃, (q.append v31).IsPath ∧
        (q.append v31).support.toFinset ⊆ s ∧
          G.neighborFinset vᵣ ⊆ ((q.append v31)).support.toFinset := by

        have v31s : v31.support.toFinset ⊆ s := by
          intro x hx; rw [support_cons,List.toFinset_cons,support_cons,List.toFinset_cons,
            support_nil, List.toFinset_cons] at hx
          simp only [List.toFinset_nil, insert_emptyc_eq, mem_insert, mem_singleton] at hx
          aesop
        obtain ⟨vᵣ, q, hq, hs, hnb⟩ := exists_maximal_path_subset s h31 v31s
        use vᵣ, q, hq, hs
        have vrs : vᵣ ∈ s := by apply hs; simp
        intro x hx
        have := (G.degreeOn_erase s vᵣ) ▸ ((hbdd vᵣ).trans (hd vᵣ vrs).symm.le)
        rw [degree_le_degreeOn_iff] at this
        exact hnb <| mem_inter.2 ⟨hx, this hx⟩

      by_cases hr : ((q.append v31)).support.toFinset = s
      · -- Main case 1
        -- TODO work out what the last ∧ condition should be below
        obtain ⟨vⱼ, hj⟩ : ∃ vⱼ, G.Adj v₂ vⱼ ∧ vⱼ ≠ v₁ ∧ vⱼ ≠ v₃ ∧ vⱼ ∈ s := by
          have := hk.trans <| (hd _ hv₂) ▸ (degreeOn_le_degree ..)
          rw [← card_neighborFinset_eq_degree] at this
          have :  1 ≤ #((G.neighborFinset v₂) \ {v₁, v₃}) := by
            rw [card_sdiff]
            · rw [card_pair hne]
              omega
            · intro x hx; simp only [mem_insert, mem_singleton, mem_neighborFinset] at *
              cases hx with
              | inl h => exact h ▸ h1.1
              | inr h => exact h ▸ h3.1.symm
          obtain ⟨vⱼ, hj⟩ := card_pos.1 this
          use vⱼ
          simp only [mem_sdiff, mem_neighborFinset, mem_insert, mem_singleton, not_or] at hj
          exact ⟨hj.1, hj.2.1, hj.2.2, hins _ hv₂ _ hj.1⟩
        let C₁ := G.ofNotAdj hnadj





        sorry

      · -- Main case 2
        replace hss := Finset.ssubset_iff_subset_ne.2 ⟨hss, hr⟩

        sorry

    · rw [not_nonempty_iff_eq_empty] at hem
      use (ofEmpty G).copy hem.symm
      intros
      rw [copy_eq, ofEmpty_eq]
      exact Nat.zero_lt_of_lt hk
  exact H #s le_rfl
#check Finset.two_lt_card



theorem Brooks (hk : 3 ≤ k) (hc : G.CliqueFree (k + 1)) (hbdd : ∀ v, G.degree v ≤ k) :
    G.Colorable k := by
  rw [colorable_iff_exists_bdd_nat_coloring]
  obtain ⟨C, heq⟩ := BrooksPartial hk hc hbdd (univ : Finset α)
  exact ⟨⟨C, fun hab ↦ C.valid (mem_univ _) (mem_univ _) hab⟩, by simpa using heq⟩

end PartialColoring

end partialcol
end SimpleGraph
