/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Vector.Defs
import Batteries.Data.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Backtracking.HydrophobicPolarModelBasic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Defs


/-!
# Hydrophobic-polar protein folding model: main theoretical development

A treatment of the hydrophobic-polar protein folding model in a generality
that covers rectangular, triangular and hexagonal lattices: `P_rect`, `P_tri`, `P_hex`.

We formalize the non-monotonicity of the objective function,
refuting an unpublished conjecture of Stecher.

We prove objective function bounds:
`P_tri ≤ P_rect ≤ P_hex` (using a theory of embeddings)
and for any model, `P ≤ b * l` and `P ≤ l * (l-1)/2` [see `pts_earned_bound_loc'`]

(The latter is worth keeping when `l ≤ 2b+1`.)

where `b` is the number of moves and `l` is the word length.
We also prove `P ≤ b * l / 2` using "handshake lemma" type reasoning
that was pointed out in Agarwala, Batzoglou et al. (`RECOMB 97`, Lemma 2.1)
and a symmetry assumption on the folding model that holds for `rect` and `hex` but not for `tri`.
The latter result required improving our definitions.

We prove the correctness of our backtracking algorithm for protein folding.

To prove some results about rotations
(we can always assume our fold starts by going to the right)
we use the type
`Fin n → α` instead of `Vector α n`

-/

open Mathlib

section Main_theoretical_development


/-- Extend a map on moves to lists. Trying a new def. Sep 13, 2024. -/
def morphSep {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) : List (Fin b₁) := match l with
  |.nil => []
  |.cons head tail =>
    (f head (path go₀ tail).head) :: morphSep f go₀ tail


/-- morph is length-preserving. New proof Sep 13, 2024 using rw [← itself]. -/
theorem morphSep_len {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) :
    (morphSep f go₀ l).length = l.length := match l with
  |.nil => by unfold morphSep; rfl
  |.cons head tail => by
    unfold morphSep; repeat (rw [List.length_cons])
    simp only [Nat.succ.injEq];
    rw [← morphSep_len f go₀]

/-- . -/
def morphSepᵥ {l:ℕ}
    {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (v : Vector (Fin b₀) l) : Vector (Fin b₁) l :=
  ⟨morphSep f go₀ v.1, by rw [morphSep_len];exact v.2⟩

/-- . -/
lemma morphSep_nil {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) :
  morphSep f go₀ [] = [] := by unfold morphSep;rfl


/-- Extend a map on moves to lists. -/
def morph {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) : List (Fin b₁) := by
  induction l with
  |nil => exact []
  |cons head tail tail_ih =>
    exact (f head (path go₀ tail).head) :: tail_ih

/-- morph is length-preserving -/
theorem morph_len {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) :
    (morph f go₀ l).length = l.length := by
  induction l with
  |nil => unfold morph; rfl
  |cons head tail tail_ih =>
    unfold morph; repeat (rw [List.length_cons])
    simp only [Nat.succ.injEq];
    rw [← tail_ih]; congr

/-- . -/
def morphᵥ {l:ℕ} {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α)
    (v : Vector (Fin b₀) l) : Vector (Fin b₁) l :=
  ⟨morph f go₀ v.1, by rw [morph_len];exact v.2⟩

/-- . -/
def morf {l:ℕ} {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁) (v : Vector (Fin b₀) l) :
    Vector (Fin b₁) l := Vector.map f v

 /-- Here, "f" means: f doesn't depend on space. "F" means: use Fin not Vector
 3/10/24. Hopefully simple enough to prove a lot about it. -/
def morfF {l : ℕ} {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁) (v : Fin l → (Fin b₀)) :
    Fin l → (Fin b₁) := fun i ↦ f (v i)

/-- . -/
def morf_list {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁) (v : List (Fin b₀)) :
    List (Fin b₁) := List.map f v

/-- finished March 8, 2024 -/
theorem morf_len {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁) (l : List (Fin b₀)) :
    (morf_list f l).length = l.length := by
  induction l
  · rfl
  unfold morf_list; repeat (rw [List.length_cons])
  simp

/-- . -/
abbrev σ {l:ℕ} {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α)
    (v : Vector (Fin b₀) l)  := morphᵥ f go₀ v

/-- . -/
theorem nearby_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
    {go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
    {x y : α} (hn : nearby go₀ x y):
    nearby go₁ x y := by
  unfold nearby at hn
  simp only [decide_eq_true_eq] at hn
  obtain ⟨a,ha⟩ := hn
  let Q := h_embed a x
  unfold nearby; simp only [decide_eq_true_eq]; rw [ha]; tauto

/-- . -/
theorem pt_loc_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
    {go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁) {l:ℕ}
    (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
    (htri: pt_loc go₀ fold a b phobic) :
           pt_loc go₁ fold a b phobic := by
  unfold pt_loc at *;
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *;
  constructor
  · tauto
  · exact nearby_of_embeds h_embed htri.2

/-- . -/
theorem pts_at_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
    {go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
    {l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
    pts_at' go₀ k ph fold ≤
    pts_at' go₁ k ph fold := by
  unfold pts_at'; apply Finset.card_le_card; intro a ha;
  simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]; simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at ha
  exact pt_loc_of_embeds h_embed fold a k ph ha


open BigOperators

/-- . -/
def pts_tot' {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α] {l:ℕ}
    (ph : Vector Bool l)(fold : Vector α l) := ∑ i : Fin l, pts_at' go i ph fold

/-- This is needed to get the Handshake Lemma bound from Agarwal et al.'s paper,
  but it is also just a nicer definition. March 13, 2024. think "ik = (i,k)"-/
def points_tot {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
    {l:ℕ} (ph : Vector Bool l) (fold : Vector α l) :=
  Finset.card (Finset.filter
    (fun ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop))
    (Finset.univ))


/-- In order to use the handshaking lemma from
 https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/DegreeSum.html#SimpleGraph.sum_degrees_eq_twice_card_edges
 Bonds:
 https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Dart.html#SimpleGraph.Dart
 we may introduce this:
 note that we form a graph on the amino acids rather than on the ambient space. -/
def SuccGraph {l:ℕ} : SimpleGraph (Fin l.succ) := {
  Adj := fun i j ↦ i.1 = j.1.succ ∨ j.1 = i.1.succ
  symm := fun i j h ↦ by simp only;simp only at h; tauto
  loopless := fun i ↦ by simp only [or_self];exact Nat.ne_of_lt (Nat.lt.base i.1)
}

/-- . -/
def ProteinGraph₀ {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α] {l:ℕ}
    (ph : Vector Bool l.succ) (fold : Vector α l.succ) : SimpleGraph (Fin l.succ) := {
  Adj := fun i j ↦ (pt_loc go fold i j ph) ∨ (pt_loc go fold j i ph)
  symm := by
    intro _ _ h;cases h with
    |inl => right;tauto
    |inr => left;tauto
  loopless := by
    intro i hi;unfold pt_loc at hi; simp only [Bool.and_self, Bool.and_eq_true,
      decide_eq_true_eq, or_self] at hi
    have : i.1.succ < i.1 := by tauto
    simp at this
}

/-- . -/
def slicer {l: ℕ} (P : (Fin l) → (Fin l) → Bool) : Fin l → Finset (Fin l × Fin l) :=
  fun k => Finset.filter (fun ik => ik.2 = k ∧ P ik.1 k = true) Finset.univ

/-- . -/
lemma slicer_disjointness {l: ℕ} (P : (Fin l) → (Fin l) → Bool) :
    ∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (slicer P k₁) (slicer P k₂) := by
  intro k₁ k₂ hk₁₂ A hA₁ hA₂ ik hikA
  have : ik ∈ slicer P k₁ := hA₁ hikA
  have h₁: ik.2 = k₁ ∧ P ik.1 k₁ = true := by
    unfold slicer at this;
    simp only [Finset.mem_filter,
    Finset.mem_univ, true_and] at this
    exact this
  have : ik ∈ slicer P k₂ := hA₂ hikA
  have h₂: ik.2 = k₂ ∧ P ik.1 k₂ = true := by
    unfold slicer at this;simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at this
    exact this
  have : k₁ = k₂ := by exact Eq.trans h₁.1.symm h₂.1
  exfalso; exact hk₁₂ this

/-- . -/
lemma slicer_card {l: ℕ} (P: Fin l → Fin l → Bool) (x : Fin l) :
    Finset.card (Finset.filter (fun ik : Fin l × Fin l => ik.2 = x ∧ P ik.1 x = true) Finset.univ) =
    Finset.card (Finset.filter (fun i_1 : Fin l => P i_1 x = true) Finset.univ) := by
  repeat rw [← Fintype.card_coe];simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]
  let f : {ik : Fin l × Fin l // ik.2 = x ∧ P ik.1 x} → { i_1 : Fin l // P i_1 x} :=
    fun ik ↦ ⟨ik.1.1, ik.2.2⟩
  have : Function.Bijective f := by
    constructor;intro u v huv;
    have : u.1 = v.1 := by
      apply Prod.ext;
      · exact congrArg (fun q ↦ q.1) huv
      · rw [u.2.1,v.2.1]
    exact SetCoe.ext this;intro y;exists ⟨⟨y.1,x⟩,by
      simp only [true_and];
      exact y.2⟩
  apply Fintype.card_of_bijective this

/-- Write `points_tot` as a disjoint union over `ik.2` to prove. March 14, 2024-/
theorem pts_tot'_eq_points_tot {α:Type} {β : Type} [Fintype β] (go : β → α → α)
    [DecidableEq α] {l:ℕ} (ph : Vector Bool l) (fold : Vector α l) :
    points_tot go ph fold = pts_tot' go ph fold := by
  unfold pts_tot' points_tot pts_at'
  let P := (fun ik1 k ↦ pt_loc go fold ik1 k ph)
  let t := fun k ↦
    (Finset.filter (fun ik : (Fin l) × (Fin l) ↦
      ik.2 = k ∧ P ik.1 k) Finset.univ)
  have : t = slicer P := rfl
  have hDU: Finset.card (Finset.biUnion Finset.univ (slicer P)) = ∑ k : Fin l,
            Finset.card ((slicer P) k) := Finset.card_biUnion (by
            have := slicer_disjointness P
            simp_all
            )
  rw [← this] at hDU
  let Q := Finset.sum_congr rfl (fun x : Fin l ↦ fun _ : x ∈ Finset.univ ↦ slicer_card P x)
  rw [← Q,← hDU]
  congr;apply Finset.ext;simp;

  intro a b
  constructor
  · intro h
    use b
    show (a, b) ∈ (fun k ↦ Finset.filter (fun ik ↦ ik.2 = k ∧ P ik.1 k = true) Finset.univ) b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · intro h
    obtain ⟨k,hk⟩ := h
    have : (a,b) ∈ (fun k ↦ Finset.filter (fun ik ↦ ik.2 = k ∧ P ik.1 k = true) Finset.univ) k := hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    have : b = k ∧ (fun ik1 k ↦ pt_loc go fold ik1 k ph) a k = true := this
    aesop

/-- . -/
theorem pts_bound_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
    {go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
    {l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
    pts_tot' go₀ ph fold ≤
    pts_tot' go₁ ph fold := by
  unfold pts_tot'; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds' h_embed _ _ _

/-- . -/
def pts_at_improved {α:Type} {β : Type} [Fintype β] (go : β → α → α)
    [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (fun i : Fin k.1.pred ↦ (pt_loc go fold (Fin_trans_pred i) k ph))
    Finset.univ
  )


/-- . -/
theorem pts_at_eq_pts_at'_improved  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
    [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
    pts_at_improved go k ph fold = pts_at' go k ph fold := by
  unfold pts_at_improved pts_at';
  (repeat rw [← Fintype.card_coe]);
  exact (change_type_card_improved go k ph fold).symm

/-- can make this i.pred I think -/
lemma pts_at_bound'_improved {α:Type} [DecidableEq α]
    {β : Type} [Fintype β]
    (go : β → α → α)
    {l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
    pts_at' go i ph fold ≤ i.1.pred := by
  rw [← pts_at_eq_pts_at'_improved, ← Finset.card_fin i.1.pred];
  unfold pts_at_improved
  apply Finset.card_le_card;
  apply Finset.filter_subset

/-- . -/
lemma Fin_sum_range (i : ℕ) : ∑ j : Fin (i+1), j.1 = i.succ * i / 2 := by
  have Q := Finset.sum_range_id i.succ;
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero] at Q
  rw [← Q]; exact (Finset.sum_range fun i => i).symm

/-- April 2, 2024 -/
lemma Fin_sum_range_pred (i : ℕ) : ∑ j : Fin (i+1), j.1.pred = i * (i-1) / 2 := by
  have Q := sum_pred i
  rw [← Q]
  exact Fin.sum_univ_eq_sum_range Nat.pred (i + 1)

/-- . -/
theorem pts_earned_bound_loc'_improved
    {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
    {l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
    pts_tot' go ph fold ≤ l * l.pred / 2 := by
  suffices pts_tot' go ph fold ≤ ∑ j : Fin l.succ, j.1.pred by calc
    _ ≤ ∑ j : Fin l.succ, j.1.pred := this
    _ = _                          := Fin_sum_range_pred _
  unfold pts_tot'; apply Finset.sum_le_sum; intro i; intro;
  exact pts_at_bound'_improved go ph fold i

/-- The result `pts_earned_bound_loc'_improved` is sharp in that for `l=2`,
we have words of length `3` and the points bound is `1`,
which does in fact happen for hex fold. April 2, 2024 -/
theorem when_zero {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
    {l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
    ph.length ≤ 2 → pts_tot' go ph fold = 0 := by
  intro h
  have : l = 0 ∨ l = 1 := by
    cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
    · left;linarith
    · tauto
  have Q := pts_earned_bound_loc'_improved go ph fold
  cases this with
  |inl h_1 =>
    subst h_1
    simp only [Nat.pred_zero, mul_zero, Nat.zero_div, nonpos_iff_eq_zero] at Q
    exact Q
  |inr h_1 =>
    subst h_1
    simp only [Nat.pred_succ, mul_zero, Nat.zero_div, nonpos_iff_eq_zero] at Q
    exact Q

/-- . -/
lemma path_len {α: Type} [Zero α] {β: Type} (go: β → α → α) {l: ℕ}
    (moves: Vector β l) : (path go moves.1).1.length = l.succ := by rw [(path go moves.1).2]; simp

/-- . -/
lemma path_at_len {α: Type} (base :α) {β: Type}
    (go: β → α → α) {l: ℕ} (moves: Vector β l) :
    (path_at base go moves.1).1.length = l.succ := by rw [(path_at base go moves.1).2]; simp

/-- . -/
def pathᵥ {l:ℕ}{α:Type} [Zero α] {β : Type} (go : β → α → α)
    (moves : Vector β l) : Vector α l.succ := ⟨(path go moves.1).1,path_len _ _⟩

/-- . -/
abbrev π  {l:ℕ}{α:Type} [Zero α] {β : Type}  (go : β → α → α)
    (moves : Vector β l) := pathᵥ go moves

/-- . -/
lemma pathᵥ_len {α: Type} [Zero α] {β: Type}
    (go: β → α → α) {l: ℕ} (moves: Vector β l) : (pathᵥ go moves).length = l.succ := by simp

/-- . -/
def pathᵥ_at {l:ℕ}{α:Type} (base : α) {β : Type} (go : β → α → α)
    (moves : Vector β l) : Vector α l.succ :=
  ⟨(path_at base go moves.1).1,path_at_len _ _ _⟩

/-- . -/
def pt_dir {α:Type} [Zero α] {β : Type} (go : β → α → α)
    {l:ℕ} (j : Fin l.succ) (moves: Vector β l) (ph : Vector Bool l.succ) :
    β → Fin l.succ → Prop  := fun a i ↦
  ph.get i ∧ ph.get j ∧ i.1.succ < j ∧ (pathᵥ go moves).get j = go a ((pathᵥ go moves).get i)

/-- . -/
theorem unique_loc  {α: Type} [Zero α] {β: Type}
    {go: β → α → α}
    {l:ℕ} {j: Fin l.succ}
    {moves: Vector β l} {ph : Vector Bool l.succ}
    (path_inj: Function.Injective (fun k : Fin l.succ ↦ (pathᵥ go moves).get k))
    (right_inj: right_injective go) (a : β) (i₀ i₁ : Fin l.succ)
    (hai₀ : pt_dir go j moves ph a i₀)
    (hai₁ : pt_dir go j moves ph a i₁) : i₀ = i₁ :=
  path_inj (right_inj a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

/-- . -/
theorem unique_dir {α: Type} [Zero α] {β: Type}
    {go: β → α → α} {l:ℕ} (j: Fin l.succ)
    (moves: Vector β l) (ph : Vector Bool l.succ)
    (left_inj : left_injective go)
    (i : Fin l.succ) (a₀ a₁ : β)
    (hai₀ : pt_dir go j moves ph a₀ i)
    (hai₁ : pt_dir go j moves ph a₁ i) : a₀ = a₁ :=
  left_inj ((pathᵥ go moves).get i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

/-- . -/
theorem unique_loc_dir {α: Type} [Zero α] {β: Type}
    {go: β → α → α} {l:ℕ} {j: Fin l.succ}
    {moves: Vector β l} {ph : Vector Bool l.succ}
    (path_inj: Function.Injective (fun k : Fin l.succ ↦ (pathᵥ go moves).get k))
    (right_inj: right_injective go)
    (left_inj : left_injective go) :
    (∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dir go j moves ph a i₀) (_ : pt_dir go j moves ph a i₁),
    i₀ = i₁)
    ∧
    (∀ (i : Fin l.succ) (a₀ a₁ : β)
    (_ : pt_dir go j moves ph a₀ i)
    (_ : pt_dir go j moves ph a₁ i),
    a₀ = a₁) :=
  And.intro (unique_loc path_inj right_inj) (unique_dir j _ ph left_inj)

/-- left_injective f
 which we can prove for tri_rect_embedding although it's harder than left_injective_tri! -/
theorem left_injective_of_embeds_in_strongly {α: Type}
    {b : ℕ}
    {go₀ go₁ : Fin b → α → α}
    (f: Fin b → α → Fin b)
    (is_emb: is_embedding go₀ go₁ f)
    (left_inj_emb : left_injective f)
    (left_inj_go: left_injective go₁) :
    left_injective go₀ := by
  intro x a₀ a₁ hxy
  simp only at hxy
  rw [is_emb a₀ x,is_emb a₁ x] at hxy
  exact left_inj_emb x (left_inj_go x hxy)

 /-- location, direction -/
theorem unique_loc_dir_rect {l:ℕ} (j: Fin l.succ)
    (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
    (path_inj: Function.Injective (fun k : Fin l.succ ↦ (pathᵥ rect moves).get k)):
    (∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : pt_dir rect j moves ph a i₀)
      (_ : pt_dir rect j moves ph a i₁),
    i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
    (_ : pt_dir rect j moves ph a₀ i)
    (_ : pt_dir rect j moves ph a₁ i),
    a₀ = a₁) :=
  unique_loc_dir path_inj right_injective_rect left_injective_rect

/-- . -/
theorem unique_loc_dir_hex {l:ℕ} (j: Fin l.succ)
    (moves: Vector (Fin 6) l) (ph : Vector Bool l.succ)
    (path_inj: Function.Injective (fun k : Fin l.succ ↦ (pathᵥ hex moves).get k)):
    (∀ (a : Fin 6) (i₀ i₁ : Fin l.succ) (_ : pt_dir hex j moves ph a i₀)
      (_ : pt_dir hex j moves ph a i₁),
    i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 6)
    (_ : pt_dir hex j moves ph a₀ i)
    (_ : pt_dir hex j moves ph a₁ i),
    a₀ = a₁) := unique_loc_dir path_inj right_injective_hex left_injective_hex


/-- This trivial instance is nonetheless needed. -/
instance  {α: Type} [Zero α] [DecidableEq α] {b:ℕ}
    {go: Fin b → α → α}
      {l:ℕ} (j : Fin l.succ) (ph : Vector Bool l.succ)
        (moves: Vector (Fin b) l) (a : Fin b)
    (i : Fin l.succ) : Decidable (pt_dir go j moves ph a i) :=
  decidable_of_iff (Vector.get ph i = true ∧
    Vector.get ph j = true ∧
      Nat.succ ↑i < ↑j ∧
      Vector.get (pathᵥ go moves) j = go a (Vector.get (pathᵥ go moves) i)) (by
        unfold pt_dir;tauto
      )

/-- . -/
theorem pts_at'_dir {α: Type} [Zero α] [DecidableEq α] {b:ℕ} {go: Fin b → α → α}
    {l:ℕ} (j : Fin l.succ) (ph : Vector Bool l.succ)
    (moves: Vector (Fin b) l)
    (path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
    (right_inj: right_injective go)
    (left_inj: left_injective go) : pts_at' go j ph (pathᵥ go moves) ≤ b := by
  unfold pts_at'
  have : Finset.filter (
      fun i : Fin (Nat.succ l) ↦ (∃ a, pt_dir go j moves ph a i)) Finset.univ =
        Finset.filter (
      fun i : Fin (Nat.succ l) ↦  pt_loc go (pathᵥ go moves) i j ph) Finset.univ := by
    apply Finset.ext;intro i;repeat (rw [Finset.mem_filter])
    simp only [Finset.mem_univ, true_and]
    unfold pt_dir pt_loc nearby;
    simp only [exists_and_left, Bool.and_eq_true, decide_eq_true_eq];
    tauto
  rw [← this,← choice_ex_finset_card (unique_loc_dir path_inj right_inj left_inj)]
  apply card_finset_fin_le

/-- Almost obsolete, except for `rect₃` fold which is not symmetric so that Handshake Lemma
reasoning does not apply. -/
theorem pts_earned_bound_dir' {α: Type} [Zero α] [DecidableEq α] {b:ℕ}
    {go: Fin b → α → α}
    {l:ℕ} (ph : Vector Bool l.succ)
    (moves: Vector (Fin b) l)
    (path_inj  : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
    (right_inj : right_injective go)
    (left_inj  : left_injective go) : pts_tot' go ph (pathᵥ go moves) ≤ l.succ * b := by
  suffices pts_tot' go ph (pathᵥ go moves) ≤
    Finset.sum (Finset.univ : Finset (Fin l.succ)) (fun _ ↦ b) by
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at this
    tauto
  apply Finset.sum_le_sum; intro i; intro
  exact pts_at'_dir i ph moves path_inj right_inj left_inj

/-- . -/
theorem independence_in_symmetric_pts_earned_bound_dir'₁ :
    ∃ (α β : Type) (_ : Fintype β) (_: DecidableEq α), ∃ go : β → α → α,
    right_injective go ∧ left_injective go ∧ ¬ Symmetric (fun x y ↦ nearby go x y) := by
  use ℤ×ℤ, Fin 3, inferInstance, inferInstance, rect₃
  constructor
  · exact right_injective_rect₃
  · constructor
    · exact left_injective_rect₃
    · intro hc
      specialize hc (show nearby rect₃ (0,0) (0,1) by decide)
      tauto

/-- "does not imply" -/
def f_dni : Fin 2 × Fin 2 → Fin 2
  | ⟨0,0⟩ => 0
  | ⟨0,1⟩ => 0
  | ⟨1,0⟩ => 1
  | ⟨1,1⟩ => 0

/-- . -/
def g : Fin 2 → Fin 2 → Fin 2 := fun x y ↦ f_dni ⟨x,y⟩

/-- . -/
instance : Decidable (Symmetric fun x y => nearby g x y = true) := by
  unfold Symmetric;unfold nearby;exact inferInstance

/-- . -/
instance : Decidable (left_injective g) := by
  unfold left_injective;exact inferInstance

/-- . -/
instance : Decidable (right_injective g) := by
  unfold right_injective;exact inferInstance

-- #eval Symmetric (fun x y ↦ nearby g x y) ∧ ¬ right_injective g ∧ ¬ left_injective g

/-- This is the first example I thought of that has a Symmetric nearby function,
  but is neither left nor right injective. -/
def ctrex : (Fin 2 → Fin 2) → Fin 2 → Fin 2 := fun f x ↦ f x

/-- . -/
theorem independence_in_symmetric_pts_earned_bound_dir'₂ :
    ∃ (α β : Type) (_ : Fintype β) (_: DecidableEq α), ∃ go : β → α → α,
    ¬ right_injective go ∧ ¬ left_injective go ∧ Symmetric (fun x y ↦ nearby go x y) := by
  use Fin 2, Fin 2 → Fin 2, inferInstance, inferInstance, ctrex
  constructor;
  · intro hc; have R := @hc 0 0 1 rfl; simp at R
  · constructor
    · intro hc
      have R : (1:Fin 2) = 0 := congrArg (fun f ↦ f 1) (@hc 0 (fun x ↦ x) (fun _ ↦ 0) rfl)
      simp only [Fin.isValue, one_ne_zero] at R
    · unfold Symmetric
      intro a b _;unfold nearby;simp only [decide_eq_true_eq];exists (fun _ ↦ a)



/-- this is anyway obsolete since Handshake lemma gives another /2 factor -/
theorem pts_earned_bound' {α: Type} [Zero α] [DecidableEq α] {b:ℕ}
    {go: Fin b → α → α}
    {l:ℕ} (ph : Vector Bool l.succ)
    (moves: Vector (Fin b) l)
    (path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
    (right_inj : right_injective go)
    (left_inj : left_injective go) :
    pts_tot' go ph (pathᵥ go moves) ≤ min (l.succ * b) (l * l.pred / 2) := by
  suffices (
    pts_tot' go ph (pathᵥ go moves) ≤ l.succ * b
    ∧ pts_tot' go ph (pathᵥ go moves) ≤ l * l.pred / 2) by
    exact Nat.le_min.mpr this
  constructor
  · exact pts_earned_bound_dir' ph moves path_inj right_inj left_inj
  · exact pts_earned_bound_loc'_improved go ph (pathᵥ go moves)


/-- . -/
theorem two_heads {α : Type} {k :ℕ} (v: Vector α k.succ) (w : List α) (hw : w ≠ [])
    (h : v.1 = w) : Vector.head v = List.head w hw := by
  symm at h
  cases w with
  |nil => tauto
  |cons head tail =>
    simp only [List.head_cons]
    have : tail.length = k := by
      let v2 := v.2
      rw [← h] at v2
      rw [List.length_cons, Nat.succ.injEq] at v2
      exact v2
    have : v = head ::ᵥ ⟨tail, this⟩ := by
      apply Vector.eq
      simp only [Vector.toList_cons, Vector.toList_mk]
      rw [h]
      rfl
    rw [this]; simp

/-- . -/
theorem path_cons {α:Type} [Zero α] {b₀ : ℕ}
    (go₀ : Fin b₀ → α → α) (head : Fin b₀) (tail : List (Fin b₀)) :
    (path go₀ (head :: tail)).1 = ((go₀ head (path go₀ tail).head) :: (path go₀ tail).1) :=
  rfl

/-- . -/
theorem path_cons_vec {α:Type} [Zero α] {b₀ : ℕ}
    (go₀ : Fin b₀ → α → α) (head : Fin b₀) (tail : List (Fin b₀)) :
    (path go₀ (head ::        tail)) = ((go₀  head (path go₀ tail).head) ::ᵥ (path go₀ tail)) :=
  rfl

/-- . -/
theorem path_at_cons {α:Type} (base :α) {b₀ : ℕ} (go₀ : Fin b₀ → α → α)
    (hd : Fin b₀) (tl : List (Fin b₀)) :
    (path_at base go₀ (hd ::        tl)).1
    = ((go₀  hd (path_at base go₀ tl).head) :: (path_at base go₀ tl).1) :=
  rfl


/-- . -/
theorem path_at_cons_vec {α:Type} (base :α) {b₀ : ℕ}
    (go₀ : Fin b₀ → α → α) (hd : Fin b₀) (tl : List (Fin b₀)) :
    (path_at base go₀ (hd :: tl)) =
    ((go₀ hd (path_at base go₀ tl).head) ::ᵥ (path_at base go₀ tl)) :=
  rfl

/-- . -/
lemma plane_assoc (x y z : ℤ×ℤ) : x + (y+z) = (x+y)+z := by ring



-- #eval pathF' rect ![0,2] 2
-- #eval rect (![0,2] 1) (pathF' rect ![0,2] 1)

-- #eval pathF' rect ![0,2] 1
-- #eval rect (![0,2] 0) (pathF' rect ![0,2] 0)




/-- . -/
theorem orderly_injective_helper {β:Type} (x : ℕ → β) (a b : β) (hab: a ≠ b)
    (h₀ : x 0 = a) (j:ℕ) (hj : ∃ i, i < j ∧ x i.succ = b)
    (h₂: ∀ i, i < j → x i = a ∨ x i = b) [DecidablePred fun n => n < j ∧ x (Nat.succ n) = b] :
    (∃ i, i < j ∧ x i = a ∧ x i.succ = b) := by
  use Nat.find hj
  have hj_spec := Nat.find_spec hj
  constructor
  · exact hj_spec.1
  · constructor
    cases h₂ (Nat.find hj) hj_spec.1 with
    |inl h => exact h
    |inr h =>
      obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero <|fun hc => hab <| .trans (hc ▸ h₀).symm h
      have : i < j := calc i < i.succ      := Nat.lt.base i
                           _ = Nat.find hj := hi.symm
                           _ < j           := hj_spec.1
      have : Nat.find hj ≤ i := Nat.find_le ⟨this, hi ▸ h⟩
      simp_all
    exact hj_spec.2


/-- . -/
theorem fin_fin {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
    i < k := calc
  _ < j.1 := h
  _ ≤ k := Fin.is_le j

/-- . -/
theorem fin_fi {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
    i < k.succ := calc
  _ < j.1 := h
  _ ≤ k.succ := Fin.is_le'

/-- . -/
theorem orderly_injective_helper₁ {β:Type} {k : ℕ} {x : (Fin k.succ) → β} {a b : β} (hab: a ≠ b)
    (h₀ : x 0 = a) {j : Fin k.succ} (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = b)
    (h₂: ∀ i, i.1 < j.1 → x i = a ∨ x i = b)
    [DecidablePred fun n => ∃ (h : n < j.1), x (Fin.succ ⟨n, fin_fin h⟩) = b] :
    (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = a ∧ x (Fin.succ i) = b) := by
  have hthis: ∃ n : ℕ, ∃ h : n < j.1, x (Fin.succ ⟨n,fin_fin h⟩) = b := by
    obtain ⟨i,hi⟩ := hj;exists i.1;exists hi.1;exact hi.2
  have h : Nat.find hthis < j.1 := (Nat.find_spec hthis).1
  exists ⟨Nat.find hthis,fin_fin h⟩
  let h := (Nat.find_spec hthis).1
  constructor
  · exact h
  constructor
  cases h₂ ⟨Nat.find hthis,fin_fi h⟩ h with
  |inl h_1 => exact h_1
  |inr h_1 =>
    have hthis₀: (⟨(Nat.find hthis),fin_fi h⟩ : Fin k.succ) ≠ 0 :=
      fun hc => hab <| Eq.trans (hc ▸ h₀).symm h_1
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero <| fun hc => hthis₀ (Fin.ext hc)
    have : Nat.find hthis ≤ i := Nat.find_le (by
      constructor
      · simp only [Fin.succ_mk];
        simp_rw [← Nat.succ_eq_add_one,← hi];
        exact h_1
      calc
        i < i.succ          := Nat.lt.base i
        _ = Nat.find hthis  := hi.symm
        _ < j               := (Nat.find_spec hthis).1
    )
    simp_all
  exact (Nat.find_spec hthis).2

/-- . -/
theorem orderly_injective_helper₂ (k:ℕ) (x : (Fin k.succ) → Fin 4) (h₀ : x 0 = 0) (j:Fin k.succ)
    (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = 1) (h₂: ∀ i, i.1 < j.1 → x i = 0 ∨ x i = 1) :
    (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = 0 ∧ x (Fin.succ i) = 1) :=
  orderly_injective_helper₁ (Fin.zero_ne_one) h₀ hj h₂


/-- . -/
theorem path_len' {α: Type} [Zero α] {β: Type} (go: β → α → α) (l: ℕ)
    (moves: List β) (hm: moves.length = l) : List.length (path go moves).1 = Nat.succ l :=
  hm ▸ (path go moves).2


/-- . -/
lemma path_nil {α:Type} [Zero α] {β:Type} (go : β → α → α) :
    (path go []).1 = [0] := rfl

/-- . -/
lemma path_at_nil {α:Type} (base:α) {β:Type} (go : β → α → α) :
    (path_at base go []).1 = [base] := rfl

/-- . -/
lemma path_at_nil_vec {α:Type} (base:α) {β:Type} (go : β → α → α):
    (path_at base go []) = ⟨[base],by simp⟩ := rfl

/-- . -/
lemma ne_nil_of_succ_length {α :Type} {k:ℕ} (tail_ih: Vector α k.succ) : tail_ih.1 ≠ [] := by
  have : tail_ih.1.length = k.succ := tail_ih.2
  intro hc; rw [hc] at this; simp at this


/-- . -/
lemma path_eq_path_morph {α:Type} [Zero α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
    (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α) (g : is_embedding go₀ go₁ f)
    (moves : List (Fin b₀)) :
  (path go₀ moves).1 = (path go₁ (morph f go₀ moves)).1 := by
    induction moves with
    |nil => unfold morph; simp only [List.length_nil]; repeat (rw [path_nil])
    |cons head tail tail_ih =>
      rw [path_cons,g head (Vector.head (path go₀ tail)),tail_ih ]
      unfold morph; simp only [List.length_cons];
      rw [path_cons]; simp only [List.cons.injEq, and_true]
      have : (Vector.head (path go₀ tail))
        = (Vector.head (path go₁ (List.rec []
        (fun head tail tail_ih => f head (Vector.head (path go₀ tail)) :: tail_ih) tail))) := by
        rw [two_heads (path go₀ tail) (path go₀ tail).1 (ne_nil_of_succ_length _) rfl]
        simp_rw [tail_ih]
        rw [two_heads]
        unfold morph
        simp
      exact congrArg _ this

/-- . -/
lemma path_eq_path_morphᵥ {l:ℕ} {α:Type} [Zero α] {b₀ b₁ : ℕ}
    (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
    (g : is_embedding go₀ go₁ f) (moves : Vector (Fin b₀) l) :
    (path go₀ moves.1).1 = (path go₁ (morphᵥ f go₀ moves).1).1 :=
  path_eq_path_morph f go₀ go₁ g moves.1

/-- . -/
lemma pathᵥ_eq_path_morphᵥ1 {l:ℕ} {α:Type} [Zero α] {b₀ b₁ : ℕ}
    (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
    (g : is_embedding go₀ go₁ f) (moves : Vector (Fin b₀) l) :
    (pathᵥ go₀ moves).1 = (pathᵥ go₁ (morphᵥ f go₀ moves)).1 :=
  path_eq_path_morphᵥ f go₀ go₁ g moves

/-- . -/
lemma pathᵥ_eq_path_morphᵥ {l:ℕ} {α:Type} [Zero α] {b₀ b₁ : ℕ}
    (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
    (g : is_embedding go₀ go₁ f) (moves : Vector (Fin b₀) l) :
    pathᵥ go₀ moves = pathᵥ go₁ (morphᵥ f go₀ moves) :=
  Vector.eq (pathᵥ go₀ moves) (pathᵥ go₁ (morphᵥ f go₀ moves))
    <| pathᵥ_eq_path_morphᵥ1 f go₀ go₁ g moves

/-- . -/
def path_transformed {α: Type} [Zero α] {b₀ b₁: ℕ}
    (f: Fin b₀ → α → Fin b₁) (go₀: Fin b₀ → α → α) (go₁: Fin b₁ → α → α)
    (l: List (Fin b₀)) : Vector α l.length.succ :=
  ⟨
    (path go₁ (morph f go₀ l)).1,
    by rw [path_len go₁ ⟨morph f go₀ l, morph_len f go₀ l⟩]
  ⟩

/-- . -/
def path_transformedᵥ {l:ℕ} {α: Type} [Zero α] {b₀ b₁: ℕ}
    (f: Fin b₀ → α → Fin b₁) (go₀: Fin b₀ → α → α) (go₁: Fin b₁ → α → α)
    (v: Vector (Fin b₀) l) : Vector α l.succ :=
  pathᵥ go₁ (morphᵥ f go₀ v)


/- Finished February 10, 2024:
When transforming, the underlying path in say ℤ×ℤ is unchanged.
-/
theorem transform_of_embed {α:Type} [Zero α] {b₀ b₁ : ℕ}
    (f : Fin b₀ → α → Fin b₁) (go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
    (l : List (Fin b₀)) (h_embed: is_embedding go₀ go₁ f) :
    path_transformed f go₀ go₁ l = path go₀ l := by
  apply SetCoe.ext; unfold path_transformed; simp only;
  unfold is_embedding at h_embed;
  induction l with
  |nil =>
    simp only [List.length_nil];
    unfold morph;
    simp only [List.length_nil]
    rfl
  |cons head tail tail_ih =>
    have morph_cons :
      (morph f go₀ (head :: tail)) = (f head ((path go₀ tail).head)) :: (morph f go₀ (tail)) := rfl
    rw [morph_cons];
    repeat (rw [path_cons])
    simp only [List.cons.injEq]
    constructor
    · let a := (Vector.head (path go₀ tail))
      rw [h_embed head a]
      have : path go₁ (morph f go₀ tail)
        = ⟨(path go₀ tail).1,(by rw [morph_len]; exact (path go₀ tail).2)⟩ :=
        Vector.eq _ _ (by unfold Vector.toList; rw [← tail_ih])
      rw [this]
      have hau: ∃ a u, path go₀ tail = a ::ᵥ u := Vector.exists_eq_cons (path go₀ tail)
      have : Vector.head ⟨
        (path go₀ tail).1, by
          show (path go₀ tail).1.length = (morph f go₀ tail).length.succ
          rw [morph_len]; exact (path go₀ tail).2
        ⟩ = Vector.head (path go₀ tail) := by
        obtain ⟨a,ha⟩ := hau
        obtain ⟨u,hu⟩ := ha
        rw [hu]; simp only [Vector.cons_val, Vector.head_cons]; rfl
      · exact congr_arg _ this
    · rw [tail_ih]

/-- . -/
def pts_tot_bound {α:Type} [Zero α] [DecidableEq α]
    {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
    ∀ moves : Vector β l, Function.Injective (fun k ↦ (path go moves.1).1.get k) →
    pts_tot' go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q

-- def myList {b l:ℕ} := Finset.toList (Finset.univ : Finset (Vector (Fin b) l))
-- Finset.toList is not computable!

/-- This version of pts_tot_bound is correct even for the asymmetric 3-move version of rect: -/
def pts_tot_bound_rev {α:Type} [Zero α] [DecidableEq α]
    {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
    ∀ moves : Vector β l, Function.Injective (fun k ↦ (path go moves.1).1.get k) →
    pts_tot' go ph (⟨(path go moves.1).1.reverse,by
      rw [List.length_reverse]
      exact path_len _ _
    ⟩) ≤ q

/-- . -/
instance {l:ℕ} {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    {ph : Vector Bool l.succ}
    (go : β → α → α) :
    DecidablePred (pts_tot_bound go ph) := by
  unfold pts_tot_bound pts_tot'
  exact inferInstance

/-- . -/
instance {l:ℕ} {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    {ph : Vector Bool l.succ}
    (go : β → α → α) : DecidablePred fun n => pts_tot_bound go ph n := by
  unfold pts_tot_bound pts_tot'
  exact inferInstance

/-- . -/
instance {l:ℕ} {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {ph : Vector Bool l.succ} :
    DecidablePred (pts_tot_bound_rev go ph) := by
  unfold pts_tot_bound_rev pts_tot'
  exact inferInstance

/-- . -/
instance {l:ℕ} {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {ph : Vector Bool l.succ} :
    DecidablePred fun n => pts_tot_bound_rev go ph n := by
  unfold pts_tot_bound_rev pts_tot'
  exact inferInstance

/-- . -/
theorem pts_tot_bound_rev_exists {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
    ∃ q, pts_tot_bound_rev go ph q :=
  ⟨l * l.pred / 2, fun moves _ =>
   pts_earned_bound_loc'_improved go ph (⟨(path go moves.1).1.reverse,by
    rw [List.length_reverse]
    exact path_len _ _
  ⟩)⟩

/-- . -/
theorem pts_tot_bound_exists {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
    ∃ q, pts_tot_bound go ph q :=
  ⟨l * l.pred / 2, fun moves _ =>
    pts_earned_bound_loc'_improved go ph (⟨(path go moves.1).1,path_len _ _⟩)⟩

/-- HP is the HP protein folding model "objective function" or "value function": -/
def HP {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_exists go ph)
/- ph has to be of succ type because there will at least be an amino acid at the origin. -/

/-- For nonsymmetric "nearby" relations we must use this version.-/
def HP_rev {α:Type} [Zero α] [DecidableEq α] {β : Type} [Fintype β]
    (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) : ℕ :=
  Nat.find (pts_tot_bound_rev_exists go ph)

/-- . -/
def P_tri'  {l:ℕ} := fun ph : Vector Bool l.succ ↦ HP tri  ph
/-- . -/
def P_rect' {l:ℕ} := fun ph : Vector Bool l.succ ↦ HP rect ph
/-- . -/
def P_rect₃' {l:ℕ} := fun ph : Vector Bool l.succ ↦ HP_rev rect₃ ph
/-- . -/
def P_hex'  {l:ℕ} := fun ph : Vector Bool l.succ ↦ HP hex  ph
-- Is P_rect₃' ≥ P_tri' ?


-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ ⟨[(0,0),(1,0),(1,1),(0,1)],rfl⟩
-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ ⟨[(0,0),(1,0),(1,1),(0,1)].reverse,rfl⟩
-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ (path rect₃ [1,2,0])
-- #eval (path rect₃ [1,2,0])
-- #eval P_rect₃' ⟨[true,true,true,true,true,true,true],rfl⟩

/-- . -/
theorem Vector_inj_of_list_inj {t : Type} {n : ℕ}
    {v : Vector t n} (h: Function.Injective fun k => List.get v.1 k) :
    Function.Injective fun k => Vector.get v k := by
  intro x y hxy;unfold Function.Injective at *;simp only at hxy
  have hx: x.1 < v.1.length := by
    let Q := x.2;have : v.1.length = n := v.2;simp_rw [← this] at Q;exact Q
  have hy: y.1 < v.1.length := by
    let Q := y.2;have : v.1.length = n := v.2;simp_rw [← this] at Q;exact Q
  have : List.get v.1 ⟨x.1,hx⟩ = List.get v.1 ⟨y,hy⟩ := by exact hxy
  let Q := h this; simp only [Fin.mk.injEq] at Q
  exact Fin.ext Q

/-- . -/
theorem list_inj_of_Vector_inj {t : Type} {n : ℕ}
    {v : Vector t n} (h: Function.Injective fun k => Vector.get v k) :
    Function.Injective fun k => List.get v.1 k := by
  intro x y hxy;unfold Function.Injective at *
  have hx: x.1 < n := by
    have Q := x.2
    simp_rw [v.2] at Q
    exact Q
  have hy: y.1 < n := by
    let Q := y.2;have : v.1.length = n := v.2;simp_rw [this] at Q;exact Q
  have : Vector.get v ⟨x.1,hx⟩ = Vector.get v ⟨y.1,hy⟩ := hxy
  let Q := h this; simp only [Fin.mk.injEq] at Q hxy
  exact Fin.ext Q

/-- . -/
theorem P_tri_lin_bound {l:ℕ} (ph : Vector Bool l.succ) :
    P_tri' ph ≤ l.succ * 3 :=
  Nat.find_le (fun _ path_inj =>
    pts_earned_bound_dir' _ _ (Vector_inj_of_list_inj path_inj)
      right_injective_tri left_injective_tri)

/-- . -/
theorem P_hex_lin_bound {l:ℕ} (ph : Vector Bool l.succ) :
    P_hex' ph ≤ l.succ * 6 :=
  Nat.find_le (fun _ path_inj =>
    pts_earned_bound_dir' _ _ (Vector_inj_of_list_inj path_inj)
    right_injective_hex left_injective_hex)

/-- . -/
theorem P_rect_lin_bound {l:ℕ} (ph : Vector Bool l.succ) : P_rect' ph ≤ l.succ * 4 :=
  Nat.find_le (fun _ path_inj =>
    pts_earned_bound_dir' _ _ (Vector_inj_of_list_inj path_inj)
      right_injective_rect left_injective_rect)

/-- . -/
theorem value_bound_of_embeds_strongly {α:Type} [Zero α] [DecidableEq α] {b₀ b₁ : ℕ}
    {go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : go₀ ≼ go₁)
    {l:ℕ} (ph : Vector Bool l.succ) : HP go₀ ph ≤ HP go₁ ph :=
  Nat.find_mono (fun q hq moves h_inj => by
  have ⟨f,hf⟩ := h_embed
  have h_inj': Function.Injective (fun k ↦ (path go₁ (morph f go₀ moves.1)).1.get k) :=
    congrArg (fun x ↦ x.1) (transform_of_embed f go₀ go₁ (moves.1) hf) ▸ h_inj
  let moves' :=
    (⟨morph f go₀ moves.1, (by rw [morph_len]; exact moves.2)⟩ : Vector (Fin b₁) l)
  calc
  _ ≤ pts_tot' go₁ ph ⟨(path go₀  moves.1).1, path_len _ _⟩ :=
      pts_bound_of_embeds' (embeds_of_strongly_embeds h_embed) ph
        (⟨(path go₀ moves.1).1,path_len _ _⟩)
  _ = pts_tot' go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ := by
      simp_rw [path_eq_path_morph f go₀ go₁ hf moves.1]
  _ ≤ q                                                     := hq moves' h_inj')


-- #eval HP_rev rect₃ ⟨[true,false,false,false,false,true,false,false,false,true],rfl⟩

-- #eval HP tri ⟨[true,false,false,false,false,true,false,false,false,true],rfl⟩


/-- . -/
theorem embeds_strongly_tri_quad : tri ≼ rect :=
  ⟨tri_rect_embedding, tri_rect_embedding_is_embedding⟩

/-- . -/
theorem embeds_strongly_quad_hex : rect ≼ hex :=
  ⟨rect_hex_embedding, rect_hex_embedding_is_embedding⟩

/- Here are some quotable results:
  The degree 3 "hexagonal lattice" protein folding model has an objective function
  P_tri that is bounded by that of the usual HP 2D model.
  Similarly for P_quad and P_hex.
-/

/-- . -/
theorem HP_quad_bounds_tri {l:ℕ} (ph : Vector Bool l.succ) : HP tri ph ≤ HP rect ph :=
  value_bound_of_embeds_strongly embeds_strongly_tri_quad _

/-- . -/
theorem HP_hex_bounds_quad {l:ℕ} (ph : Vector Bool l.succ) : HP rect ph ≤ HP hex ph :=
  value_bound_of_embeds_strongly embeds_strongly_quad_hex _

/- We want to show that rect is not ≤ hex₄;
because that would be an effective separation result rect ≤ hex₄ ≤ hex
(assuming of course that hex is NP-complete)
True for length up to 7!
-/



-- abbrev t := true
-- abbrev f := false
-- #eval numtrue   (⟨[f,f,f,f,f,t],rfl⟩ : Vector Bool 6)

-- abbrev xx := (⟨[f,f,f,f,f,f],rfl⟩ : Vector Bool 6)
-- abbrev y := [
--   (⟨[f,f,f,f,f,f],rfl⟩ : Vector Bool 6),
--   (⟨[f,f,f,f,f,t],rfl⟩ : Vector Bool 6),
-- ]
-- -- #eval xx
-- -- #eval [HP_rev rect ⟨xx,rfl⟩, HP_rev hex₄ ⟨x,rfl⟩]
-- #eval Vector.map (fun a ↦ [HP_rev rect a, numtrue a, HP_rev hex₄ a]) ⟨y,rfl⟩

end Main_theoretical_development
