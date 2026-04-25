/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Basic

/-!
# Abstract Sperner's Lemma

We prove Sperner's lemma for an abstract cell complex satisfying
adjacency axioms, via the door-counting parity argument.

## Main definitions

* `CellComplex`: An abstract cell complex with adjacency.
* `CellComplex.IsPanchromatic`: A cell whose vertices receive
  all `d + 1` colors.
* `CellComplex.IsDoor`: A codimension-1 face (door) whose
  remaining vertices receive colors `{0, ..., d - 1}`.

## Main results

* `CellComplex.sperner_parity`: The panchromatic cell count is
  congruent mod 2 to the boundary door count.
* `CellComplex.sperner`: If boundary doors are odd, a
  panchromatic cell exists.

## Implementation notes

The `CellComplex` structure axiomatizes exactly the adjacency
properties needed for the door-counting proof, without assuming
any geometric embedding. This follows the approach suggested by
Yaël Dillies on mathlib4#25231: prove the combinatorial core
abstractly, then separately verify that geometric simplicial
complexes satisfy the axioms.

Interior doors pair via the adjacency involution (even count).
Boundary doors are unpaired. A per-cell parity argument shows
total doors ≡ panchromatic cells (mod 2).

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, combinatorics, parity, triangulation, door-counting
-/

@[expose] public section

open Finset

/-- A fixed-point-free involution on a finset has even
cardinality: every element pairs with its distinct image. -/
theorem Finset.even_card_of_fpf_invol {α : Type*}
    (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  classical
  -- Pair each element with its involution image: ∑ _ ∈ S, (1 : ZMod 2) = 0
  have hsum : ∑ _ ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun _ _ => by decide)
      (fun a ha _ => hNe a ha)
      hMem hInv
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ 2).mp hsum
  exact ⟨k, by omega⟩

section DoorCountParity

/-! ### Door count parity

The central combinatorial fact: the number of "door positions"
of a coloring `f : Fin (d+1) → Fin (d+1)` has parity equal to
the surjectivity indicator of `f`.

The key invariant is the **fiber structure** of the coloring.
A surjection `Fin (d+1) → Fin d` has exactly one fiber of
size 2 (by pigeonhole), giving two door positions (even).
A bijection `Fin (d+1) → Fin (d+1)` has exactly one door
position. A non-surjection missing some lower color has none.
-/

/-- If a lower color `j₀ : Fin d` has no preimage under `f`,
then no position is a door: we cannot cover all of
`{0, ..., d-1}` while omitting any vertex. -/
private lemma door_filter_empty_of_missing_color (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (j₀ : Fin d)
    (hmiss : ¬∃ i : Fin (d + 1),
      f i = ⟨j₀.val, by omega⟩) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)) = ∅ := by
  rw [filter_eq_empty_iff]
  intro k _; push_neg
  exact ⟨j₀, fun i _ h => hmiss ⟨i, h⟩⟩

/-- If natural numbers indexed by a finset sum to 1, exactly one
equals 1 and the rest equal 0. -/
private lemma exists_of_sum_eq_one {ι : Type*}
    {s : Finset ι} {f : ι → ℕ}
    (hsum : ∑ i ∈ s, f i = 1) :
    ∃ a ∈ s, f a = 1 ∧ ∀ b ∈ s, b ≠ a → f b = 0 := by
  classical
  have ⟨a, ha, hfa⟩ : ∃ a ∈ s, 0 < f a := by
    by_contra h; push_neg at h
    have := Finset.sum_eq_zero (fun i hi =>
      Nat.eq_zero_of_le_zero (h i hi))
    omega
  have hle : f a ≤ 1 :=
    hsum ▸ Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) ha
  have hfa_eq : f a = 1 := by omega
  have hrest : ∑ x ∈ s.erase a, f x = 0 := by
    have := Finset.add_sum_erase s f ha
    omega
  exact ⟨a, ha, hfa_eq, fun b hb hne =>
    Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hne, hb⟩)).trans
        hrest.le)⟩

/-- **Pigeonhole for one extra element**: a surjection
`Fin (d+1) → Fin d` has exactly one fiber of size 2, with
all other fibers of size 1. -/
private lemma surjection_unique_dup_fiber (d : ℕ)
    (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    ∃ c₀ : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c₀)).card = 2 ∧
      ∀ c ≠ c₀, (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card =
        1 := by
  have hcard_ge : ∀ c : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card ≥ 1 := by
    intro c; obtain ⟨i, hi⟩ := hcov c
    exact Finset.card_pos.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have htotal : ∑ c : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card =
      d + 1 := by
    rw [← Finset.card_biUnion (by
      intro x _ y _ hxy
      apply Finset.disjoint_filter.mpr
      intro i _ h1 h2; exact hxy (h1.symm.trans h2))]
    have hbU : Finset.biUnion univ (fun c : Fin d =>
        univ.filter
          (fun i : Fin (d + 1) => f i = c)) =
        univ := by
      ext i; constructor
      · intro _; exact mem_univ _
      · intro _
        rw [mem_biUnion]
        exact ⟨f i, mem_univ _,
          mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    rw [hbU, card_univ, Fintype.card_fin]
  have hexcess : ∑ c : Fin d,
      ((univ.filter
        (fun i : Fin (d + 1) => f i = c)).card - 1) =
      1 := by
    have hadd : ∀ c : Fin d,
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card -
          1 + 1 =
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card := by
      intro c; have := hcard_ge c; omega
    have := Finset.sum_congr
      (show (univ : Finset (Fin d)) = univ from rfl)
      (fun c _ => hadd c)
    simp only [Finset.sum_add_distrib,
      Finset.sum_const, card_univ, Fintype.card_fin,
      htotal, smul_eq_mul] at this
    omega
  obtain ⟨c₀, _, hc₀_eq, hc₀_rest⟩ :=
    exists_of_sum_eq_one hexcess
  exact ⟨c₀,
    by have := hcard_ge c₀; omega,
    fun c hc => by
      have := hc₀_rest c (mem_univ _) hc
      have := hcard_ge c; omega⟩

/-- When `f : Fin (d+1) → Fin d` is surjective, the door
positions are exactly the two elements of the unique fiber of
size 2. In particular, the door count is even. -/
private lemma even_card_doors_of_surjective (d : ℕ)
    (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    Even (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d,
        ∃ i : Fin (d + 1), i ≠ k ∧ f i = j)).card := by
  obtain ⟨c₀, hc₀_eq, hc₀_rest⟩ :=
    surjection_unique_dup_fiber d f hcov
  obtain ⟨k₁, k₂, hk₁, hk₂, hne12, hpair⟩ :
      ∃ k₁ k₂ : Fin (d + 1),
        f k₁ = c₀ ∧ f k₂ = c₀ ∧ k₁ ≠ k₂ ∧
        univ.filter
          (fun i : Fin (d + 1) => f i = c₀) =
          {k₁, k₂} := by
    rw [Finset.card_eq_two] at hc₀_eq
    obtain ⟨a, b, hab, habset⟩ := hc₀_eq
    have ha := (mem_filter.mp
      (habset ▸ mem_insert_self a {b})).2
    have hb := (mem_filter.mp
      (habset ▸ mem_insert.mpr
        (Or.inr (mem_singleton.mpr rfl)))).2
    exact ⟨a, b, ha, hb, hab, habset⟩
  suffices hset : univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d,
        ∃ i : Fin (d + 1), i ≠ k ∧ f i = j) =
      {k₁, k₂} by
    rw [hset, card_pair hne12]; exact even_two
  ext k
  simp only [mem_filter, mem_univ, true_and,
    mem_insert, mem_singleton]
  constructor
  · intro hk
    obtain ⟨i, hi_ne, hi_eq⟩ := hk (f k)
    have hfk : f k = c₀ := by
      by_contra hne
      have hmult1 := hc₀_rest (f k) hne
      rw [Finset.card_eq_one] at hmult1
      obtain ⟨a, ha⟩ := hmult1
      have hk_in : k ∈ univ.filter
          (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ _, rfl⟩
      have hi_in : i ∈ univ.filter
          (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ i, hi_eq⟩
      rw [ha] at hk_in hi_in
      rw [Finset.mem_singleton] at hk_in hi_in
      exact hi_ne (hk_in ▸ hi_in)
    have hk_mem : k ∈ univ.filter
        (fun i : Fin (d + 1) => f i = c₀) :=
      mem_filter.mpr ⟨mem_univ k, hfk⟩
    rw [hpair] at hk_mem
    rw [mem_insert, mem_singleton] at hk_mem
    exact hk_mem
  · intro hk j
    obtain ⟨i₀, hi₀⟩ := hcov j
    by_cases hik : i₀ = k
    · rcases hk with heq | heq
      · have hfk : f k = c₀ := heq ▸ hk₁
        have hj_c0 : j = c₀ := by
          rw [← hi₀, hik, hfk]
        exact ⟨k₂, (heq ▸ hne12).symm,
          by rw [hj_c0, hk₂]⟩
      · have hfk : f k = c₀ := heq ▸ hk₂
        have hj_c0 : j = c₀ := by
          rw [← hi₀, hik, hfk]
        exact ⟨k₁, heq ▸ hne12,
          by rw [hj_c0, hk₁]⟩
    · exact ⟨i₀, hik, hi₀⟩

/-- A bijection `Fin (d+1) → Fin (d+1)` has exactly one door
position: the unique preimage of the top color `d`. -/
private lemma door_count_of_surj (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (hsurj : Function.Surjective f) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card = 1 := by
  have hinj :=
    Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨k₀, hk₀⟩ := hsurj ⟨d, by omega⟩
  have huniq : ∀ k, f k = ⟨d, by omega⟩ → k = k₀ :=
    fun k hk => hinj (hk.trans hk₀.symm)
  suffices hset : univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
          f i = ⟨j.val, by omega⟩) = {k₀} by
    rw [hset, card_singleton]
  ext k
  simp only [mem_filter, mem_univ, true_and,
    mem_singleton]
  constructor
  · intro hk; by_contra hne
    have hfk_ne : f k ≠ ⟨d, by omega⟩ :=
      fun h => hne (huniq k h)
    have hfk_val_ne : (f k).val ≠ d :=
      fun h => hfk_ne (Fin.ext h)
    have hfk_lt : (f k).val < d := by
      have := (f k).isLt; omega
    obtain ⟨i, hi_ne, hi_eq⟩ :=
      hk ⟨(f k).val, hfk_lt⟩
    have hval : f i = f k :=
      Fin.ext (Fin.ext_iff.mp hi_eq)
    exact hi_ne (hinj hval)
  · intro hk; subst hk; intro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hsurj ⟨j, by omega⟩
    exact ⟨i,
      fun hik => by
        subst hik; rw [hk₀] at hi
        simp only [Fin.mk.injEq] at hi; omega,
      by rw [hi]⟩

/-- A non-surjection `Fin (d+1) → Fin (d+1)` has an even
number of door positions (0 if a lower color is missing,
or paired via the duplicated fiber if no top color appears
but the truncation is surjective). -/
private lemma door_count_even_of_not_surj (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (hnsurj : ¬Function.Surjective f) :
    Even (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card := by
  by_cases hd_app : ∃ i, f i = ⟨d, by omega⟩
  · -- Top color d has a preimage but f is not surjective,
    -- so some lower color j₀ is missing. No doors.
    have ⟨j₀, hj₀⟩ : ∃ j : Fin d,
        ¬∃ i, f i =
          ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
      by_contra hall; push_neg at hall; apply hnsurj
      intro ⟨y, hy⟩; by_cases hyd : y = d
      · subst hyd; exact hd_app
      · exact hall ⟨y, by omega⟩
    rw [Finset.card_eq_zero.mpr
      (door_filter_empty_of_missing_color d f j₀ hj₀)]
    exact ⟨0, by omega⟩
  · -- Top color d never appears. Truncate to
    -- g : Fin (d+1) → Fin d.
    push_neg at hd_app
    have hlt : ∀ i, (f i).val < d := by
      intro i; have := (f i).isLt
      by_contra h; push_neg at h
      have hlt2 := (f i).isLt
      have : (f i).val = d := by omega
      exact hd_app i (Fin.ext this)
    let g : Fin (d + 1) → Fin d :=
      fun i => ⟨(f i).val, hlt i⟩
    by_cases hgsurj : Function.Surjective g
    · -- g surjective: doors pair via the duplicated fiber.
      have heven :=
        even_card_doors_of_surjective d g hgsurj
      suffices heq : univ.filter
          (fun k : Fin (d + 1) =>
            ∀ j : Fin d,
              ∃ i : Fin (d + 1), i ≠ k ∧
                f i = ⟨j.val, by omega⟩) =
          univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d,
              ∃ i : Fin (d + 1),
                i ≠ k ∧ g i = j) by
        rw [heq]; exact heven
      ext k
      simp only [mem_filter, mem_univ, true_and]
      constructor <;> intro h j
      · obtain ⟨i, hi, hfi⟩ := h j
        refine ⟨i, hi, Fin.ext ?_⟩
        change (f i).val = j.val
        exact congr_arg Fin.val hfi
      · obtain ⟨i, hi, hgi⟩ := h j
        refine ⟨i, hi, Fin.ext ?_⟩
        change (f i).val = j.val
        exact congr_arg Fin.val hgi
    · -- g not surjective: some lower color missing. No doors.
      have ⟨j₀, hj₀⟩ :
          ∃ j : Fin d, ¬∃ i, g i = j := by
        by_contra h; push_neg at h; exact hgsurj h
      suffices h0 : (univ.filter
          (fun k : Fin (d + 1) =>
            ∀ j : Fin d,
              ∃ i : Fin (d + 1), i ≠ k ∧
                f i = ⟨j.val, by omega⟩)).card =
          0 by rw [h0]; exact ⟨0, by omega⟩
      rw [Finset.card_eq_zero, filter_eq_empty_iff]
      intro k _; push_neg
      exact ⟨j₀, fun i _ h =>
        hj₀ ⟨i, Fin.ext (show (g i).val = j₀.val by
          change (f i).val = j₀.val
          exact congr_arg Fin.val h)⟩⟩

/-- **Door count parity**: the number of door positions of a
coloring `f : Fin (d+1) → Fin (d+1)` has parity equal to 1
if `f` is surjective (bijective), and 0 otherwise. -/
theorem door_count_parity (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1)) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · rw [if_pos hsurj, door_count_of_surj d f hsurj]
  · rw [if_neg hsurj]
    exact Nat.even_iff.mp
      (door_count_even_of_not_surj d f hsurj)

end DoorCountParity

/-- An abstract cell complex with adjacency, parametrized by
vertex type `V` and dimension `d`. Each cell has `d + 1`
vertices from `V`. Interior codimension-1 faces pair via
`adj`; boundary faces have `adj = none`. -/
structure CellComplex (V : Type*) [DecidableEq V]
    (d : ℕ) where
  /-- The type of top-dimensional cells. -/
  Cell : Type
  /-- Decidable equality on cells. -/
  cellDecEq : DecidableEq Cell
  /-- Finiteness of cells. -/
  cellFintype : Fintype Cell
  /-- The `d + 1` vertices of each cell. -/
  vertex : Cell → Fin (d + 1) → V
  /-- Adjacency: the face opposite vertex `k` in cell `s`
  is shared with another cell, or is a boundary face. -/
  adj : Cell → Fin (d + 1) →
    Option (Cell × Fin (d + 1))
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') →
    adj s' k' = some (s, k)
  /-- Adjacent cells share the codimension-1 face. -/
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  /-- Adjacent cells are distinct. -/
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] CellComplex.cellDecEq
attribute [instance] CellComplex.cellFintype

namespace CellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A cell is *panchromatic* (fully colored): the coloring
restricted to its vertices is surjective onto `Fin (d+1)`. -/
def IsPanchromatic (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell) : Prop :=
  Function.Surjective (c ∘ K.vertex s)

/-- A facet `(s, k)` is a *door*: removing vertex `k`, the
remaining `d` vertices carry all colors `{0, ..., d-1}`. -/
def IsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1),
    i ≠ k ∧ c (K.vertex s i) = Fin.castSucc j

instance decidableIsPanchromatic
    (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) :
    Decidable (IsPanchromatic c K s) := by
  unfold IsPanchromatic Function.Surjective
  exact inferInstance

instance decidableIsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) :
    Decidable (IsDoor c K s k) := by
  unfold IsDoor; exact inferInstance

/-- The adjacency map: sends `(s, k)` to its adjacent
cell-face pair, or to itself if on the boundary. -/
private def adjMap (K : CellComplex V d)
    (p : K.Cell × Fin (d + 1)) :
    K.Cell × Fin (d + 1) :=
  match K.adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p

/-- A door transfers through a shared face (one direction). -/
private lemma isDoor_of_shared_face
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Cell} {k : Fin (d + 1)}
    {s' : K.Cell} {k' : Fin (d + 1)}
    (hvert :
      (univ.erase k).image (K.vertex s) =
      (univ.erase k').image (K.vertex s'))
    (h : IsDoor c K s k) : IsDoor c K s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : K.vertex s i ∈
      (univ.erase k').image (K.vertex s') := by
    rw [← hvert]
    exact mem_image.mpr
      ⟨i, mem_erase.mpr ⟨hi_ne, mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := mem_image.mp hmem
  exact ⟨i', (mem_erase.mp hi'_mem).1,
    by rw [hi'_eq]; exact hi_eq⟩

/-- A door transfers through adjacency (iff version). -/
private lemma isDoor_iff_of_adj
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Cell} {k : Fin (d + 1)}
    {s' : K.Cell} {k' : Fin (d + 1)}
    (hadj : K.adj s k = some (s', k')) :
    IsDoor c K s k ↔ IsDoor c K s' k' :=
  ⟨isDoor_of_shared_face
    (K.adj_vertex s k s' k' hadj),
   isDoor_of_shared_face
    (K.adj_vertex s k s' k' hadj).symm⟩

/-- Interior doors pair up via the adjacency involution,
so their count is even. -/
theorem even_card_interiorDoors
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    Even (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 ≠ none)).card := by
  set S := univ.filter
    (fun p : K.Cell × Fin (d + 1) =>
      IsDoor c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)
  apply Finset.even_card_of_fpf_invol S (adjMap K)
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back :=
        K.adj_symm p.1 p.2 s' k' hadj_eq
      change adjMap K (adjMap K p) = p
      simp only [adjMap, hadj_eq, hadj_back]
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back :=
        K.adj_symm p.1 p.2 s' k' hadj_eq
      change IsDoor c K (adjMap K p).1
          (adjMap K p).2 ∧
        K.adj (adjMap K p).1 (adjMap K p).2 ≠ none
      simp only [adjMap, hadj_eq]
      exact ⟨(isDoor_iff_of_adj hadj_eq).mp hdoor,
        by rw [hadj_back]; exact nofun⟩
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show adjMap K p ≠ p
      simp only [adjMap, hadj_eq]
      intro heq
      exact K.adj_ne p.1 p.2 s' k' hadj_eq
        (congr_arg Prod.fst heq).symm

/-- Per-cell door parity: the door count of a single cell
has the same parity as its panchromaticity indicator. -/
private lemma per_cell_door_parity
    (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) :
    (univ.filter (fun k : Fin (d + 1) =>
      IsDoor c K s k)).card % 2 =
    if IsPanchromatic c K s then 1 else 0 := by
  have h := door_count_parity d (c ∘ K.vertex s)
  have h1 : (univ.filter (fun k : Fin (d + 1) =>
      IsDoor c K s k)) =
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        (c ∘ K.vertex s) i =
          ⟨j.val, by omega⟩)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]; rfl
  rw [h1, h]
  exact if_congr Iff.rfl rfl rfl

private lemma sum_mod_congr {ι : Type*}
    (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, a i % 2 = b i % 2) :
    (∑ i ∈ S, a i) % 2 =
    (∑ i ∈ S, b i) % 2 := by
  induction S using Finset.cons_induction with
  | empty => rfl
  | cons x s hx ih =>
    rw [sum_cons, sum_cons]
    have hx_eq :=
      h x (mem_cons_self x s)
    have hs_eq := ih
      (fun i hi => h i (mem_cons.mpr (Or.inr hi)))
    omega

private lemma card_doors_eq_sum
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    ∑ s : K.Cell, (univ.filter
      (fun k : Fin (d + 1) =>
        IsDoor c K s k)).card := by
  have hlhs : (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    ∑ p : K.Cell × Fin (d + 1),
      if IsDoor c K p.1 p.2 then 1 else 0 := by
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  have hrhs : ∀ s : K.Cell,
      (univ.filter (fun k : Fin (d + 1) =>
        IsDoor c K s k)).card =
      ∑ k : Fin (d + 1),
        if IsDoor c K s k then 1 else 0 := by
    intro s
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  rw [hlhs, sum_congr rfl (fun s _ => hrhs s)]
  rw [← Fintype.sum_prod_type']

private lemma doors_partition
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 ≠ none)).card +
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext p
    simp only [mem_filter, mem_univ, true_and,
      mem_union]
    constructor
    · intro h
      by_cases hadj : K.adj p.1 p.2 = none
      · right; exact ⟨h, hadj⟩
      · left; exact ⟨h, hadj⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [disjoint_left]
    intro p h₁ h₂
    simp only [mem_filter, mem_univ,
      true_and] at h₁ h₂
    exact h₁.2 h₂.2

/-- **Sperner Parity Theorem**: the panchromatic cell count
is congruent mod 2 to the boundary door count. -/
theorem sperner_parity (c : V → Fin (d + 1))
    (K : CellComplex V d) :
    (univ.filter (fun s : K.Cell =>
      IsPanchromatic c K s)).card % 2 =
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card % 2 := by
  have hper := per_cell_door_parity c K
  have hsum :
      (∑ s : K.Cell, (univ.filter
        (fun k => IsDoor c K s k)).card) % 2 =
      (∑ s : K.Cell,
        if IsPanchromatic c K s
        then 1 else 0) % 2 :=
    sum_mod_congr univ _ _ (fun s _ => by
      rw [hper s]
      split_ifs <;> omega)
  have hfc_sum :
      (∑ s : K.Cell,
        if IsPanchromatic c K s
        then (1 : ℕ) else 0) =
      (univ.filter
        (fun s => IsPanchromatic c K s)).card := by
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  have hdoor_sum := card_doors_eq_sum c K
  have hpart := doors_partition c K
  have heven := even_card_interiorDoors c K
  obtain ⟨m, hm⟩ := heven
  calc (univ.filter
      (fun s => IsPanchromatic c K s)).card % 2
    _ = (∑ s : K.Cell,
        if IsPanchromatic c K s
        then 1 else 0) % 2 := by rw [hfc_sum]
    _ = (∑ s : K.Cell, (univ.filter
        (fun k => IsDoor c K s k)).card) % 2 :=
      hsum.symm
    _ = (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2)).card % 2 := by
      rw [hdoor_sum]
    _ = ((univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 ≠ none)).card +
       (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 = none)).card) % 2 := by
      rw [hpart]
    _ = (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 = none)).card % 2 := by
      rw [hm, Nat.add_mod,
        show (m + m) % 2 = 0 from by omega,
        Nat.zero_add, Nat.mod_mod_of_dvd]
      exact ⟨1, rfl⟩

/-- **Sperner's Lemma**: if boundary doors are odd, a
panchromatic cell exists. -/
theorem sperner (c : V → Fin (d + 1))
    (K : CellComplex V d)
    (hbdry : Odd (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card) :
    ∃ s : K.Cell, IsPanchromatic c K s := by
  have hparity := sperner_parity c K
  have hodd : Odd (univ.filter
      (fun s : K.Cell =>
        IsPanchromatic c K s)).card := by
    rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
  have hpos : 0 < (univ.filter
      (fun s => IsPanchromatic c K s)).card := by
    obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (mem_filter.mp hs).2⟩

end CellComplex
