/-
Copyright (c) 2025 Knala Solomon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Knala Solomon
-/
import Mathlib.SetTheory.ZFC.Rank
import Mathlib.SetTheory.Ordinal.Family

/-!
# von Neumann Hierarchy

In this file, we define the von Neumann hierarchy and prove the result that all sets are contained
within it, which follows from regularity. Then, we show that `ZFSet.rank` is consistent with the
traditional definition of the rank of a set as the least ordinal whose stage of the von Neumann
hierarchy contains the set as a subset.

## Main Definition

- `stage`: the stage of the von Neumann hierarchy corresponding to a given `Ordinal` as a `ZFSet` in
  the same universe.

## Main Results

- `stage_mono`: theorem providing that every stage of the hierarchy contains all those below it.
- `in_hierarchy`: theorem guaranteeing that any set is contained within the hierarchy as defined.
- `rank_stage_eq_self`: theorem stating that the rank of an ordinal's stage is the ordinal itself.
- `rank_def`: the main theorem showing that the `ZFSet.rank` is consistent with `stage` as defined.

## Implementation Notes

The first section defining the hierarchy does not depend on the definition and properties of rank
contained in `Mathlib/SetTheory/ZFC/Rank.lean'

## Tags

ordinal, rank, von Neumann hierarchy, von Neumann universe, cumulative hierarchy

-/

universe u

namespace ZFSet

/-! ### Definition of Hierarchy and Basic Properties -/

/-- The stage in the von Neumann hierarchy indexed by a given Ordinal. -/
noncomputable def stage (o : Ordinal.{u}) : ZFSet.{u} :=
  Ordinal.limitRecOn o ∅
    (fun _ x => x.powerset)
    (fun a _ ih =>
      (range (fun (b : ↑(Set.Iio a)) => by
        use ih b ?_
        rw [← Set.mem_Iio]
        exact Subtype.mem b)).sUnion)

/-- The stages of the von Neumann hierarchy are transitive as sets,
meaning that every element of a stage is a subset of it. -/
theorem stage_sub_of_mem {o : Ordinal.{u}} : ∀ {x : ZFSet.{u}}, x ∈ stage o → x ⊆ stage o := by
  induction o using Ordinal.limitRecOn
  <;> simp [stage]
  <;> intro x hxo z (hzx : z ∈ x)
  case succ a ih =>
    show z ∈ (stage a).powerset
    rw [mem_powerset]
    exact ih (hxo hzx)
  case isLimit o olim ih =>
    simp [olim] at hxo ⊢
    obtain ⟨a, ⟨hao : a < o, hxa : x ∈ stage a⟩⟩ := hxo
    show ∃ b < o, z ∈ stage b
    use a
    have : x ⊆ stage a := ih a hao hxa
    exact ⟨hao, this hzx⟩

/-- Higher stages of the von Neumann hierarchy contain lower stages. -/
theorem stage_mono {a b : Ordinal.{u}} (h : a ≤ b) : stage a ⊆ stage b := by
  induction b using Ordinal.induction with | _ b ih
  rw [le_iff_eq_or_lt] at h
  rcases h with heq | hlt
  · rw [heq]
  rcases (Ordinal.zero_or_succ_or_limit b) with hbz | hbs | hbl
  · subst hbz
    have := Ordinal.not_lt_zero a
    contradiction
  · obtain ⟨o, hob⟩ := hbs
    subst hob
    show stage a ⊆ stage (Order.succ o)
    apply stage_sub_of_mem
    conv in stage (Order.succ o) => simp [stage]
    rw [mem_powerset]
    exact ih o (Order.lt_succ o) (Order.le_of_lt_succ hlt)
  · intro x (hx : x ∈ stage a)
    simp [stage, hbl]
    show ∃ o < b, x ∈ stage o
    use Order.succ a
    constructor
    · exact (Ordinal.succ_lt_of_isLimit hbl).mpr hlt
    · simp [stage]
      apply stage_sub_of_mem
      exact hx



/-- The Axiom of Regularity is equivalent to there not existing any sequences of sets such that
each set in the sequence contains the next. This is a proof of the forward direction. --/
lemma no_infinite_chains (f : ℕ → ZFSet.{u}) : ¬∀ n, f (n + 1) ∈ f n := by
  intro hf
  let r := ZFSet.range f
  have hrne : r ≠ ∅ := by
    intro hre
    rw [eq_empty] at hre
    apply hre (f 0)
    rw [mem_range]
    exact Set.mem_range_self 0
  obtain ⟨y, ⟨hyr : y ∈ r, hrye : r ∩ y = ∅⟩⟩ := regularity r hrne
  obtain ⟨n, fny⟩ : ∃ n, f n = y := by
    rw [← Set.mem_range, ← mem_range]
    exact hyr
  rw [eq_empty] at hrye
  specialize hrye (f (n + 1))
  have : f (n + 1) ∈ r ∩ y := by
    rw [mem_inter]
    constructor
    · rw [mem_range]
      exact Set.mem_range_self (n + 1)
    · exact fny ▸ (hf n)
  contradiction

/-- If a property is not always false, then there is a least set for which it is true. -/
lemma exists_least {p : ZFSet.{u} → Prop} (q : ∃ x, p x) : ∃ y, p y ∧ (∀ z ∈ y, ¬ p z) := by
  by_contra h
  push_neg at h
  obtain ⟨x, px⟩ := q
  let α := { z : ZFSet.{u} × ZFSet.{u} // z.1 ∈ z.2 ∧ p z.1 }
  let f_succ : ℕ → α → α := fun n fn =>
    let y := h fn.val.1 fn.property.right;
    Subtype.mk ⟨Classical.choose y, fn.val.1⟩ (by exact Classical.choose_spec y)
  let f (n : ℕ) : α :=
    Nat.recOn n ⟨⟨x, {x}⟩, ⟨(by rw [mem_singleton]), px⟩⟩ f_succ
  let g : ℕ → ZFSet.{u} := fun n => (f n).val.1
  have : ∀ n, g (n + 1) ∈ g n := by
    intro n
    unfold g
    have : (f (n + 1)).val.2 = (f n).val.1 := by conv_lhs => simp [f, f_succ]
    exact this ▸ (f (n + 1)).property.left
  have := no_infinite_chains g
  contradiction

/-- All sets are contained within the von Neumann hierarchy -/
theorem in_hierarchy (x : ZFSet.{u}) : ∃ (o : Ordinal.{u}), x ∈ stage o := by
  revert x
  by_contra h
  push_neg at h
  apply exists_least at h
  push_neg at h
  obtain ⟨x, ⟨hx, xleast⟩⟩ := h
  have f (z : x.toSet) : { o : Ordinal.{u} // (z : ZFSet.{u}) ∈ stage o } := by
    apply Classical.indefiniteDescription
    exact xleast z.val z.property
  let o : Ordinal.{u} := iSup (fun y => (f y).val)
  suffices x ∈ stage (Order.succ o) from hx (Order.succ o) this
  simp [stage]
  intro y (hyx : y ∈ x)
  let fy := f ⟨y, hyx⟩
  apply stage_mono _ fy.property
  unfold fy o
  apply Ordinal.le_iSup (fun z => (f z).val)



/-! ### Theorems about `rank` -/

/-- The stage at the rank of a set contains the set as a subset. -/
theorem sub_stage_rank (x : ZFSet.{u}) : x ⊆ stage x.rank := by
  induction x using ZFSet.inductionOn with | _ x ih
  intro y (hy : y ∈ x)
  have : Order.succ y.rank ≤ x.rank := LT.lt.succ_le (rank_lt_of_mem hy)
  apply stage_mono this
  simp [stage]
  exact ih y hy

/-- The rank of the stage corresponding to an ordinal is the ordinal itself. -/
theorem rank_stage_eq_self (o : Ordinal.{u}) : (stage o).rank = o := by
  induction o using Ordinal.limitRecOn
  case zero =>
    simp [stage, rank_empty]
  case succ o ih =>
    simp [stage, rank_powerset]
    exact ih
  case isLimit o olim ih =>
    rw [eq_iff_le_not_lt]
    constructor
    · let f := fun (a : ↑(Set.Iio o)) => stage ↑a
      calc
        (stage o).rank = (⋃₀ range f).rank                            := by simp [f, stage, olim]
        _              ≤ (range f).rank                               := rank_sUnion_le (range f)
        _              = iSup fun a => Order.succ (f a).rank          := rank_range f
        _              = iSup fun (a : ↑(Set.Iio o)) => Order.succ ↑a := ?_
        _              = o                                            := Ordinal.iSup_succ o
      apply iSup_congr
      intro a
      rw [Order.succ_eq_succ_iff]
      apply ih
      show ↑a < o
      rw [← Set.mem_Iio]
      exact Subtype.mem a
    · show ¬(stage o).rank < o
      intro h
      obtain ⟨a, ⟨hlto : a < o, hgtr : (stage o).rank < a⟩⟩ := (Ordinal.lt_limit olim).mp h
      have : ¬ (stage a).rank ≤ (stage o).rank := by
        apply not_le_of_gt
        rw [ih a hlto]
        exact hgtr
      have : (stage a).rank ≤ (stage o).rank := by
        apply rank_mono
        apply stage_mono
        rw [le_iff_lt_or_eq]
        left
        exact hlto
      contradiction

/-- A set is contained by a stage of the von Neumann hierarchy iff the rank of the stage is greater
than or equal to the rank of the set. -/
theorem sub_stage_iff_rank_le {x : ZFSet.{u}} {o : Ordinal.{u}} : x ⊆ stage o ↔ x.rank ≤ o := by
  constructor <;> intro h
  · exact rank_stage_eq_self o ▸ ZFSet.rank_mono h
  · intro y (hy : y ∈ x)
    apply stage_mono h
    apply sub_stage_rank x
    exact hy

/-- The definition in ZFSet.rank is equivalent to the definition of rank in terms of the von Neumann hierarchy. -/
theorem rank_def {x : ZFSet.{u}} {o : Ordinal.{u}} :
    x.rank = o ↔ (x ⊆ stage o ∧ ∀ o' < o, ¬ x ⊆ stage o') := by
  constructor
  · intro h
    constructor
    · rw [sub_stage_iff_rank_le, le_iff_lt_or_eq]
      right
      exact h
    · intro a (ha : a < o)
      rw [sub_stage_iff_rank_le]
      subst h
      exact not_le_of_gt ha
  · intro ⟨hxo, omin⟩
    rw [eq_iff_le_not_lt]
    constructor
    · rw [← sub_stage_iff_rank_le]
      exact hxo
    · by_contra hlto
      apply omin x.rank hlto
      exact sub_stage_rank x


end ZFSet
