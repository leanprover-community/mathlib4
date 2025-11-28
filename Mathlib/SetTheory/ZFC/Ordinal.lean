/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.GameAdd
public import Mathlib.Order.RelIso.Set
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`. We show multiple
  equivalences to this definition.
- `Ordinal.toZFSet` converts Lean's type-theoretic ordinals into ZFC ordinals. We prove that these
  two notions are order-isomorphic.
-/

@[expose] public section

universe u

variable {x y z w : ZFSet.{u}}

open Set

namespace ZFSet

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset.

This is equivalent to being an infinite-open interval in the transitive closure of membership. -/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
theorem isTransitive_empty : IsTransitive ∅ := fun y hy => (notMem_empty y hy).elim

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x := h y

theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

/-- The union of a transitive set is transitive. -/
protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

/-- The union of transitive sets is transitive. -/
theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

protected theorem IsTransitive.iUnion {α : Type*} [Small.{u} α] {f : α → ZFSet.{u}}
    (hf : ∀ i, (f i).IsTransitive) : (⋃ i, f i).IsTransitive :=
  sUnion' (by simpa)

protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)

theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x := by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
  · exact fun z hz ↦ h <| mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h _ hy => mem_powerset.2 <| h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

/-! ### Ordinals -/

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`. We
prove that this further implies that `x` is well-ordered under `∈` in `isOrdinal_iff_isWellOrder`.

The transitivity condition `a ∈ b → b ∈ c → a ∈ c` can be written without assuming `a ∈ x` and
`b ∈ x`. The lemma `isOrdinal_iff_isTrans` shows this condition is equivalent to the usual one. -/
structure IsOrdinal (x : ZFSet) : Prop where
  /-- An ordinal is a transitive set. -/
  isTransitive : x.IsTransitive
  /-- The membership operation within an ordinal is transitive. -/
  mem_trans' {y z w : ZFSet} : y ∈ z → z ∈ w → w ∈ x → y ∈ w

namespace IsOrdinal

theorem subset_of_mem (h : x.IsOrdinal) : y ∈ x → y ⊆ x :=
  h.isTransitive.subset_of_mem

theorem mem_trans (h : z.IsOrdinal) : x ∈ y → y ∈ z → x ∈ z :=
  h.isTransitive.mem_trans

protected theorem isTrans (h : x.IsOrdinal) : IsTrans _ (Subrel (· ∈ ·) (· ∈ x)) :=
  ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩

/-- The simplified form of transitivity used within `IsOrdinal` yields an equivalent definition to
the standard one. -/
theorem _root_.ZFSet.isOrdinal_iff_isTrans :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrans _ (Subrel (· ∈ ·) (· ∈ x)) where
  mp h := ⟨h.isTransitive, h.isTrans⟩
  mpr := by
    rintro ⟨h₁, ⟨h₂⟩⟩
    refine ⟨h₁, fun {y z w} hyz hzw hwx ↦ ?_⟩
    have hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw

protected theorem mem (hx : x.IsOrdinal) (hy : y ∈ x) : y.IsOrdinal :=
  have := hx.isTrans
  let f : _ ↪r Subrel (· ∈ ·) (· ∈ x) := Subrel.inclusionEmbedding (· ∈ ·) (hx.subset_of_mem hy)
  isOrdinal_iff_isTrans.2 ⟨fun _ hz _ ha ↦ hx.mem_trans' ha hz hy, f.isTrans⟩

/-- An ordinal is a transitive set of transitive sets. -/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive :
    x.IsOrdinal ↔ x.IsTransitive ∧ ∀ y ∈ x, y.IsTransitive where
  mp h := ⟨h.isTransitive, fun _ hy ↦ (h.mem hy).isTransitive⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun hyz hzw hwx ↦ (h₂ _ hwx).mem_trans hyz hzw⟩

/-- An ordinal is a transitive set of ordinals. -/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal :
    x.IsOrdinal ↔ x.IsTransitive ∧ ∀ y ∈ x, y.IsOrdinal where
  mp h := ⟨h.isTransitive, fun _ ↦ h.mem⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ isOrdinal_iff_forall_mem_isTransitive.2
    ⟨h₁, fun y hy ↦ (h₂ y hy).isTransitive⟩

theorem subset_iff_eq_or_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ⊆ y ↔ x = y ∨ x ∈ y := by
  constructor
  · revert hx hy
    apply Sym2.GameAdd.induction mem_wf _ x y
    intro x y IH hx hy hxy
    by_cases hyx : y ⊆ x
    · exact Or.inl (subset_antisymm hxy hyx)
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y \ x) (Set.diff_nonempty.2 hyx)
      have hmy : m ∈ y := by simp only [Set.mem_diff, SetLike.mem_coe] at hm; exact hm.1
      have hmx : m ⊆ x := by
        intro z hzm
        by_contra hzx
        exact hm' _ ⟨hy.mem_trans hzm hmy, hzx⟩ hzm
      obtain rfl | H := IH m x (Sym2.GameAdd.fst_snd hmy) (hy.mem hmy) hx hmx
      · exact Or.inr hmy
      · cases Set.notMem_of_mem_diff hm H
  · rintro (rfl | h)
    · rfl
    · exact hy.subset_of_mem h

alias ⟨eq_or_mem_of_subset, _⟩ := subset_iff_eq_or_mem

theorem mem_of_subset_of_mem (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x ⊆ y) (hy : y ∈ z) :
    x ∈ z := by
  obtain rfl | hx := h.eq_or_mem_of_subset (hz.mem hy) hx
  · exact hy
  · exact hz.mem_trans hx hy

theorem notMem_iff_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∉ y ↔ y ⊆ x := by
  refine ⟨?_, fun hxy hyx ↦ mem_irrefl _ (hxy hyx)⟩
  revert hx hy
  apply Sym2.GameAdd.induction mem_wf _ x y
  intro x y IH hx hy hyx z hzy
  by_contra hzx
  exact hyx (mem_of_subset_of_mem hx hy (IH z x (Sym2.GameAdd.fst_snd hzy) (hy.mem hzy) hx hzx) hzy)

@[deprecated (since := "2025-05-23")] alias not_mem_iff_subset := notMem_iff_subset

theorem not_subset_iff_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : ¬ x ⊆ y ↔ y ∈ x := by
  rw [not_iff_comm, notMem_iff_subset hy hx]

theorem mem_or_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∈ y ∨ y ⊆ x := by
  rw [or_iff_not_imp_left, notMem_iff_subset hx hy]
  exact id

theorem subset_total (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ⊆ y ∨ y ⊆ x := by
  obtain h | h := mem_or_subset hx hy
  · exact Or.inl (hy.subset_of_mem h)
  · exact Or.inr h

theorem mem_trichotomous (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∈ y ∨ x = y ∨ y ∈ x := by
  rw [eq_comm, ← subset_iff_eq_or_mem hy hx]
  exact mem_or_subset hx hy

protected theorem isTrichotomous (h : x.IsOrdinal) : IsTrichotomous _ (Subrel (· ∈ ·) (· ∈ x)) :=
  ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ by simpa using mem_trichotomous (h.mem ha) (h.mem hb)⟩

/-- An ordinal is a transitive set, trichotomous under membership. -/
theorem _root_.ZFSet.isOrdinal_iff_isTrichotomous :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrichotomous _ (Subrel (· ∈ ·) (· ∈ x)) where
  mp h := ⟨h.isTransitive, h.isTrichotomous⟩
  mpr := by
    rintro ⟨h₁, h₂⟩
    rw [isOrdinal_iff_isTrans]
    refine ⟨h₁, ⟨@fun y z w hyz hzw ↦ ?_⟩⟩
    obtain hyw | rfl | hwy := trichotomous_of (Subrel (· ∈ ·) (· ∈ x)) y w
    · exact hyw
    · cases asymm hyz hzw
    · cases mem_wf.asymmetric₃ _ _ _ hyz hzw hwy

protected theorem isWellOrder (h : x.IsOrdinal) : IsWellOrder _ (Subrel (· ∈ ·) (· ∈ x)) where
  wf := (Subrel.relEmbedding _ _).wellFounded mem_wf
  trans := h.isTrans.1
  trichotomous := h.isTrichotomous.1

/-- An ordinal is a transitive set, well-ordered under membership. -/
theorem _root_.ZFSet.isOrdinal_iff_isWellOrder : x.IsOrdinal ↔
    x.IsTransitive ∧ IsWellOrder _ (Subrel (· ∈ ·) (· ∈ x)) := by
  use fun h ↦ ⟨h.isTransitive, h.isWellOrder⟩
  rintro ⟨h₁, h₂⟩
  refine isOrdinal_iff_isTrans.2 ⟨h₁, ?_⟩
  infer_instance

theorem rank_lt_iff_mem {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x < rank y ↔ x ∈ y := by
  refine ⟨fun h ↦ ?_, rank_lt_of_mem⟩
  rw [← hy.not_subset_iff_mem hx]
  exact fun h' ↦ (rank_mono h').not_gt h

theorem rank_le_iff_subset {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x ≤ rank y ↔ x ⊆ y := by
  rw [← notMem_iff_subset hy hx, ← rank_lt_iff_mem hy hx, not_lt]

theorem rank_inj {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x = rank y ↔ x = y := by
  rw [le_antisymm_iff, subset_antisymm_iff, rank_le_iff_subset hx hy, rank_le_iff_subset hy hx]

end IsOrdinal

@[simp]
theorem isOrdinal_empty : IsOrdinal ∅ :=
  ⟨isTransitive_empty, fun _ _ H ↦ (notMem_empty _ H).elim⟩

theorem isOrdinal_succ {x : ZFSet} (h : IsOrdinal x) : IsOrdinal (insert x x) := by
  refine ⟨fun y hy ↦ ?_, @fun y z w hyz hzw hw ↦ ?_⟩
  · obtain rfl | hy := mem_insert_iff.1 hy
    on_goal 2 => apply (h.subset_of_mem hy).trans
    all_goals simp_all [subset_def]
  · obtain rfl | hw := mem_insert_iff.1 hw
    exacts [h.mem_trans hyz hzw, h.mem_trans' hyz hzw hw]

end ZFSet

/-! ### Type-theoretic ordinals to von Neumann ordinals -/

namespace Ordinal
open ZFSet

/-- The von Neumann ordinal corresponding to a given `Ordinal`, as a `PSet`.

The elements of `o.toPSet` are all `a.toPSet` with `a < o`. -/
noncomputable def toPSet (o : Ordinal.{u}) : PSet.{u} :=
  ⟨o.toType, fun a ↦ toPSet ((enumIsoToType o).symm a)⟩
termination_by o
decreasing_by exact ((enumIsoToType o).symm a).2

@[simp]
theorem type_toPSet (o : Ordinal) : o.toPSet.Type = o.toType := by
  rw [toPSet]
  rfl

theorem mem_toPSet_iff {o : Ordinal} {x : PSet} : x ∈ o.toPSet ↔ ∃ a < o, x.Equiv a.toPSet := by
  rw [toPSet, PSet.mem_def]
  simpa using ((enumIsoToType o).exists_congr_left (p := fun y ↦ x.Equiv y.1.toPSet)).symm

@[simp]
theorem rank_toPSet (o : Ordinal) : o.toPSet.rank = o := by
  rw [toPSet, PSet.rank]
  conv_rhs => rw [← _root_.iSup_succ o]
  convert (enumIsoToType o).symm.iSup_comp (g := fun x ↦ Order.succ x.1.toPSet.rank)
  rw [rank_toPSet]
termination_by o
decreasing_by rename_i x; exact x.2

/-- The von Neumann ordinal corresponding to a given `Ordinal`, as a `ZFSet`.

The elements of `o.toZFSet` are all `a.toZFSet` with `a < o`. -/
noncomputable def toZFSet (o : Ordinal.{u}) : ZFSet.{u} :=
  .mk o.toPSet

@[simp]
theorem mk_toPSet (o : Ordinal) : .mk o.toPSet = o.toZFSet :=
  rfl

theorem mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x ∈ o.toZFSet ↔ ∃ a < o, a.toZFSet = x := by
  induction x using Quotient.ind
  rw [toZFSet, mk_eq, ZFSet.mk_mem_iff, mem_toPSet_iff]
  congr!
  rw [toZFSet, eq, PSet.Equiv.comm]

@[simp]
theorem rank_toZFSet (o : Ordinal) : o.toZFSet.rank = o :=
  rank_toPSet o

@[simp]
theorem coe_toZFSet {o : Ordinal} : o.toZFSet = toZFSet '' Iio o := by
  ext
  simp [mem_toZFSet_iff]

private theorem toZFSet_mem_toZFSet_of_lt {a b : Ordinal} (h : a < b) :
    a.toZFSet ∈ b.toZFSet := by
  rw [mem_toZFSet_iff]
  exact ⟨a, h, rfl⟩

theorem toZFSet_monotone : Monotone toZFSet := by
  intro a b h x hx
  obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hx
  exact toZFSet_mem_toZFSet_of_lt (hc.trans_le h)

@[simp]
theorem toZFSet_mem_toZFSet_iff {a b : Ordinal} : a.toZFSet ∈ b.toZFSet ↔ a < b := by
  refine ⟨?_, toZFSet_mem_toZFSet_of_lt⟩
  contrapose!
  exact fun h ↦ notMem_of_subset (toZFSet_monotone h)

@[simp]
theorem toZFSet_subset_toZFSet_iff {a b : Ordinal} : a.toZFSet ⊆ b.toZFSet ↔ a ≤ b := by
  refine ⟨?_, fun h ↦ toZFSet_monotone h⟩
  contrapose!
  exact fun h ↦ not_subset_of_mem (toZFSet_mem_toZFSet_of_lt h)

theorem toZFSet_strictMono : StrictMono toZFSet :=
  fun _ _ h ↦ by simpa [ssubset_iff_subset_not_subset] using ⟨h.le, h⟩

theorem toZFSet_injective : Function.Injective toZFSet :=
  toZFSet_strictMono.injective

@[simp]
theorem toZFSet_zero : toZFSet 0 = ∅ := by
  ext; simp [mem_toZFSet_iff]

@[simp]
theorem toZFSet_succ (o : Ordinal) : toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o) := by
  aesop (add simp [mem_toZFSet_iff, le_iff_eq_or_lt])

end Ordinal

namespace ZFSet
open Ordinal

theorem isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.toZFSet := by
  refine ⟨fun x hx y hy ↦ ?_, @fun z y x hz hy hx ↦ ?_⟩
  all_goals
    obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_toZFSet_iff.1 hy
  · exact toZFSet_mem_toZFSet_iff.2 (hb.trans ha)
  · obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hz
    exact toZFSet_mem_toZFSet_iff.2 (hc.trans hb)

theorem IsOrdinal.toZFSet_rank_eq {x : ZFSet} (hx : IsOrdinal x) : x.rank.toZFSet = x :=
  (IsOrdinal.rank_inj (isOrdinal_toZFSet _) hx).1 (rank_toZFSet _)

theorem isOrdinal_iff_mem_range_toZFSet {x : ZFSet.{u}} :
    IsOrdinal x ↔ x ∈ Set.range toZFSet.{u} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← h.toZFSet_rank_eq]
    exact Set.mem_range_self _
  · rintro ⟨a, rfl⟩
    exact isOrdinal_toZFSet a

/-- `Ordinal` is order-equivalent to the type of von Neumann ordinals. -/
@[simps apply symm_apply]
noncomputable def _root_.Ordinal.toZFSetIso : Ordinal ≃o {x // ZFSet.IsOrdinal x} where
  toFun o := ⟨_, isOrdinal_toZFSet o⟩
  invFun x := rank x.1
  left_inv o := rank_toZFSet o
  right_inv := fun ⟨x, hx⟩ ↦ by simpa using hx.toZFSet_rank_eq
  map_rel_iff' {a b} := by simp

end ZFSet
