/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.GameAdd
import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.ZFC.Basic

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`. We show multiple
  equivalences to this definition.

## TODO

- Build correspondences between these set notions and those of the standard `Ordinal` type.
-/

universe u

variable {x y z w : ZFSet.{u}}

namespace ZFSet

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset.

This is equivalent to being an infinite-open interval in the transitive closure of membership. -/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
theorem IsTransitive.empty : IsTransitive ∅ := fun y hy ↦ (notMem_empty y hy).elim

@[deprecated (since := "2025-07-30")] alias isTransitive_empty := IsTransitive.empty

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x := h y

theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

theorem IsTransitive.empty_mem {x : ZFSet} (hx : x.IsTransitive) (hx₀ : x ≠ ∅) : ∅ ∈ x := by
  obtain ⟨y, hy, hxy⟩ := regularity x hx₀
  obtain rfl | ⟨z, hz⟩ := y.eq_empty_or_nonempty
  · exact hy
  · simpa [hxy] using mem_inter.2 ⟨hx _ hy hz, hz⟩

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

protected theorem IsTransitive.sInter {x : ZFSet} (hx : ∀ y ∈ x, IsTransitive y) :
    IsTransitive (⋂₀ x) := by
  obtain rfl | hx₀ := x.eq_empty_or_nonempty
  · simp
  · intro y hy z hz
    rw [mem_sInter hx₀] at hy ⊢
    exact fun w hw ↦ (hx w hw) _ (hy w hw) hz

protected theorem IsTransitive.union {x y : ZFSet} (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  convert IsTransitive.sUnion' (x := {x, y}) _ using 1
  simp_all

protected theorem IsTransitive.inter {x y : ZFSet} (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := by
  convert IsTransitive.sInter (x := {x, y}) _ using 1 <;>
  simp_all

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

@[simp]
protected theorem empty : IsOrdinal ∅ :=
  ⟨.empty, fun _ _ H ↦ (notMem_empty _ H).elim⟩

@[deprecated (since := "2025-07-30")] alias isOrdinal_empty := IsOrdinal.empty

protected theorem sUnion (hx : ∀ y ∈ x, IsOrdinal y) : (⋃₀ x).IsOrdinal := by
  refine ⟨.sUnion' fun y hy ↦ (hx y hy).isTransitive, @fun z a b hza hab hb ↦ ?_⟩
  rw [mem_sUnion] at hb
  obtain ⟨c, hcx, hbc⟩ := hb
  exact (hx c hcx).mem_trans' hza hab hbc

protected theorem sInter (hx : ∀ y ∈ x, IsOrdinal y) : (⋂₀ x).IsOrdinal := by
  obtain rfl | hx₀ := x.eq_empty_or_nonempty
  · simp
  · refine ⟨.sInter fun y hy ↦ (hx y hy).isTransitive, @fun z a b hza hab hb ↦ ?_⟩
    rw [mem_sInter hx₀] at hb
    obtain ⟨c, hc⟩ := hx₀
    exact (hx _ hc).mem_trans' hza hab (hb c hc)

protected theorem union (hx : x.IsTransitive) (hy : y.IsTransitive) : (x ∪ y).IsTransitive := by
  convert IsTransitive.sUnion' (x := {x, y}) _ using 1
  simp_all

protected theorem inter (hx : x.IsTransitive) (hy : y.IsTransitive) : (x ∩ y).IsTransitive := by
  convert IsTransitive.sInter (x := {x, y}) _ using 1 <;>
  simp_all

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
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y.toSet \ x.toSet) (Set.diff_nonempty.2 hyx)
      have hmy : m ∈ y := show m ∈ y.toSet from Set.mem_of_mem_diff hm
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
  intros x y IH hx hy hyx z hzy
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

end IsOrdinal

end ZFSet
