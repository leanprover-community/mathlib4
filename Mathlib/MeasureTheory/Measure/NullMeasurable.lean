/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.null_measurable
! leanprover-community/mathlib commit e4edb23029fff178210b9945dcb77d293f001e1c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.AeDisjoint

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : set α` is called *null measurable* (`measure_theory.null_measurable_set`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `measure_theory.to_measurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `measurable_space` instance on
`measure_theory.null_measurable_space α μ`. We also say that `f : α → β` is
`measure_theory.null_measurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`measure_theory.null_measurable_space α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `measurable_space α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `measure_theory.measure.completion μ` to be the same measure
interpreted as a measure on `measure_theory.null_measurable_space α μ` and prove that this is a
complete measure.

## Implementation notes

We define `measure_theory.null_measurable_set` as `@measurable_set (null_measurable_space α μ) _` so
that theorems about `measurable_set`s like `measurable_set.union` can be applied to
`null_measurable_set`s. However, these lemmas output terms of the same form
`@measurable_set (null_measurable_space α μ) _ _`. While this is definitionally equal to the
expected output `null_measurable_set s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `measure_theory.null_measurable_set` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/


open Filter Set Encodable

variable {ι α β γ : Type _}

namespace MeasureTheory

/-- A type tag for `α` with `measurable_set` given by `null_measurable_set`. -/
@[nolint unused_arguments]
def NullMeasurableSpace (α : Type _) [MeasurableSpace α]
    (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Type _ :=
  α
#align measure_theory.null_measurable_space MeasureTheory.NullMeasurableSpace

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

instance [h : Inhabited α] : Inhabited (NullMeasurableSpace α μ) :=
  h

instance [h : Subsingleton α] : Subsingleton (NullMeasurableSpace α μ) :=
  h

instance : MeasurableSpace (NullMeasurableSpace α μ) where
  MeasurableSet' s := ∃ t, MeasurableSet t ∧ s =ᵐ[μ] t
  measurable_set_empty := ⟨∅, MeasurableSet.empty, ae_eq_refl _⟩
  measurable_set_compl := fun s ⟨t, htm, hts⟩ => ⟨tᶜ, htm.compl, hts.compl⟩
  measurable_set_unionᵢ s hs := by
    choose t htm hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.unionᵢ htm, EventuallyEq.countable_unionᵢ hts⟩

/-- A set is called `null_measurable_set` if it can be approximated by a measurable set up to
a set of null measure. -/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s
#align measure_theory.null_measurable_set MeasureTheory.NullMeasurableSet

@[simp]
theorem MeasurableSet.nullMeasurableSet (h : MeasurableSet s) : NullMeasurableSet s μ :=
  ⟨s, h, ae_eq_refl _⟩
#align measurable_set.null_measurable_set MeasurableSet.nullMeasurableSet

@[simp]
theorem nullMeasurableSetEmpty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty
#align measure_theory.null_measurable_set_empty MeasureTheory.nullMeasurableSetEmpty

@[simp]
theorem nullMeasurableSetUniv : NullMeasurableSet univ μ :=
  MeasurableSet.univ
#align measure_theory.null_measurable_set_univ MeasureTheory.nullMeasurableSetUniv

namespace NullMeasurableSet

theorem ofNull (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩
#align measure_theory.null_measurable_set.of_null MeasureTheory.NullMeasurableSet.ofNull

theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet (sᶜ) μ :=
  h.compl
#align measure_theory.null_measurable_set.compl MeasureTheory.NullMeasurableSet.compl

theorem ofCompl (h : NullMeasurableSet (sᶜ) μ) : NullMeasurableSet s μ :=
  h.ofCompl
#align measure_theory.null_measurable_set.of_compl MeasureTheory.NullMeasurableSet.ofCompl

@[simp]
theorem compl_iff : NullMeasurableSet (sᶜ) μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff
#align measure_theory.null_measurable_set.compl_iff MeasureTheory.NullMeasurableSet.compl_iff

@[nontriviality]
theorem ofSubsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurableSet
#align measure_theory.null_measurable_set.of_subsingleton MeasureTheory.NullMeasurableSet.ofSubsingleton

protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ :=
  let ⟨s', hm, hs'⟩ := hs
  ⟨s', hm, h.symm.trans hs'⟩
#align measure_theory.null_measurable_set.congr MeasureTheory.NullMeasurableSet.congr

protected theorem union {ι : Sort _} [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) : NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.unionᵢ h
#align measure_theory.null_measurable_set.Union MeasureTheory.NullMeasurableSet.union

protected theorem bUnionDecode₂ [Encodable ι] ⦃f : ι → Set α⦄ (h : ∀ i, NullMeasurableSet (f i) μ)
    (n : ℕ) : NullMeasurableSet (⋃ b ∈ Encodable.decode₂ ι n, f b) μ :=
  MeasurableSet.bunionᵢ_decode₂ h n
#align measure_theory.null_measurable_set.bUnion_decode₂ MeasureTheory.NullMeasurableSet.bUnionDecode₂

protected theorem bUnion {f : ι → Set α} {s : Set ι} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  MeasurableSet.bunionᵢ hs h
#align measure_theory.null_measurable_set.bUnion MeasureTheory.NullMeasurableSet.bUnion

protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀ s) μ := by
  rw [sUnion_eq_bUnion]
  exact MeasurableSet.bunionᵢ hs h
#align measure_theory.null_measurable_set.sUnion MeasureTheory.NullMeasurableSet.sUnion

protected theorem inter {ι : Sort _} [Countable ι] {f : ι → Set α}
    (h : ∀ i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.interᵢ h
#align measure_theory.null_measurable_set.Inter MeasureTheory.NullMeasurableSet.inter

protected theorem bInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  MeasurableSet.binterᵢ hs h
#align measure_theory.null_measurable_set.bInter MeasureTheory.NullMeasurableSet.bInter

protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.interₛ hs h
#align measure_theory.null_measurable_set.sInter MeasureTheory.NullMeasurableSet.sInter

/- warning: measure_theory.null_measurable_set.union clashes with measure_theory.null_measurable_set.Union -> MeasureTheory.NullMeasurableSet.union
warning: measure_theory.null_measurable_set.union -> MeasureTheory.NullMeasurableSet.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {m0 : MeasurableSpace.{u_2} α} {μ : MeasureTheory.Measure.{u_2} α m0} {s : Set.{u_2} α} {t : Set.{u_2} α}, (MeasureTheory.NullMeasurableSet.{u_2} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u_2} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u_2} α m0 (Union.union.{u_2} (Set.{u_2} α) (Set.hasUnion.{u_2} α) s t) μ)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.union MeasureTheory.NullMeasurableSet.unionₓ'. -/
@[simp]
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union ht
#align measure_theory.null_measurable_set.union MeasureTheory.NullMeasurableSet.union

protected theorem unionNull (hs : NullMeasurableSet s μ) (ht : μ t = 0) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union (ofNull ht)
#align measure_theory.null_measurable_set.union_null MeasureTheory.NullMeasurableSet.unionNull

/- warning: measure_theory.null_measurable_set.inter clashes with measure_theory.null_measurable_set.Inter -> MeasureTheory.NullMeasurableSet.inter
warning: measure_theory.null_measurable_set.inter -> MeasureTheory.NullMeasurableSet.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_2}} {m0 : MeasurableSpace.{u_2} α} {μ : MeasureTheory.Measure.{u_2} α m0} {s : Set.{u_2} α} {t : Set.{u_2} α}, (MeasureTheory.NullMeasurableSet.{u_2} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u_2} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u_2} α m0 (Inter.inter.{u_2} (Set.{u_2} α) (Set.hasInter.{u_2} α) s t) μ)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.inter MeasureTheory.NullMeasurableSet.interₓ'. -/
@[simp]
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∩ t) μ :=
  hs.inter ht
#align measure_theory.null_measurable_set.inter MeasureTheory.NullMeasurableSet.inter

@[simp]
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s \ t) μ :=
  hs.diffₓ ht
#align measure_theory.null_measurable_set.diff MeasureTheory.NullMeasurableSet.diff

@[simp]
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n
#align measure_theory.null_measurable_set.disjointed MeasureTheory.NullMeasurableSet.disjointed

@[simp]
protected theorem const (p : Prop) : NullMeasurableSet { a : α | p } μ :=
  MeasurableSet.const p
#align measure_theory.null_measurable_set.const MeasureTheory.NullMeasurableSet.const

instance [MeasurableSingletonClass α] : MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  ⟨fun x => (@measurableSet_singleton α _ _ x).NullMeasurableSet⟩

protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)]
    (hs : NullMeasurableSet s μ) (a : α) : NullMeasurableSet (insert a s) μ :=
  hs.insert a
#align measure_theory.null_measurable_set.insert MeasureTheory.NullMeasurableSet.insert

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊇ » s) -/
theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s := by
  rcases h with ⟨t, htm, hst⟩
  refine' ⟨t ∪ to_measurable μ (s \ t), _, htm.union (measurable_set_to_measurable _ _), _⟩
  · exact diff_subset_iff.1 (subset_to_measurable _ _)
  · have : to_measurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using hst.symm.union this
#align measure_theory.null_measurable_set.exists_measurable_superset_ae_eq MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq

theorem toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s := by
  rw [to_measurable, dif_pos]
  exact h.exists_measurable_superset_ae_eq.some_spec.snd.2
#align measure_theory.null_measurable_set.to_measurable_ae_eq MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq

theorem compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ (sᶜ)ᶜ =ᵐ[μ] s :=
  by simpa only [compl_compl] using h.compl.to_measurable_ae_eq.compl
#align measure_theory.null_measurable_set.compl_to_measurable_compl_ae_eq MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eq

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨toMeasurable μ (sᶜ)ᶜ, compl_subset_comm.2 <| subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, h.compl_toMeasurable_compl_ae_eq⟩
#align measure_theory.null_measurable_set.exists_measurable_subset_ae_eq MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq

end NullMeasurableSet

/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
theorem exists_subordinate_pairwise_disjoint [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AeDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, t i ⊆ s i) ∧
        (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) := by
  choose t ht_sub htm ht_eq using fun i => (h i).exists_measurable_subset_ae_eq
  rcases exists_null_pairwise_disjoint_diff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => (diff_subset _ _).trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (diff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diffₓ (hum i),
      hud.mono fun i j h =>
        h.mono (diff_subset_diff_left (ht_sub i)) (diff_subset_diff_left (ht_sub j))⟩
#align measure_theory.exists_subordinate_pairwise_disjoint MeasureTheory.exists_subordinate_pairwise_disjoint

theorem measure_unionᵢ {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι → Set α}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  by
  rw [measure_eq_extend (MeasurableSet.unionᵢ h),
    extend_Union MeasurableSet.empty _ MeasurableSet.unionᵢ _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_Union
#align measure_theory.measure_Union MeasureTheory.measure_unionᵢ

theorem measure_Union₀ [Countable ι] {f : ι → Set α} (hd : Pairwise (AeDisjoint μ on f))
    (h : ∀ i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) := by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (EventuallyEq.countable_unionᵢ ht_eq)
    _ = ∑' i, μ (t i) := (measure_Union htd htm)
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm
    
#align measure_theory.measure_Union₀ MeasureTheory.measure_Union₀

theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hd : AeDisjoint μ s t) : μ (s ∪ t) = μ s + μ t := by
  rw [union_eq_Union, measure_Union₀, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts[(pairwise_on_bool ae_disjoint.symmetric).2 hd, fun b => Bool.casesOn b ht hs]
#align measure_theory.measure_union₀_aux MeasureTheory.measure_union₀_aux

/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem measure_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∩ t) + μ (s \ t) = μ s := by
  refine' le_antisymm _ _
  · rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
    replace hs'm : null_measurable_set s' μ := hs'm.null_measurable_set
    calc
      μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) :=
        add_le_add (measure_mono <| inter_subset_inter_left _ hsub)
          (measure_mono <| diff_subset_diff_left hsub)
      _ = μ (s' ∩ t ∪ s' \ t) :=
        (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
            (@disjoint_inf_sdiff _ s' t _).AeDisjoint).symm
      _ = μ s' := (congr_arg μ (inter_union_diff _ _))
      _ = μ s := hs'
      
  ·
    calc
      μ s = μ (s ∩ t ∪ s \ t) := by rw [inter_union_diff]
      _ ≤ μ (s ∩ t) + μ (s \ t) := measure_union_le _ _
      
#align measure_theory.measure_inter_add_diff₀ MeasureTheory.measure_inter_add_diff₀

theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]
#align measure_theory.measure_union_add_inter₀ MeasureTheory.measure_union_add_inter₀

theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_comm]
#align measure_theory.measure_union_add_inter₀' MeasureTheory.measure_union_add_inter₀'

theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AeDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [← measure_union_add_inter₀ s ht, hd.eq, add_zero]
#align measure_theory.measure_union₀ MeasureTheory.measure_union₀

theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AeDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [union_comm, measure_union₀ hs hd.symm, add_comm]
#align measure_theory.measure_union₀' MeasureTheory.measure_union₀'

theorem measure_add_measure_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    μ s + μ (sᶜ) = μ univ := by rw [← measure_union₀' hs ae_disjoint_compl_right, union_compl_self]
#align measure_theory.measure_add_measure_compl₀ MeasureTheory.measure_add_measure_compl₀

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

theorem nullMeasurableSetSingleton (x : α) : NullMeasurableSet {x} μ :=
  measurableSet_singleton x
#align measure_theory.null_measurable_set_singleton MeasureTheory.nullMeasurableSetSingleton

@[simp]
theorem nullMeasurableSet_insert {a : α} {s : Set α} :
    NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurableSet_insert
#align measure_theory.null_measurable_set_insert MeasureTheory.nullMeasurableSet_insert

theorem nullMeasurableSetEq {a : α} : NullMeasurableSet { x | x = a } μ :=
  nullMeasurableSetSingleton a
#align measure_theory.null_measurable_set_eq MeasureTheory.nullMeasurableSetEq

protected theorem Set.Finite.nullMeasurableSet (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurableSet hs
#align set.finite.null_measurable_set Set.Finite.nullMeasurableSet

protected theorem Finset.nullMeasurableSet (s : Finset α) : NullMeasurableSet (↑s) μ :=
  Finset.measurableSet s
#align finset.null_measurable_set Finset.nullMeasurableSet

end MeasurableSingletonClass

theorem Set.Finite.nullMeasurableSetBUnion {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finite.measurableSet_bunionᵢ hs h
#align set.finite.null_measurable_set_bUnion Set.Finite.nullMeasurableSetBUnion

theorem Finset.nullMeasurableSetBUnion {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finset.measurableSet_bunionᵢ s h
#align finset.null_measurable_set_bUnion Finset.nullMeasurableSetBUnion

theorem Set.Finite.nullMeasurableSetSUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀ s) μ :=
  Finite.measurableSet_unionₛ hs h
#align set.finite.null_measurable_set_sUnion Set.Finite.nullMeasurableSetSUnion

theorem Set.Finite.nullMeasurableSetBInter {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  Finite.measurableSet_binterᵢ hs h
#align set.finite.null_measurable_set_bInter Set.Finite.nullMeasurableSetBInter

theorem Finset.nullMeasurableSetBInter {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  s.finite_toSet.nullMeasurableSetBInter h
#align finset.null_measurable_set_bInter Finset.nullMeasurableSetBInter

theorem Set.Finite.nullMeasurableSetSInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter hs.Countable h
#align set.finite.null_measurable_set_sInter Set.Finite.nullMeasurableSetSInter

theorem nullMeasurableSetToMeasurable : NullMeasurableSet (toMeasurable μ s) μ :=
  (measurableSet_toMeasurable _ _).NullMeasurableSet
#align measure_theory.null_measurable_set_to_measurable MeasureTheory.nullMeasurableSetToMeasurable

end

section NullMeasurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measure α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def NullMeasurable (f : α → β) (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) :
    Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ
#align measure_theory.null_measurable MeasureTheory.NullMeasurable

protected theorem Measurable.nullMeasurable (h : Measurable f) : NullMeasurable f μ := fun s hs =>
  (h hs).NullMeasurableSet
#align measurable.null_measurable Measurable.nullMeasurable

protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) :
    @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h
#align measure_theory.null_measurable.measurable' MeasureTheory.NullMeasurable.measurable'

theorem Measurable.compNullMeasurable {g : β → γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ :=
  hg.comp hf
#align measure_theory.measurable.comp_null_measurable MeasureTheory.Measurable.compNullMeasurable

theorem NullMeasurable.congr {g : α → β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) :
    NullMeasurable g μ := fun s hs =>
  (hf hs).congr <| eventuallyEq_set.2 <| hg.mono fun x hx => by rw [mem_preimage, mem_preimage, hx]
#align measure_theory.null_measurable.congr MeasureTheory.NullMeasurable.congr

end NullMeasurable

section IsComplete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : ∀ s, μ s = 0 → MeasurableSet s
#align measure_theory.measure.is_complete MeasureTheory.Measure.IsComplete

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

theorem Measure.isComplete_iff : μ.IsComplete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align measure_theory.measure.is_complete_iff MeasureTheory.Measure.isComplete_iff

theorem Measure.IsComplete.out (h : μ.IsComplete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1
#align measure_theory.measure.is_complete.out MeasureTheory.Measure.IsComplete.out

theorem measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs
#align measure_theory.measurable_set_of_null MeasureTheory.measurableSet_of_null

theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] :
    MeasurableSet s :=
  diff_diff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diffₓ
      (measurableSet_of_null (ae_le_set.1 hs.toMeasurable_ae_eq.le))
#align measure_theory.null_measurable_set.measurable_of_complete MeasureTheory.NullMeasurableSet.measurable_of_complete

theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {m1 : MeasurableSpace β} {f : α → β}
    (hf : NullMeasurable f μ) : Measurable f := fun s hs => (hf hs).measurable_of_complete
#align measure_theory.null_measurable.measurable_of_complete MeasureTheory.NullMeasurable.measurable_of_complete

theorem Measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [hμ : μ.IsComplete] {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  (hf.NullMeasurable.congr hfg).measurable_of_complete
#align measurable.congr_ae Measurable.congr_ae

namespace Measure

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : MeasurableSpace α} (μ : Measure α) :
    @MeasureTheory.Measure (NullMeasurableSpace α μ) _ where
  toOuterMeasure := μ.toOuterMeasure
  m_unionᵢ s hs hd := measure_Union₀ (hd.mono fun i j h => h.AeDisjoint) hs
  trimmed := by
    refine' le_antisymm (fun s => _) (outer_measure.le_trim _)
    rw [outer_measure.trim_eq_infi]; simp only [to_outer_measure_apply]
    refine' (infᵢ₂_mono _).trans_eq (measure_eq_infi _).symm
    exact fun t ht => infᵢ_mono' fun h => ⟨h.NullMeasurableSet, le_rfl⟩
#align measure_theory.measure.completion MeasureTheory.Measure.completion

instance completion.isComplete {m : MeasurableSpace α} (μ : Measure α) : μ.Completion.IsComplete :=
  ⟨fun z hz => NullMeasurableSet.ofNull hz⟩
#align measure_theory.measure.completion.is_complete MeasureTheory.Measure.completion.isComplete

@[simp]
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.Completion = μ :=
  rfl
#align measure_theory.measure.coe_completion MeasureTheory.Measure.coe_completion

theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.Completion s = μ s :=
  rfl
#align measure_theory.measure.completion_apply MeasureTheory.Measure.completion_apply

end Measure

end IsComplete

end MeasureTheory

