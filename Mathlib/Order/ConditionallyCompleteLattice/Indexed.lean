/-
Copyright (c) 2018 Sébastian Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastian Gouëzel
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete,
rather than complete, lattice. We add a prefix `c` to distinguish them from the versions for
complete lattices, giving names `ciSup_xxx` or `ciInf_xxx`.
-/

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `iSup` and `iInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

@[simp]
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι → α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f) hf, ← range_comp, Function.comp_def]

@[norm_cast]
theorem WithTop.coe_iSup [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp, Function.comp_def]

@[simp]
theorem WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    ⨆ i, f i = ⊥ :=
  WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι → α} (hf : BddAbove (range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithTop.coe_iInf (α := αᵒᵈ) hf

@[norm_cast]
theorem WithBot.coe_iInf [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  WithTop.coe_iSup (α := αᵒᵈ) _ h

end

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {a b : α}

theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H

theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H

theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  isLUB_ciSup_set (α := αᵒᵈ) H Hne

theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)

theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)

theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- The indexed supremum of a function is bounded above by a uniform bound -/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_mem_range])

/-- The indexed supremum of a function is bounded below by the value taken at one point -/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)

theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  ciSup_mono (α := αᵒᵈ) B H

/-- The indexed minimum of a function is bounded below by a uniform lower bound -/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  ciSup_le (α := αᵒᵈ) H

/-- The indexed infimum of a function is bounded above by the value taken at one point -/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  le_ciSup (α := αᵒᵈ) H c

theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  le_ciSup_of_le (α := αᵒᵈ) H c h

theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    ⨅ i : s, f i ≤ f c :=
  le_ciSup_set (α := αᵒᵈ) H hc

lemma ciInf_le_ciSup [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (ciInf_le hf (Classical.arbitrary _)).trans <| le_ciSup hf' (Classical.arbitrary _)

@[simp]
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup, range_const, csSup_singleton]

@[simp]
theorem ciInf_const [Nonempty ι] {a : α} : ⨅ _ : ι, a = a :=
  ciSup_const (α := αᵒᵈ)

@[simp]
theorem ciSup_unique [Unique ι] {s : ι → α} : ⨆ i, s i = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[simp]
theorem ciInf_unique [Unique ι] {s : ι → α} : ⨅ i, s i = s default :=
  ciSup_unique (α := αᵒᵈ)

theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

theorem ciInf_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨅ i, s i = s i :=
  @ciInf_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp := by
  simp [hp]

theorem ciInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp := by
  simp [hp]

lemma ciSup_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

lemma ciInf_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨅ (h : p), f h = sInf (∅ : Set α) :=
  ciSup_neg (α := αᵒᵈ) hp

lemma ciSup_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨆ h : p, f h) = if h : p then f h else sSup (∅ : Set α) := by
  by_cases H : p <;> simp [ciSup_neg, H]

lemma ciInf_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨅ h : p, f h) = if h : p then f h else sInf (∅ : Set α) :=
  ciSup_eq_ite (α := αᵒᵈ)

theorem cbiSup_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f := by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

theorem cbiInf_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f :=
  cbiSup_eq_of_forall (α := αᵒᵈ) hp

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : ⨅ i : ι, f i = b :=
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂

/-- **Nested intervals lemma**: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine mem_iInter.2 fun n => ?_
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_ciSup ⟨g <| n, forall_mem_range.2 this⟩ _, ciSup_le this⟩

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem ciSup_mem_iInter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

lemma Set.Iic_ciInf [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) :
    Iic (⨅ i, f i) = ⋂ i, Iic (f i) := by
  apply Subset.antisymm
  · rintro x hx - ⟨i, rfl⟩
    exact hx.trans (ciInf_le hf _)
  · rintro x hx
    apply le_ciInf
    simpa using hx

lemma Set.Ici_ciSup [Nonempty ι] {f : ι → α} (hf : BddAbove (range f)) :
    Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  Iic_ciInf (α := αᵒᵈ) hf

theorem ciSup_Iic [Preorder β] {f : β → α} (a : β) (hf : Monotone f) :
    ⨆ x : Iic a, f x = f a := by
  have H : BddAbove (range fun x : Iic a ↦ f x) := ⟨f a, fun _ ↦ by aesop⟩
  apply (le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

theorem ciInf_Ici [Preorder β] {f : β → α} (a : β) (hf : Monotone f) :
    ⨅ x : Ici a, f x = f a := by
  have H : BddBelow (range fun x : Ici a ↦ f x) := ⟨f a, fun _ ↦ by aesop⟩
  apply (ciInf_le H (⟨a, le_refl a⟩ : Ici a)).antisymm
  rw [le_ciInf_iff H]
  rintro ⟨a, h⟩
  exact hf h

theorem ciSup_subtype [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : Subtype p → α}
    (hf : BddAbove (Set.range f)) (hf' : sSup ∅ ≤ iSup f) :
    iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ := by
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩) i := by simp [h]
    rw [this]
    refine le_ciSup (f := (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩)) ?_ i
    simp_rw [ciSup_eq_ite]
    refine (hf.union (bddAbove_singleton (a := sSup ∅))).mono ?_
    intro
    simp only [Set.mem_range, Set.union_singleton, Set.mem_insert_iff, Subtype.exists,
      forall_exists_index]
    intro b hb
    split_ifs at hb
    · exact Or.inr ⟨_, _, hb⟩
    · simp_all
  · refine ciSup_le fun i ↦ ?_
    simp_rw [ciSup_eq_ite]
    split_ifs
    · exact le_ciSup hf ?_
    · exact hf'

theorem ciInf_subtype [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : Subtype p → α}
    (hf : BddBelow (Set.range f)) (hf' : iInf f ≤ sInf ∅) :
    iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  ciSup_subtype (α := αᵒᵈ) hf hf'

theorem ciSup_subtype' [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : ∀ i, p i → α}
    (hf : BddAbove (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : sSup ∅ ≤ ⨆ (i : Subtype p), f i i.prop) :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

theorem ciInf_subtype' [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : ∀ i, p i → α}
    (hf : BddBelow (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : ⨅ (i : Subtype p), f i i.prop ≤ sInf ∅) :
    ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property :=
  (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

theorem ciSup_subtype'' {ι} [Nonempty ι] {s : Set ι} (hs : s.Nonempty) {f : ι → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  haveI : Nonempty s := Set.Nonempty.to_subtype hs
  ciSup_subtype hf hf'

theorem ciInf_subtype'' {ι} [Nonempty ι] {s : Set ι} (hs : s.Nonempty) {f : ι → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  haveI : Nonempty s := Set.Nonempty.to_subtype hs
  ciInf_subtype hf hf'

theorem csSup_image [Nonempty β] {s : Set β} (hs : s.Nonempty) {f : β → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← ciSup_subtype'' hs hf hf', iSup, Set.image_eq_range]

theorem csInf_image [Nonempty β] {s : Set β} (hs : s.Nonempty) {f : β → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    sInf (f '' s) = ⨅ a ∈ s, f a :=
  csSup_image (α := αᵒᵈ) hs hf hf'

lemma ciSup_image {α ι ι' : Type*} [ConditionallyCompleteLattice α] [Nonempty ι] [Nonempty ι']
    {s : Set ι} (hs : s.Nonempty) {f : ι → ι'} {g : ι' → α}
    (hf : BddAbove (Set.range fun i : s ↦ g (f i))) (hg' : sSup ∅ ≤ ⨆ i : s, g (f i)) :
    ⨆ i ∈ (f '' s), g i = ⨆ x ∈ s, g (f x) := by
  have hg : BddAbove (Set.range fun i : f '' s ↦ g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ ≤ ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.Nonempty.to_subtype hs
    refine ciSup_le ?_
    intro ⟨i, h⟩
    obtain ⟨t, ht⟩ : ∃ t : f '' s, g t = g (f (Subtype.mk i h)) := by
      have : f i ∈ f '' s := Set.mem_image_of_mem _ h
      exact ⟨⟨f i, this⟩, by simp⟩
    rw [← ht]
    refine le_ciSup_set ?_ t.prop
    simpa [bddAbove_def] using hf
  rw [← csSup_image (by simpa using hs) hg hf', ← csSup_image hs hf hg', ← Set.image_comp, comp_def]

lemma ciInf_image {α ι ι' : Type*} [ConditionallyCompleteLattice α] [Nonempty ι] [Nonempty ι']
    {s : Set ι} (hs : s.Nonempty) {f : ι → ι'} {g : ι' → α}
    (hf : BddBelow (Set.range fun i : s ↦ g (f i))) (hg' : ⨅ i : s, g (f i) ≤ sInf ∅) :
    ⨅ i ∈ (f '' s), g i = ⨅ x ∈ s, g (f x) :=
  ciSup_image (α := αᵒᵈ) hs hf hg'

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {a b : α}

/-- Indexed version of `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

/-- Indexed version of `exists_lt_of_csInf_lt`.
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  exists_lt_of_lt_ciSup (α := αᵒᵈ) h

theorem lt_ciSup_iff [Nonempty ι] {f : ι → α} (hb : BddAbove (range f)) :
    a < iSup f ↔ ∃ i, a < f i := by
  simpa only [mem_range, exists_exists_eq_and] using lt_csSup_iff hb (range_nonempty _)

theorem ciInf_lt_iff [Nonempty ι] {f : ι → α} (hb : BddBelow (range f)) :
    iInf f < a ↔ ∃ i, f i < a := by
  simpa only [mem_range, exists_exists_eq_and] using csInf_lt_iff hb (range_nonempty _)

theorem cbiSup_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅ := by
  classical
  rcases not_forall.1 hp with ⟨i₀, hi₀⟩
  have : Nonempty ι := ⟨i₀⟩
  simp only [ciSup_eq_ite]
  by_cases H : BddAbove (range f)
  · have B : BddAbove (range fun i ↦ if h : p i then f ⟨i, h⟩ else sSup ∅) := by
      rcases H with ⟨c, hc⟩
      refine ⟨c ⊔ sSup ∅, ?_⟩
      rintro - ⟨i, rfl⟩
      by_cases hi : p i
      · simp only [hi, dite_true, le_sup_iff, hc (mem_range_self _), true_or]
      · simp only [hi, dite_false, le_sup_right]
    apply le_antisymm
    · apply ciSup_le (fun i ↦ ?_)
      by_cases hi : p i
      · simp only [hi, dite_true, le_sup_iff]
        left
        exact le_ciSup H _
      · simp [hi]
    · apply sup_le
      · rcases isEmpty_or_nonempty (Subtype p) with hp | hp
        · rw [iSup_of_empty']
          convert le_ciSup B i₀
          simp [hi₀]
        · apply ciSup_le
          rintro ⟨i, hi⟩
          convert le_ciSup B i
          simp [hi]
      · convert le_ciSup B i₀
        simp [hi₀]
  · have : iSup f = sSup (∅ : Set α) := csSup_of_not_bddAbove H
    simp only [this, le_refl, sup_of_le_left]
    apply csSup_of_not_bddAbove
    contrapose! H
    apply H.mono
    rintro - ⟨i, rfl⟩
    convert mem_range_self i.1
    simp [i.2]

theorem cbiInf_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅ :=
  cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

theorem ciInf_eq_bot_of_bot_mem [OrderBot α] {f : ι → α} (hs : ⊥ ∈ range f) : iInf f = ⊥ :=
  csInf_eq_bot_of_bot_mem hs

theorem ciInf_eq_top_of_top_mem [OrderTop α] {f : ι → α} (hs : ⊤ ∈ range f) : iSup f = ⊤ :=
  csSup_eq_top_of_top_mem hs

variable [WellFoundedLT α]

theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {a : α}

@[simp]
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty', csSup_empty]

theorem ciSup_false (f : False → α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f

theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]

theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff (OrderBot.bddBelow _)

theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i := ciInf_le (OrderBot.bddBelow _) _

lemma ciInf_le_of_le' (c : ι) : f c ≤ a → iInf f ≤ a := ciInf_le_of_le (OrderBot.bddBelow _) _

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `ciSup_le_iff`. -/
theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_mem_range

theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  csSup_le' <| forall_mem_range.2 h

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `lt_ciSup_iff`. -/
theorem lt_ciSup_iff' {f : ι → α} (h : BddAbove (range f)) : a < iSup f ↔ ∃ i, a < f i := by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not

theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact ciSup_le' h

theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_le' fun i => Exists.elim (h i) (le_ciSup_of_le hg)

lemma ciSup_or' (p q : Prop) (f : p ∨ q → α) :
    ⨆ (h : p ∨ q), f h = (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h) := by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]

end ConditionallyCompleteLinearOrderBot

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']

theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd

theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd

theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf

theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne

end GaloisConnection

namespace OrderIso

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd

theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd

theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf

theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne

theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd

theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd

theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf

theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrderBot β]

@[simp]
lemma map_ciSup' (e : α ≃o β) (f : ι → α) : e (⨆ i, f i) = ⨆ i, e (f i) := by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i ↦ e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

end ConditionallyCompleteLinearOrderBot
end OrderIso

section WithTopBot

namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α}

lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩

lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]

lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top, Ne, iInf_coe_eq_top, not_isEmpty_iff]

end WithTop

end WithTopBot
