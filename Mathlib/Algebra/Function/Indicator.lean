/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Algebra.Function.Support
import Mathlib.Algebra.Group.Pi.Lemmas

#align_import algebra.indicator_function from "leanprover-community/mathlib"@"2445c98ae4b87eabebdde552593519b9b6dc350c"

/-!
# Indicator function

- `Set.indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `Set.mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `fun _ ↦ 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.single` or `Set.piecewise`.

## Tags
indicator, characteristic
-/

open Function

variable {α β ι M N : Type*}

namespace Set

section One

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise.  -/
@[to_additive "`Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise."]
noncomputable def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then f x else 1
#align set.mul_indicator Set.mulIndicator

@[to_additive (attr := simp)]
theorem piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl
#align set.piecewise_eq_mul_indicator Set.piecewise_eq_mulIndicator
#align set.piecewise_eq_indicator Set.piecewise_eq_indicator

-- Porting note: needed unfold for mulIndicator
@[to_additive]
theorem mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by
  unfold mulIndicator
  congr
#align set.mul_indicator_apply Set.mulIndicator_apply
#align set.indicator_apply Set.indicator_apply

@[to_additive (attr := simp)]
theorem mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a :=
  if_pos h
#align set.mul_indicator_of_mem Set.mulIndicator_of_mem
#align set.indicator_of_mem Set.indicator_of_mem

@[to_additive (attr := simp)]
theorem mulIndicator_of_not_mem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 :=
  if_neg h
#align set.mul_indicator_of_not_mem Set.mulIndicator_of_not_mem
#align set.indicator_of_not_mem Set.indicator_of_not_mem

@[to_additive]
theorem mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases h : a ∈ s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_not_mem h f)
#align set.mul_indicator_eq_one_or_self Set.mulIndicator_eq_one_or_self
#align set.indicator_eq_zero_or_self Set.indicator_eq_zero_or_self

@[to_additive (attr := simp)]
theorem mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])
#align set.mul_indicator_apply_eq_self Set.mulIndicator_apply_eq_self
#align set.indicator_apply_eq_self Set.indicator_apply_eq_self

@[to_additive (attr := simp)]
theorem mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f ⊆ s := by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]
#align set.mul_indicator_eq_self Set.mulIndicator_eq_self
#align set.indicator_eq_self Set.indicator_eq_self

@[to_additive]
theorem mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2
#align set.mul_indicator_eq_self_of_superset Set.mulIndicator_eq_self_of_superset
#align set.indicator_eq_self_of_superset Set.indicator_eq_self_of_superset

@[to_additive (attr := simp)]
theorem mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_right_iff
#align set.mul_indicator_apply_eq_one Set.mulIndicator_apply_eq_one
#align set.indicator_apply_eq_zero Set.indicator_apply_eq_zero

@[to_additive (attr := simp)]
theorem mulIndicator_eq_one : (mulIndicator s f = fun x => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]
#align set.mul_indicator_eq_one Set.mulIndicator_eq_one
#align set.indicator_eq_zero Set.indicator_eq_zero

@[to_additive (attr := simp)]
theorem mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one
#align set.mul_indicator_eq_one' Set.mulIndicator_eq_one'
#align set.indicator_eq_zero' Set.indicator_eq_zero'

@[to_additive]
theorem mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne.def, mulIndicator_apply_eq_one, not_imp, mem_inter_iff, mem_mulSupport]
#align set.mul_indicator_apply_ne_one Set.mulIndicator_apply_ne_one
#align set.indicator_apply_ne_zero Set.indicator_apply_ne_zero

@[to_additive (attr := simp)]
theorem mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]
#align set.mul_support_mul_indicator Set.mulSupport_mulIndicator
#align set.support_indicator Set.support_indicator

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive
      "If an additive indicator function is not equal to `0` at a point, then that point is
      in the set."]
theorem mem_of_mulIndicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mulIndicator_of_not_mem hn f) h
#align set.mem_of_mul_indicator_ne_one Set.mem_of_mulIndicator_ne_one
#align set.mem_of_indicator_ne_zero Set.mem_of_indicator_ne_zero

@[to_additive]
theorem eqOn_mulIndicator : EqOn (mulIndicator s f) f s := fun _ hx => mulIndicator_of_mem hx f
#align set.eq_on_mul_indicator Set.eqOn_mulIndicator
#align set.eq_on_indicator Set.eqOn_indicator

@[to_additive]
theorem mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_not_mem h f
#align set.mul_support_mul_indicator_subset Set.mulSupport_mulIndicator_subset
#align set.support_indicator_subset Set.support_indicator_subset

@[to_additive (attr := simp)]
theorem mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f :=
  mulIndicator_eq_self.2 Subset.rfl
#align set.mul_indicator_mul_support Set.mulIndicator_mulSupport
#align set.indicator_support Set.indicator_support

@[to_additive (attr := simp)]
theorem mulIndicator_range_comp {ι : Sort*} (f : ι → α) (g : α → M) :
    mulIndicator (range f) g ∘ f = g ∘ f :=
  letI := Classical.decPred (· ∈ range f)
  piecewise_range_comp _ _ _
#align set.mul_indicator_range_comp Set.mulIndicator_range_comp
#align set.indicator_range_comp Set.indicator_range_comp

@[to_additive]
theorem mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl
#align set.mul_indicator_congr Set.mulIndicator_congr
#align set.indicator_congr Set.indicator_congr

@[to_additive (attr := simp)]
theorem mulIndicator_univ (f : α → M) : mulIndicator (univ : Set α) f = f :=
  mulIndicator_eq_self.2 <| subset_univ _
#align set.mul_indicator_univ Set.mulIndicator_univ
#align set.indicator_univ Set.indicator_univ

@[to_additive (attr := simp)]
theorem mulIndicator_empty (f : α → M) : mulIndicator (∅ : Set α) f = fun _ => 1 :=
  mulIndicator_eq_one.2 <| disjoint_empty _
#align set.mul_indicator_empty Set.mulIndicator_empty
#align set.indicator_empty Set.indicator_empty

@[to_additive]
theorem mulIndicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f
#align set.mul_indicator_empty' Set.mulIndicator_empty'
#align set.indicator_empty' Set.indicator_empty'

variable (M)

@[to_additive (attr := simp)]
theorem mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) :=
  mulIndicator_eq_one.2 <| by simp only [mulSupport_one, empty_disjoint]
#align set.mul_indicator_one Set.mulIndicator_one
#align set.indicator_zero Set.indicator_zero

@[to_additive (attr := simp)]
theorem mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mulIndicator_one M s
#align set.mul_indicator_one' Set.mulIndicator_one'
#align set.indicator_zero' Set.indicator_zero'

variable {M}

@[to_additive]
theorem mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all (config := { contextual := true })
#align set.mul_indicator_mul_indicator Set.mulIndicator_mulIndicator
#align set.indicator_indicator Set.indicator_indicator

@[to_additive (attr := simp)]
theorem mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    mulIndicator (s ∩ mulSupport f) f = mulIndicator s f := by
  rw [← mulIndicator_mulIndicator, mulIndicator_mulSupport]
#align set.mul_indicator_inter_mul_support Set.mulIndicator_inter_mulSupport
#align set.indicator_inter_support Set.indicator_inter_support

@[to_additive]
theorem comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  letI := Classical.decPred (· ∈ s)
  convert s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2
#align set.comp_mul_indicator Set.comp_mulIndicator
#align set.comp_indicator Set.comp_indicator

@[to_additive]
theorem mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  simp only [mulIndicator, Function.comp]
  split_ifs with h h' h'' <;> first | rfl | contradiction
#align set.mul_indicator_comp_right Set.mulIndicator_comp_right
#align set.indicator_comp_right Set.indicator_comp_right

@[to_additive]
theorem mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mulIndicator_comp_right, preimage_image_eq _ hg]
#align set.mul_indicator_image Set.mulIndicator_image
#align set.indicator_image Set.indicator_image

@[to_additive]
theorem mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]
#align set.mul_indicator_comp_of_one Set.mulIndicator_comp_of_one
#align set.indicator_comp_of_zero Set.indicator_comp_of_zero

@[to_additive]
theorem comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c :=
  (mulIndicator_comp_of_one hf).symm
#align set.comp_mul_indicator_const Set.comp_mulIndicator_const
#align set.comp_indicator_const Set.comp_indicator_const

@[to_additive]
theorem mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B
#align set.mul_indicator_preimage Set.mulIndicator_preimage
#align set.indicator_preimage Set.indicator_preimage

@[to_additive]
theorem mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s ∈ ({Set.univ, ∅} : Set (Set α)) := by
  classical
    rw [mulIndicator_one', preimage_one]
    split_ifs <;> simp
#align set.mul_indicator_one_preimage Set.mulIndicator_one_preimage
#align set.indicator_zero_preimage Set.indicator_zero_preimage

@[to_additive]
theorem mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a ∈ s)]
    [Decidable ((1 : M) ∈ s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
      (if a ∈ s then U else ∅) ∪ if (1 : M) ∈ s then Uᶜ else ∅ := by
  rw [mulIndicator_preimage, preimage_one, preimage_const]
  split_ifs <;> simp [← compl_eq_univ_diff]
#align set.mul_indicator_const_preimage_eq_union Set.mulIndicator_const_preimage_eq_union
#align set.indicator_const_preimage_eq_union Set.indicator_const_preimage_eq_union

@[to_additive]
theorem mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp
#align set.mul_indicator_const_preimage Set.mulIndicator_const_preimage
#align set.indicator_const_preimage Set.indicator_const_preimage

theorem indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) :=
  indicator_const_preimage _ _ 1
#align set.indicator_one_preimage Set.indicator_one_preimage

@[to_additive]
theorem mulIndicator_preimage_of_not_mem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_not_mem ht]
#align set.mul_indicator_preimage_of_not_mem Set.mulIndicator_preimage_of_not_mem
#align set.indicator_preimage_of_not_mem Set.indicator_preimage_of_not_mem

@[to_additive]
theorem mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
-- Porting note: This proof used to be:
  -- simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
  -- @eq_comm _ r 1]
  simp only [mem_range, mulIndicator, ne_eq, mem_image]
  rw [eq_univ_iff_forall, not_forall]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    split_ifs at hy with hys
    · tauto
    · left
      tauto
  · rintro (⟨hr, ⟨x, hx⟩⟩ | ⟨x, ⟨hx, hxs⟩⟩) <;> use x <;> split_ifs <;> tauto
#align set.mem_range_mul_indicator Set.mem_range_mulIndicator
#align set.mem_range_indicator Set.mem_range_indicator

@[to_additive]
theorem mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]
#align set.mul_indicator_rel_mul_indicator Set.mulIndicator_rel_mulIndicator
#align set.indicator_rel_indicator Set.indicator_rel_indicator

end One

section Monoid

variable [MulOneClass M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive]
theorem mulIndicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a
      = mulIndicator s f a * mulIndicator t f a := by
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [*]
#align set.mul_indicator_union_mul_inter_apply Set.mulIndicator_union_mul_inter_apply
#align set.indicator_union_add_inter_apply Set.indicator_union_add_inter_apply

@[to_additive]
theorem mulIndicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f :=
  funext <| mulIndicator_union_mul_inter_apply f s t
#align set.mul_indicator_union_mul_inter Set.mulIndicator_union_mul_inter
#align set.indicator_union_add_inter Set.indicator_union_add_inter

@[to_additive]
theorem mulIndicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← mulIndicator_union_mul_inter_apply f s t, mulIndicator_of_not_mem h, mul_one]
#align set.mul_indicator_union_of_not_mem_inter Set.mulIndicator_union_of_not_mem_inter
#align set.indicator_union_of_not_mem_inter Set.indicator_union_of_not_mem_inter

@[to_additive]
theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a :=
  funext fun _ => mulIndicator_union_of_not_mem_inter (fun ha => h.le_bot ha) _
#align set.mul_indicator_union_of_disjoint Set.mulIndicator_union_of_disjoint
#align set.indicator_union_of_disjoint Set.indicator_union_of_disjoint

open scoped symmDiff in
@[to_additive]
theorem mulIndicator_symmDiff (s t : Set α) (f : α → M) :
    mulIndicator (s ∆ t) f = mulIndicator (s \ t) f * mulIndicator (t \ s) f :=
  mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[to_additive]
theorem mulIndicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]
#align set.mul_indicator_mul Set.mulIndicator_mul
#align set.indicator_add Set.indicator_add

@[to_additive]
theorem mulIndicator_mul' (s : Set α) (f g : α → M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mulIndicator_mul s f g
#align set.mul_indicator_mul' Set.mulIndicator_mul'
#align set.indicator_add' Set.indicator_add'

@[to_additive (attr := simp)]
theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator sᶜ f a * mulIndicator s f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]
#align set.mul_indicator_compl_mul_self_apply Set.mulIndicator_compl_mul_self_apply
#align set.indicator_compl_add_self_apply Set.indicator_compl_add_self_apply

@[to_additive (attr := simp)]
theorem mulIndicator_compl_mul_self (s : Set α) (f : α → M) :
    mulIndicator sᶜ f * mulIndicator s f = f :=
  funext <| mulIndicator_compl_mul_self_apply s f
#align set.mul_indicator_compl_mul_self Set.mulIndicator_compl_mul_self
#align set.indicator_compl_add_self Set.indicator_compl_add_self

@[to_additive (attr := simp)]
theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator sᶜ f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]
#align set.mul_indicator_self_mul_compl_apply Set.mulIndicator_self_mul_compl_apply
#align set.indicator_self_add_compl_apply Set.indicator_self_add_compl_apply

@[to_additive (attr := simp)]
theorem mulIndicator_self_mul_compl (s : Set α) (f : α → M) :
    mulIndicator s f * mulIndicator sᶜ f = f :=
  funext <| mulIndicator_self_mul_compl_apply s f
#align set.mul_indicator_self_mul_compl Set.mulIndicator_self_mul_compl
#align set.indicator_self_add_compl Set.indicator_self_add_compl

@[to_additive]
theorem mulIndicator_mul_eq_left {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f := by
  refine' (mulIndicator_congr fun x hx => _).trans mulIndicator_mulSupport
  have : g x = 1 := nmem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply, this, mul_one]
#align set.mul_indicator_mul_eq_left Set.mulIndicator_mul_eq_left
#align set.indicator_add_eq_left Set.indicator_add_eq_left

@[to_additive]
theorem mulIndicator_mul_eq_right {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g := by
  refine' (mulIndicator_congr fun x hx => _).trans mulIndicator_mulSupport
  have : f x = 1 := nmem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply, this, one_mul]
#align set.mul_indicator_mul_eq_right Set.mulIndicator_mul_eq_right
#align set.indicator_add_eq_right Set.indicator_add_eq_right

@[to_additive]
theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases h : x ∈ s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_not_mem (Set.not_mem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_not_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_not_mem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]
#align set.mul_indicator_mul_compl_eq_piecewise Set.mulIndicator_mul_compl_eq_piecewise
#align set.indicator_add_compl_eq_piecewise Set.indicator_add_compl_eq_piecewise

/-- `Set.mulIndicator` as a `monoidHom`. -/
@[to_additive "`Set.indicator` as an `addMonoidHom`."]
noncomputable def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α → M) →* α → M
    where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s
#align set.mul_indicator_hom Set.mulIndicatorHom
#align set.indicator_hom Set.indicatorHom

end Monoid

section Group

variable {G : Type*} [Group G] {s t : Set α} {f g : α → G} {a : α}

@[to_additive]
theorem mulIndicator_inv' (s : Set α) (f : α → G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ :=
  (mulIndicatorHom G s).map_inv f
#align set.mul_indicator_inv' Set.mulIndicator_inv'
#align set.indicator_neg' Set.indicator_neg'

@[to_additive]
theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mulIndicator_inv' s f
#align set.mul_indicator_inv Set.mulIndicator_inv
#align set.indicator_neg Set.indicator_neg

@[to_additive]
theorem mulIndicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a :=
  (mulIndicatorHom G s).map_div f g
#align set.mul_indicator_div Set.mulIndicator_div
#align set.indicator_sub Set.indicator_sub

@[to_additive]
theorem mulIndicator_div' (s : Set α) (f g : α → G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mulIndicator_div s f g
#align set.mul_indicator_div' Set.mulIndicator_div'
#align set.indicator_sub' Set.indicator_sub'

@[to_additive indicator_compl']
theorem mulIndicator_compl (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| s.mulIndicator_compl_mul_self f
#align set.mul_indicator_compl Set.mulIndicator_compl
#align set.indicator_compl' Set.indicator_compl'

@[to_additive indicator_compl]
theorem mulIndicator_compl' (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f / mulIndicator s f := by rw [div_eq_mul_inv, mulIndicator_compl]
#align set.indicator_compl Set.indicator_compl

@[to_additive indicator_diff']
theorem mulIndicator_diff (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by
    rw [Pi.mul_def, ← mulIndicator_union_of_disjoint, diff_union_self,
      union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left
#align set.mul_indicator_diff Set.mulIndicator_diff
#align set.indicator_diff' Set.indicator_diff'

@[to_additive indicator_diff]
theorem mulIndicator_diff' (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f / mulIndicator s f := by
  rw [mulIndicator_diff h, div_eq_mul_inv]
#align set.indicator_diff Set.indicator_diff

open scoped symmDiff in
@[to_additive]
theorem apply_mulIndicator_symmDiff {g : G → β} (hg : ∀ x, g x⁻¹ = g x)
    (s t : Set α) (f : α → G) (x : α):
    g (mulIndicator (s ∆ t) f x) = g (mulIndicator s f x / mulIndicator t f x) := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [mem_symmDiff, *]

end Group

section MulZeroClass

variable [MulZeroClass M] {s t : Set α} {f g : α → M} {a : α}

theorem indicator_mul (s : Set α) (f g : α → M) :
    (indicator s fun a => f a * g a) = fun a => indicator s f a * indicator s g a := by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
#align set.indicator_mul Set.indicator_mul

theorem indicator_mul_left (s : Set α) (f g : α → M) :
    indicator s (fun a => f a * g a) a = indicator s f a * g a := by
  simp only [indicator]
  split_ifs
  · rfl
  rw [zero_mul]
#align set.indicator_mul_left Set.indicator_mul_left

theorem indicator_mul_right (s : Set α) (f g : α → M) :
    indicator s (fun a => f a * g a) a = f a * indicator s g a := by
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
#align set.indicator_mul_right Set.indicator_mul_right

theorem inter_indicator_mul {t1 t2 : Set α} (f g : α → M) (x : α) :
    (t1 ∩ t2).indicator (fun x => f x * g x) x = t1.indicator f x * t2.indicator g x := by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp
#align set.inter_indicator_mul Set.inter_indicator_mul

end MulZeroClass

section MulZeroOneClass

variable [MulZeroOneClass M]

theorem inter_indicator_one {s t : Set α} :
    (s ∩ t).indicator (1 : α → M) = s.indicator 1 * t.indicator 1 :=
  funext fun _ => by
    simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]
    congr
#align set.inter_indicator_one Set.inter_indicator_one

-- Porting note: Think the following note was due to writing (1 : _ → M) instead of (1 : α × β → M)
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem indicator_prod_one {s : Set α} {t : Set β} {x : α} {y : β} :
    (s ×ˢ t).indicator (1 : α × β → M) (x, y) = s.indicator 1 x * t.indicator 1 y := by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto
#align set.indicator_prod_one Set.indicator_prod_one

variable (M) [Nontrivial M]

theorem indicator_eq_zero_iff_not_mem {U : Set α} {x : α} : indicator U 1 x = (0 : M) ↔ x ∉ U := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_zero_iff_not_mem Set.indicator_eq_zero_iff_not_mem

theorem indicator_eq_one_iff_mem {U : Set α} {x : α} : indicator U 1 x = (1 : M) ↔ x ∈ U := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_one_iff_mem Set.indicator_eq_one_iff_mem

theorem indicator_one_inj {U V : Set α} (h : indicator U (1 : α → M) = indicator V 1) : U = V := by
  ext
  simp_rw [← indicator_eq_one_iff_mem M, h]
#align set.indicator_one_inj Set.indicator_one_inj

end MulZeroOneClass

end Set

@[to_additive]
theorem MonoidHom.map_mulIndicator {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]
#align monoid_hom.map_mul_indicator MonoidHom.map_mulIndicator
#align add_monoid_hom.map_indicator AddMonoidHom.map_indicator
