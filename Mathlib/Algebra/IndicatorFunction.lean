/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Algebra.Support

#align_import algebra.indicator_function from "leanprover-community/mathlib"@"2445c98ae4b87eabebdde552593519b9b6dc350c"

/-!
# Indicator function

- `indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `λx, 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.Single` or `Set.Piecewise`.

## Tags
indicator, characteristic
-/

open BigOperators

open Function

variable {α β ι M N : Type _}

namespace Set

section One

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
noncomputable def indicator {M} [Zero M] (s : Set α) (f : α → M) : α → M
  | x =>
    haveI := Classical.decPred (· ∈ s)
    if x ∈ s then f x else 0
#align set.indicator Set.indicator

/-- `mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise.  -/
@[to_additive existing]
noncomputable def mulIndicator (s : Set α) (f : α → M) : α → M
  | x =>
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
      split_ifs with h <;> simp
#align set.mul_indicator_apply Set.mulIndicator_apply
#align set.indicator_apply Set.indicator_apply

@[to_additive (attr := simp)]
theorem mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a :=
  letI := Classical.dec (a ∈ s)
  if_pos h
#align set.mul_indicator_of_mem Set.mulIndicator_of_mem
#align set.indicator_of_mem Set.indicator_of_mem

@[to_additive (attr := simp)]
theorem mulIndicator_of_not_mem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 :=
  letI := Classical.dec (a ∈ s)
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
    split_ifs
    repeat' simp_all (config := { contextual := true })
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
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a = mulIndicator s f a * mulIndicator t f a :=
  by by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [*]
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

section DistribMulAction

variable {A : Type*} [AddMonoid A] [Monoid M] [DistribMulAction M A]

theorem indicator_smul_apply (s : Set α) (r : α → M) (f : α → A) (x : α) :
    indicator s (fun x => r x • f x) x = r x • indicator s f x := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r x)).symm]
#align set.indicator_smul_apply Set.indicator_smul_apply

theorem indicator_smul (s : Set α) (r : α → M) (f : α → A) :
    (indicator s fun x : α => r x • f x) = fun x : α => r x • indicator s f x :=
  funext <| indicator_smul_apply s r f
#align set.indicator_smul Set.indicator_smul

theorem indicator_const_smul_apply (s : Set α) (r : M) (f : α → A) (x : α) :
    indicator s (fun x => r • f x) x = r • indicator s f x :=
  indicator_smul_apply s (fun _ => r) f x
#align set.indicator_const_smul_apply Set.indicator_const_smul_apply

theorem indicator_const_smul (s : Set α) (r : M) (f : α → A) :
    (indicator s fun x : α => r • f x) = fun x : α => r • indicator s f x :=
  funext <| indicator_const_smul_apply s r f
#align set.indicator_const_smul Set.indicator_const_smul

end DistribMulAction

section SMulWithZero

variable {A : Type*} [Zero A] [Zero M] [SMulWithZero M A]

theorem indicator_smul_apply_left (s : Set α) (r : α → M) (f : α → A) (x : α) :
    indicator s (fun x => r x • f x) x = indicator s r x • f x := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f x)).symm]

theorem indicator_smul_left (s : Set α) (r : α → M) (f : α → A) :
    (indicator s fun x : α => r x • f x) = fun x : α => indicator s r x • f x :=
  funext <| indicator_smul_apply_left s r f

theorem indicator_smul_const_apply (s : Set α) (r : α → M) (a : A) (x : α) :
    indicator s (fun x => r x • a) x = indicator s r x • a :=
  indicator_smul_apply_left s r (fun _ => a) x

theorem indicator_smul_const (s : Set α) (r : α → M) (a : A) :
    (indicator s fun x : α => r x • a) = fun x : α => indicator s r x • a :=
  funext <| indicator_smul_const_apply s r a

end SMulWithZero

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

theorem indicator_compl {G} [AddGroup G] (s : Set α) (f : α → G) :
    indicator sᶜ f = f - indicator s f := by rw [sub_eq_add_neg, indicator_compl']
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

theorem indicator_diff {G : Type*} [AddGroup G] {s t : Set α} (h : s ⊆ t) (f : α → G) :
    indicator (t \ s) f = indicator t f - indicator s f := by rw [indicator_diff' h, sub_eq_add_neg]
#align set.indicator_diff Set.indicator_diff

end Group

section CommMonoid

variable [CommMonoid M]

/-- Consider a product of `g i (f i)` over a `Finset`.  Suppose `g` is a
function such as `Pow`, which maps a second argument of `1` to
`1`. Then if `f` is replaced by the corresponding multiplicative indicator
function, the `Finset` may be replaced by a possibly larger `Finset`
without changing the value of the sum. -/
@[to_additive]
theorem prod_mulIndicator_subset_of_eq_one [One N] (f : α → N) (g : α → N → M) {s t : Finset α}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    (∏ i in s, g i (f i)) = ∏ i in t, g i (mulIndicator (↑s) f i) := by
  rw [← Finset.prod_subset h _]
  · apply Finset.prod_congr rfl
    intro i hi
    congr
    symm
    -- Porting note: This did not use to need the implicit argument
    exact mulIndicator_of_mem (α := α) hi f
  · refine' fun i _ hn => _
    convert hg i
    -- Porting note: This did not use to need the implicit argument
    exact mulIndicator_of_not_mem (α := α) hn f
#align set.prod_mul_indicator_subset_of_eq_one Set.prod_mulIndicator_subset_of_eq_one
#align set.sum_indicator_subset_of_eq_zero Set.sum_indicator_subset_of_eq_zero

/-- Consider a sum of `g i (f i)` over a `Finset`. Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i • h i`,
where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `Finset` may be replaced by a possibly larger `Finset`
without changing the value of the sum. -/
add_decl_doc Set.sum_indicator_subset_of_eq_zero

/-- Taking the product of an indicator function over a possibly larger `Finset` is the same as
taking the original function over the original `Finset`. -/
@[to_additive
      "Summing an indicator function over a possibly larger `Finset` is the same as summing
      the original function over the original `finset`."]
theorem prod_mulIndicator_subset (f : α → M) {s t : Finset α} (h : s ⊆ t) :
    ∏ i in s, f i = ∏ i in t, mulIndicator (↑s) f i :=
  prod_mulIndicator_subset_of_eq_one _ (fun _ b => b) h fun _ => rfl
#align set.prod_mul_indicator_subset Set.prod_mulIndicator_subset
#align set.sum_indicator_subset Set.sum_indicator_subset

@[to_additive]
theorem _root_.Finset.prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → α → M)
    (t : ι → Set α) (g : ι → α) [DecidablePred fun i => g i ∈ t i] :
    (∏ i in s, mulIndicator (t i) (f i) (g i)) = ∏ i in s.filter fun i => g i ∈ t i, f i (g i) := by
  refine' (Finset.prod_filter_mul_prod_filter_not s (fun i => g i ∈ t i) _).symm.trans _
  refine' Eq.trans _ (mul_one _)
  exact
    congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun x hx => mulIndicator_of_mem (Finset.mem_filter.1 hx).2 _)
      (Finset.prod_eq_one fun x hx => mulIndicator_of_not_mem (Finset.mem_filter.1 hx).2 _)
#align finset.prod_mul_indicator_eq_prod_filter Finset.prod_mulIndicator_eq_prod_filter
#align finset.sum_indicator_eq_sum_filter Finset.sum_indicator_eq_sum_filter

@[to_additive]
theorem mulIndicator_finset_prod (I : Finset ι) (s : Set α) (f : ι → α → M) :
    mulIndicator s (∏ i in I, f i) = ∏ i in I, mulIndicator s (f i) :=
  (mulIndicatorHom M s).map_prod _ _
#align set.mul_indicator_finset_prod Set.mulIndicator_finset_prod
#align set.indicator_finset_sum Set.indicator_finset_sum

@[to_additive]
theorem mulIndicator_finset_biUnion {ι} (I : Finset ι) (s : ι → Set α) {f : α → M} :
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (s i) (s j)) →
      mulIndicator (⋃ i ∈ I, s i) f = fun a => ∏ i in I, mulIndicator (s i) f a := by
  classical
    refine' Finset.induction_on I _ _
    · intro
      funext
      simp
    intro a I haI ih hI
    funext
    rw [Finset.prod_insert haI, Finset.set_biUnion_insert, mulIndicator_union_of_not_mem_inter,
      ih _]
    · intro i hi j hj hij
      exact hI i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    simp only [not_exists, exists_prop, mem_iUnion, mem_inter_iff, not_and]
    intro hx a' ha'
    refine'
      disjoint_left.1 (hI a (Finset.mem_insert_self _ _) a' (Finset.mem_insert_of_mem ha') _) hx
    exact (ne_of_mem_of_not_mem ha' haI).symm
#align set.mul_indicator_finset_bUnion Set.mulIndicator_finset_biUnion
#align set.indicator_finset_bUnion Set.indicator_finset_biUnion

@[to_additive]
theorem mulIndicator_finset_biUnion_apply {ι} (I : Finset ι) (s : ι → Set α) {f : α → M}
    (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (s i) (s j)) (x : α) :
    mulIndicator (⋃ i ∈ I, s i) f x = ∏ i in I, mulIndicator (s i) f x := by
  rw [Set.mulIndicator_finset_biUnion I s h]
#align set.mul_indicator_finset_bUnion_apply Set.mulIndicator_finset_biUnion_apply
#align set.indicator_finset_bUnion_apply Set.indicator_finset_biUnion_apply

end CommMonoid

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

section Order

variable [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

section

variable [LE M]

@[to_additive]
theorem mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha
#align set.mul_indicator_apply_le' Set.mulIndicator_apply_le'
#align set.indicator_apply_le' Set.indicator_apply_le'

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2:
warning: expanding binder collection (a «expr ∉ » s) -/
@[to_additive]
theorem mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ (a) (_ : a ∉ s), 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ => mulIndicator_apply_le' (hfg _) (hg _)
#align set.mul_indicator_le' Set.mulIndicator_le'
#align set.indicator_le' Set.indicator_le'

@[to_additive]
theorem le_mulIndicator_apply {y} (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a :=
  @mulIndicator_apply_le' α Mᵒᵈ ‹_› _ _ _ _ _ hfg hf
#align set.le_mul_indicator_apply Set.le_mulIndicator_apply
#align set.le_indicator_apply Set.le_indicator_apply

@[to_additive]
theorem le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ (a) (_ : a ∉ s), f a ≤ 1) :
    f ≤ mulIndicator s g := fun _ => le_mulIndicator_apply (hfg _) (hf _)
#align set.le_mul_indicator Set.le_mulIndicator
#align set.le_indicator Set.le_indicator

end

variable [Preorder M]

@[to_additive indicator_apply_nonneg]
theorem one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ => le_rfl
#align set.one_le_mul_indicator_apply Set.one_le_mulIndicator_apply
#align set.indicator_apply_nonneg Set.indicator_apply_nonneg

@[to_additive indicator_nonneg]
theorem one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)
#align set.one_le_mul_indicator Set.one_le_mulIndicator
#align set.indicator_nonneg Set.indicator_nonneg

@[to_additive]
theorem mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le' h fun _ => le_rfl
#align set.mul_indicator_apply_le_one Set.mulIndicator_apply_le_one
#align set.indicator_apply_nonpos Set.indicator_apply_nonpos

@[to_additive]
theorem mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le_one (h a)
#align set.mul_indicator_le_one Set.mulIndicator_le_one
#align set.indicator_nonpos Set.indicator_nonpos

@[to_additive]
theorem mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ => h
#align set.mul_indicator_le_mul_indicator Set.mulIndicator_le_mulIndicator
#align set.indicator_le_indicator Set.indicator_le_indicator

attribute [mono] mulIndicator_le_mulIndicator indicator_le_indicator

@[to_additive]
theorem mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) (a : α) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha => le_mulIndicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun _ =>
    one_le_mulIndicator_apply fun _ => hf _
#align set.mul_indicator_le_mul_indicator_of_subset Set.mulIndicator_le_mulIndicator_of_subset
#align set.indicator_le_indicator_of_subset Set.indicator_le_indicator_of_subset

@[to_additive]
theorem mulIndicator_le_self' (hf : ∀ (x) (_ : x ∉ s), 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ => le_rfl) hf
#align set.mul_indicator_le_self' Set.mulIndicator_le_self'
#align set.indicator_le_self' Set.indicator_le_self'

@[to_additive]
theorem mulIndicator_iUnion_apply {ι M} [CompleteLattice M] [One M] (h1 : (⊥ : M) = 1)
    (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine' le_antisymm _ (iSup_le fun i => mulIndicator_le_self' (fun x _ => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_not_mem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]
#align set.mul_indicator_Union_apply Set.mulIndicator_iUnion_apply
#align set.indicator_Union_apply Set.indicator_iUnion_apply

@[to_additive] lemma mulIndicator_iInter_apply {ι M} [Nonempty ι] [CompleteLattice M] [One M]
    (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iInter] at hx
    refine le_antisymm ?_ (by simp only [mulIndicator_of_mem (hx _), ciInf_const, le_refl])
    exact le_iInf (fun j ↦ by simp only [mulIndicator_of_mem (hx j), le_refl])
  · rw [mulIndicator_of_not_mem hx]
    simp only [mem_iInter, not_exists, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_not_mem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

end Order

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid M]

@[to_additive]
theorem mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mulIndicator_le_self' fun _ _ => one_le _
#align set.mul_indicator_le_self Set.mulIndicator_le_self
#align set.indicator_le_self Set.indicator_le_self

@[to_additive]
theorem mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  mulIndicator_apply_le' hfg fun _ => one_le _
#align set.mul_indicator_apply_le Set.mulIndicator_apply_le
#align set.indicator_apply_le Set.indicator_apply_le

@[to_additive]
theorem mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  mulIndicator_le' hfg fun _ _ => one_le _
#align set.mul_indicator_le Set.mulIndicator_le
#align set.indicator_le Set.indicator_le

end CanonicallyOrderedMonoid

theorem indicator_le_indicator_nonneg {β} [LinearOrder β] [Zero β] (s : Set α) (f : α → β) :
    s.indicator f ≤ { x | 0 ≤ f x }.indicator f := by
  intro x
  classical
    simp_rw [indicator_apply]
    split_ifs with h_1 h_2 h_3
    · exact le_rfl
    · exact (not_le.mp h_2).le
    · exact h_3
    · exact le_rfl
#align set.indicator_le_indicator_nonneg Set.indicator_le_indicator_nonneg

theorem indicator_nonpos_le_indicator {β} [LinearOrder β] [Zero β] (s : Set α) (f : α → β) :
    { x | f x ≤ 0 }.indicator f ≤ s.indicator f :=
  @indicator_le_indicator_nonneg α βᵒᵈ _ _ s f
#align set.indicator_nonpos_le_indicator Set.indicator_nonpos_le_indicator

end Set

@[to_additive]
theorem MonoidHom.map_mulIndicator {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]
#align monoid_hom.map_mul_indicator MonoidHom.map_mulIndicator
#align add_monoid_hom.map_indicator AddMonoidHom.map_indicator
