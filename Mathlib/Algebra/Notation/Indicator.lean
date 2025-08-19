/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Algebra.Notation.Support
import Mathlib.Data.Set.Piecewise

/-!
# Indicator function

This file defines the indicator function of a set. More lemmas can be found in
`Mathlib/Algebra/Group/Indicator.lean`.

## Main declarations

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

assert_not_exists Monoid

open Function

variable {α β M N : Type*}

namespace Set
variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise. -/
@[to_additive /-- `Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise. -/]
noncomputable def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then f x else 1

@[to_additive (attr := simp)]
lemma piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]
lemma mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by
  unfold mulIndicator
  congr

@[to_additive (attr := simp)]
lemma mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a := if_pos h

@[to_additive (attr := simp)]
lemma mulIndicator_of_notMem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 := if_neg h

@[deprecated (since := "2025-05-23")]
alias indicator_of_not_mem := indicator_of_notMem

@[to_additive existing, deprecated (since := "2025-05-23")]
alias mulIndicator_of_not_mem := mulIndicator_of_notMem

@[to_additive]
lemma mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases h : a ∈ s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_notMem h f)

@[to_additive (attr := simp)]
lemma mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

@[to_additive (attr := simp)]
lemma mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f ⊆ s := by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]
lemma mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := simp)]
lemma mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_right_iff

@[to_additive (attr := simp)]
lemma mulIndicator_eq_one : (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

@[to_additive (attr := simp)]
lemma mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one

@[to_additive]
lemma mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]
lemma mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive
/-- If an additive indicator function is not equal to `0` at a point, then that point is in the set.
-/]
lemma mem_of_mulIndicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mulIndicator_of_notMem hn f) h

/-- See `Set.eqOn_mulIndicator'` for the version with `sᶜ`. -/
@[to_additive /-- See `Set.eqOn_indicator'` for the version with `sᶜ`. -/]
lemma eqOn_mulIndicator : EqOn (mulIndicator s f) f s := fun _ hx => mulIndicator_of_mem hx f

/-- See `Set.eqOn_mulIndicator` for the version with `s`. -/
@[to_additive /-- See `Set.eqOn_indicator` for the version with `s`. -/]
lemma eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 sᶜ :=
  fun _ hx => mulIndicator_of_notMem hx f

@[to_additive]
lemma mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_notMem h f

@[to_additive (attr := simp)]
lemma mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f :=
  mulIndicator_eq_self.2 Subset.rfl

@[to_additive (attr := simp)]
lemma mulIndicator_range_comp {ι : Sort*} (f : ι → α) (g : α → M) :
    mulIndicator (range f) g ∘ f = g ∘ f :=
  letI := Classical.decPred (· ∈ range f)
  piecewise_range_comp _ _ _

@[to_additive]
lemma mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

@[to_additive]
lemma mulIndicator_eq_mulIndicator {t : Set β} {g : β → M} {b : β}
    (h1 : a ∈ s ↔ b ∈ t) (h2 : f a = g b) :
    s.mulIndicator f a = t.mulIndicator g b := by
  by_cases a ∈ s <;> simp_all

@[to_additive]
lemma mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : a ∈ s ↔ b ∈ t) :
    s.mulIndicator (fun _ ↦ c) a = t.mulIndicator (fun _ ↦ c) b :=
  mulIndicator_eq_mulIndicator h rfl

@[to_additive (attr := simp)]
lemma mulIndicator_univ (f : α → M) : mulIndicator (univ : Set α) f = f :=
  mulIndicator_eq_self.2 <| subset_univ _

@[to_additive (attr := simp)]
lemma mulIndicator_empty (f : α → M) : mulIndicator (∅ : Set α) f = fun _ => 1 :=
  mulIndicator_eq_one.2 <| disjoint_empty _

@[to_additive]
lemma mulIndicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f

variable (M)

@[to_additive (attr := simp)]
lemma mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) :=
  mulIndicator_eq_one.2 <| by simp only [mulSupport_fun_one, empty_disjoint]

@[to_additive (attr := simp)]
lemma mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mulIndicator_one M s

variable {M}

@[to_additive]
lemma mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]
lemma mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    mulIndicator (s ∩ mulSupport f) f = mulIndicator s f := by
  rw [← mulIndicator_mulIndicator, mulIndicator_mulSupport]

@[to_additive]
lemma comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  letI := Classical.decPred (· ∈ s)
  convert s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

@[to_additive]
lemma mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  tauto

@[to_additive]
lemma mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mulIndicator_comp_right, preimage_image_eq _ hg]

@[to_additive]
lemma mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]
lemma comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c :=
  (mulIndicator_comp_of_one hf).symm

@[to_additive]
lemma mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B

@[to_additive]
lemma mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s ∈ ({Set.univ, ∅} : Set (Set α)) := by
  classical
  rw [mulIndicator_one', Pi.one_def, Set.preimage_const]
  split_ifs <;> simp

@[to_additive]
lemma mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a ∈ s)]
    [Decidable ((1 : M) ∈ s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
      (if a ∈ s then U else ∅) ∪ if (1 : M) ∈ s then Uᶜ else ∅ := by
  rw [mulIndicator_preimage, Pi.one_def, Set.preimage_const, preimage_const]
  split_ifs <;> simp [← compl_eq_univ_diff]

@[to_additive]
lemma mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[to_additive]
lemma mulIndicator_preimage_of_notMem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

@[deprecated (since := "2025-05-23")]
alias indicator_preimage_of_not_mem := indicator_preimage_of_notMem

@[to_additive existing, deprecated (since := "2025-05-23")]
alias mulIndicator_preimage_of_not_mem := mulIndicator_preimage_of_notMem

@[to_additive]
lemma mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[to_additive]
lemma mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]

lemma indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) :=
  indicator_const_preimage _ _ 1

end Set
