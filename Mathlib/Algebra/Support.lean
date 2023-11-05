/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Module.Basic
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Order.Cover

#align_import algebra.support from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/


open Set

open BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type*} {ι : Sort*}

section One

variable [One M] [One N] [One P]

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }

/-- `mulSupport` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive existing]
def mulSupport (f : α → M) : Set α :=
  { x | f x ≠ 1 }

@[to_additive]
theorem mulSupport_eq_preimage (f : α → M) : mulSupport f = f ⁻¹' {1}ᶜ :=
  rfl

@[to_additive]
theorem nmem_mulSupport {f : α → M} {x : α} : x ∉ mulSupport f ↔ f x = 1 :=
  not_not

@[to_additive]
theorem compl_mulSupport {f : α → M} : (mulSupport f)ᶜ = { x | f x = 1 } :=
  ext fun _ => nmem_mulSupport

@[to_additive (attr := simp)]
theorem mem_mulSupport {f : α → M} {x : α} : x ∈ mulSupport f ↔ f x ≠ 1 :=
  Iff.rfl

@[to_additive (attr := simp)]
theorem mulSupport_subset_iff {f : α → M} {s : Set α} : mulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl

@[to_additive]
theorem mulSupport_subset_iff' {f : α → M} {s : Set α} :
    mulSupport f ⊆ s ↔ ∀ (x) (_ : x ∉ s), f x = 1 :=
  forall_congr' fun _ => not_imp_comm

@[to_additive]
theorem mulSupport_eq_iff {f : α → M} {s : Set α} :
    mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp (config := { contextual := true }) only [ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]
theorem mulSupport_disjoint_iff {f : α → M} {s : Set α} :
    Disjoint (mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', not_mem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]
theorem disjoint_mulSupport_iff {f : α → M} {s : Set α} : Disjoint s (mulSupport f) ↔ EqOn f 1 s :=
  by rw [disjoint_comm, mulSupport_disjoint_iff]

@[to_additive (attr := simp)]
theorem mulSupport_eq_empty_iff {f : α → M} : mulSupport f = ∅ ↔ f = 1 := by
  simp_rw [← subset_empty_iff, mulSupport_subset_iff', funext_iff]
  simp

@[to_additive (attr := simp)]
theorem mulSupport_nonempty_iff {f : α → M} : (mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne.def, mulSupport_eq_empty_iff]

@[to_additive]
theorem range_subset_insert_image_mulSupport (f : α → M) :
    range f ⊆ insert 1 (f '' mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using
    fun x (hx : x ∈ mulSupport f) => mem_image_of_mem f hx

@[to_additive]
lemma range_eq_image_or_of_mulSupport_subset {f : α → M} {k : Set α} (h : mulSupport f ⊆ k) :
    range f = f '' k ∨ range f = insert 1 (f '' k) := by
  apply (wcovby_insert _ _).eq_or_eq (image_subset_range _ _)
  exact (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_subset f h))

@[to_additive (attr := simp)]
theorem mulSupport_one' : mulSupport (1 : α → M) = ∅ :=
  mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]
theorem mulSupport_one : (mulSupport fun _ : α => (1 : M)) = ∅ :=
  mulSupport_one'

@[to_additive]
theorem mulSupport_const {c : M} (hc : c ≠ 1) : (mulSupport fun _ : α => c) = Set.univ := by
  ext x
  simp [hc]

@[to_additive]
theorem mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (mulSupport fun x => op (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := fun x hx =>
  not_or_of_imp fun hf hg => hx <| by simp only [hf, hg, op1]

@[to_additive]
theorem mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    (mulSupport fun x => f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) sup_idem f g

@[to_additive]
theorem mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    (mulSupport fun x => f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) inf_idem f g

@[to_additive]
theorem mulSupport_max [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_sup f g

@[to_additive]
theorem mulSupport_min [LinearOrder M] (f g : α → M) :
    (mulSupport fun x => min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_inf f g

@[to_additive]
theorem mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  rw [mulSupport_subset_iff']
  simp only [mem_iUnion, not_exists, nmem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]
theorem mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (mulSupport fun x => ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) :=
  @mulSupport_iSup _ Mᵒᵈ ι ⟨(1 : M)⟩ _ _ f

@[to_additive]
theorem mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) :
    mulSupport (g ∘ f) ⊆ mulSupport f := fun x => mt fun h => by simp only [(· ∘ ·), *]

@[to_additive]
theorem mulSupport_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    mulSupport f ⊆ mulSupport (g ∘ f) := fun _ => mt hg

@[to_additive]
theorem mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun _ => not_congr hg

@[to_additive]
theorem mulSupport_comp_eq_of_range_subset {g : M → N} {f : α → M}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun x ↦ not_congr <| by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]
theorem mulSupport_comp_eq_preimage (g : β → M) (f : α → β) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g :=
  rfl

@[to_additive support_prod_mk]
theorem mulSupport_prod_mk (f : α → M) (g : α → N) :
    (mulSupport fun x => (f x, g x)) = mulSupport f ∪ mulSupport g :=
  Set.ext fun x => by
    simp only [mulSupport, not_and_or, mem_union, mem_setOf_eq, Prod.mk_eq_one, Ne.def]

@[to_additive support_prod_mk']
theorem mulSupport_prod_mk' (f : α → M × N) :
    mulSupport f = (mulSupport fun x => (f x).1) ∪ mulSupport fun x => (f x).2 := by
  simp only [← mulSupport_prod_mk]

@[to_additive]
theorem mulSupport_along_fiber_subset (f : α × β → M) (a : α) :
    (mulSupport fun b => f (a, b)) ⊆ (mulSupport f).image Prod.snd :=
  fun x hx => ⟨(a, x), by simpa using hx⟩

@[to_additive (attr := simp)]
theorem mulSupport_along_fiber_finite_of_finite (f : α × β → M) (a : α)
    (h : (mulSupport f).Finite) : (mulSupport fun b => f (a, b)).Finite :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end One

@[to_additive]
theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x => f x * g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]
theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction' n with n hfn
  · simp [pow_zero, mulSupport_one]
  · simpa only [pow_succ] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[to_additive (attr := simp)]
theorem mulSupport_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one

@[to_additive (attr := simp)]
theorem mulSupport_inv' : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_inv f

@[to_additive]
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]
theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g

end DivisionMonoid

section ZeroOne

variable (R) [Zero R] [One R] [NeZero (1 : R)]

@[simp]
theorem support_one : support (1 : α → R) = univ :=
  support_const one_ne_zero

@[simp]
theorem mulSupport_zero : mulSupport (0 : α → R) = univ :=
  mulSupport_const zero_ne_one

end ZeroOne

section AddMonoidWithOne

variable [AddMonoidWithOne R] [CharZero R] {n : ℕ}

theorem support_nat_cast (hn : n ≠ 0) : support (n : α → R) = univ :=
  support_const <| Nat.cast_ne_zero.2 hn

theorem mulSupport_nat_cast (hn : n ≠ 1) : mulSupport (n : α → R) = univ :=
  mulSupport_const <| Nat.cast_ne_one.2 hn

end AddMonoidWithOne

section AddGroupWithOne

variable [AddGroupWithOne R] [CharZero R] {n : ℤ}

theorem support_int_cast (hn : n ≠ 0) : support (n : α → R) = univ :=
  support_const <| Int.cast_ne_zero.2 hn

theorem mulSupport_int_cast (hn : n ≠ 1) : mulSupport (n : α → R) = univ :=
  mulSupport_const <| Int.cast_ne_one.2 hn

end AddGroupWithOne

theorem support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun _ => smul_ne_zero_iff

@[simp]
theorem support_mul [MulZeroClass R] [NoZeroDivisors R] (f g : α → R) :
    (support fun x => f x * g x) = support f ∩ support g :=
  support_smul f g

--@[simp] Porting note: removing simp, bad lemma LHS not in normal form
theorem support_mul_subset_left [MulZeroClass R] (f g : α → R) :
    (support fun x => f x * g x) ⊆ support f := fun x hfg hf => hfg <| by simp only [hf, zero_mul]

--@[simp] Porting note: removing simp, bad lemma LHS not in normal form
theorem support_mul_subset_right [MulZeroClass R] (f g : α → R) :
    (support fun x => f x * g x) ⊆ support g := fun x hfg hg => hfg <| by simp only [hg, mul_zero]

theorem support_smul_subset_right [AddMonoid A] [Monoid B] [DistribMulAction B A] (b : B)
    (f : α → A) : support (b • f) ⊆ support f := fun x hbf hf =>
  hbf <| by rw [Pi.smul_apply, hf, smul_zero]

theorem support_smul_subset_left [Zero M] [Zero β] [SMulWithZero M β] (f : α → M) (g : α → β) :
    support (f • g) ⊆ support f := fun x hfg hf => hfg <| by rw [Pi.smul_apply', hf, zero_smul]

theorem support_const_smul_of_ne_zero [Semiring R] [AddCommMonoid M] [Module R M]
    [NoZeroSMulDivisors R M] (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun x => by simp only [hc, mem_support, Pi.smul_apply, Ne.def, smul_eq_zero, false_or_iff]

@[simp]
theorem support_inv [GroupWithZero G₀] (f : α → G₀) : (support fun x => (f x)⁻¹) = support f :=
  Set.ext fun _ => not_congr inv_eq_zero

@[simp]
theorem support_div [GroupWithZero G₀] (f g : α → G₀) :
    (support fun x => f x / g x) = support f ∩ support g := by simp [div_eq_mul_inv]

@[to_additive]
theorem mulSupport_prod [CommMonoid M] (s : Finset α) (f : α → β → M) :
    (mulSupport fun x => ∏ i in s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) := by
  rw [mulSupport_subset_iff']
  simp only [mem_iUnion, not_exists, nmem_mulSupport]
  exact fun x => Finset.prod_eq_one

theorem support_prod_subset [CommMonoidWithZero A] (s : Finset α) (f : α → β → A) :
    (support fun x => ∏ i in s, f i x) ⊆ ⋂ i ∈ s, support (f i) := fun _ hx =>
  mem_iInter₂.2 fun _ hi H => hx <| Finset.prod_eq_zero hi H

theorem support_prod [CommMonoidWithZero A] [NoZeroDivisors A] [Nontrivial A] (s : Finset α)
    (f : α → β → A) : (support fun x => ∏ i in s, f i x) = ⋂ i ∈ s, support (f i) :=
  Set.ext fun x => by
    simp [support, Ne.def, Finset.prod_eq_zero_iff, mem_setOf_eq, Set.mem_iInter, not_exists]

theorem mulSupport_one_add [One R] [AddLeftCancelMonoid R] (f : α → R) :
    (mulSupport fun x => 1 + f x) = support f :=
  Set.ext fun _ => not_congr add_right_eq_self

theorem mulSupport_one_add' [One R] [AddLeftCancelMonoid R] (f : α → R) :
    mulSupport (1 + f) = support f :=
  mulSupport_one_add f

theorem mulSupport_add_one [One R] [AddRightCancelMonoid R] (f : α → R) :
    (mulSupport fun x => f x + 1) = support f :=
  Set.ext fun _ => not_congr add_left_eq_self

theorem mulSupport_add_one' [One R] [AddRightCancelMonoid R] (f : α → R) :
    mulSupport (f + 1) = support f :=
  mulSupport_add_one f

theorem mulSupport_one_sub' [One R] [AddGroup R] (f : α → R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg, mulSupport_one_add', support_neg']

theorem mulSupport_one_sub [One R] [AddGroup R] (f : α → R) :
    (mulSupport fun x => 1 - f x) = support f :=
  mulSupport_one_sub' f

end Function

namespace Set

open Function

variable {α β M : Type*} [One M] {f : α → M}

@[to_additive]
theorem image_inter_mulSupport_eq {s : Set β} {g : β → α} :
    g '' s ∩ mulSupport f = g '' (s ∩ mulSupport (f ∘ g)) := by
  rw [mulSupport_comp_eq_preimage f g, image_inter_preimage]

end Set

namespace Pi

variable {A : Type*} {B : Type*} [DecidableEq A] [One B] {a : A} {b : B}

open Function

@[to_additive]
theorem mulSupport_mulSingle_subset : mulSupport (mulSingle a b) ⊆ {a} := fun _ hx =>
  by_contra fun hx' => hx <| mulSingle_eq_of_ne hx' _

@[to_additive]
theorem mulSupport_mulSingle_one : mulSupport (mulSingle a (1 : B)) = ∅ := by simp

@[to_additive (attr := simp)]
theorem mulSupport_mulSingle_of_ne (h : b ≠ 1) : mulSupport (mulSingle a b) = {a} :=
  mulSupport_mulSingle_subset.antisymm fun x (hx : x = a) => by
    rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]
theorem mulSupport_mulSingle [DecidableEq B] :
    mulSupport (mulSingle a b) = if b = 1 then ∅ else {a} := by split_ifs with h <;> simp [h]

@[to_additive]
theorem mulSupport_mulSingle_disjoint {b' : B} (hb : b ≠ 1) (hb' : b' ≠ 1) {i j : A} :
    Disjoint (mulSupport (mulSingle i b)) (mulSupport (mulSingle j b')) ↔ i ≠ j := by
  rw [mulSupport_mulSingle_of_ne hb, mulSupport_mulSingle_of_ne hb', disjoint_singleton]

end Pi
