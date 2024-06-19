/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Order.Cover

#align_import algebra.support from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/

assert_not_exists MonoidWithZero

open Set

namespace Function

variable {α β A B M N P G : Type*}

section One
variable [One M] [One N] [One P]

/-- `mulSupport` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive "`support` of a function is the set of points `x` such that `f x ≠ 0`."]
def mulSupport (f : α → M) : Set α := {x | f x ≠ 1}
#align function.mul_support Function.mulSupport
#align function.support Function.support

@[to_additive]
theorem mulSupport_eq_preimage (f : α → M) : mulSupport f = f ⁻¹' {1}ᶜ :=
  rfl
#align function.mul_support_eq_preimage Function.mulSupport_eq_preimage
#align function.support_eq_preimage Function.support_eq_preimage

@[to_additive]
theorem nmem_mulSupport {f : α → M} {x : α} : x ∉ mulSupport f ↔ f x = 1 :=
  not_not
#align function.nmem_mul_support Function.nmem_mulSupport
#align function.nmem_support Function.nmem_support

@[to_additive]
theorem compl_mulSupport {f : α → M} : (mulSupport f)ᶜ = { x | f x = 1 } :=
  ext fun _ => nmem_mulSupport
#align function.compl_mul_support Function.compl_mulSupport
#align function.compl_support Function.compl_support

@[to_additive (attr := simp)]
theorem mem_mulSupport {f : α → M} {x : α} : x ∈ mulSupport f ↔ f x ≠ 1 :=
  Iff.rfl
#align function.mem_mul_support Function.mem_mulSupport
#align function.mem_support Function.mem_support

@[to_additive (attr := simp)]
theorem mulSupport_subset_iff {f : α → M} {s : Set α} : mulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl
#align function.mul_support_subset_iff Function.mulSupport_subset_iff
#align function.support_subset_iff Function.support_subset_iff

@[to_additive]
theorem mulSupport_subset_iff' {f : α → M} {s : Set α} :
    mulSupport f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
  forall_congr' fun _ => not_imp_comm
#align function.mul_support_subset_iff' Function.mulSupport_subset_iff'
#align function.support_subset_iff' Function.support_subset_iff'

@[to_additive]
theorem mulSupport_eq_iff {f : α → M} {s : Set α} :
    mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp (config := { contextual := true }) only [ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]
#align function.mul_support_eq_iff Function.mulSupport_eq_iff
#align function.support_eq_iff Function.support_eq_iff

@[to_additive]
theorem ext_iff_mulSupport {f g : α → M} :
    f = g ↔ f.mulSupport = g.mulSupport ∧ ∀ x ∈ f.mulSupport, f x = g x :=
  ⟨fun h ↦ h ▸ ⟨rfl, fun _ _ ↦ rfl⟩, fun ⟨h₁, h₂⟩ ↦ funext fun x ↦ by
    if hx : x ∈ f.mulSupport then exact h₂ x hx
    else rw [nmem_mulSupport.1 hx, nmem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]⟩

@[to_additive]
theorem mulSupport_update_of_ne_one [DecidableEq α] (f : α → M) (x : α) {y : M} (hy : y ≠ 1) :
    mulSupport (update f x y) = insert x (mulSupport f) := by
  ext a; rcases eq_or_ne a x with rfl | hne <;> simp [*]

@[to_additive]
theorem mulSupport_update_one [DecidableEq α] (f : α → M) (x : α) :
    mulSupport (update f x 1) = mulSupport f \ {x} := by
  ext a; rcases eq_or_ne a x with rfl | hne <;> simp [*]

@[to_additive]
theorem mulSupport_update_eq_ite [DecidableEq α] [DecidableEq M] (f : α → M) (x : α) (y : M) :
    mulSupport (update f x y) = if y = 1 then mulSupport f \ {x} else insert x (mulSupport f) := by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]
theorem mulSupport_extend_one_subset {f : α → M} {g : α → N} :
    mulSupport (f.extend g 1) ⊆ f '' mulSupport g :=
  mulSupport_subset_iff'.mpr fun x hfg ↦ by
    by_cases hf : ∃ a, f a = x
    · rw [extend, dif_pos hf, ← nmem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg ↦ hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]
theorem mulSupport_extend_one {f : α → M} {g : α → N} (hf : f.Injective) :
    mulSupport (f.extend g 1) = f '' mulSupport g :=
  mulSupport_extend_one_subset.antisymm <| by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]
theorem mulSupport_disjoint_iff {f : α → M} {s : Set α} :
    Disjoint (mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', not_mem_compl_iff, EqOn,
    Pi.one_apply]
#align function.mul_support_disjoint_iff Function.mulSupport_disjoint_iff
#align function.support_disjoint_iff Function.support_disjoint_iff

@[to_additive]
theorem disjoint_mulSupport_iff {f : α → M} {s : Set α} :
    Disjoint s (mulSupport f) ↔ EqOn f 1 s := by
  rw [disjoint_comm, mulSupport_disjoint_iff]
#align function.disjoint_mul_support_iff Function.disjoint_mulSupport_iff
#align function.disjoint_support_iff Function.disjoint_support_iff

@[to_additive (attr := simp)]
theorem mulSupport_eq_empty_iff {f : α → M} : mulSupport f = ∅ ↔ f = 1 := by
  -- Adaptation note: This used to be `simp_rw` rather than `rw`,
  -- but this broke `to_additive` as of `nightly-2024-03-07`
  rw [← subset_empty_iff, mulSupport_subset_iff', funext_iff]
  simp
#align function.mul_support_eq_empty_iff Function.mulSupport_eq_empty_iff
#align function.support_eq_empty_iff Function.support_eq_empty_iff

@[to_additive (attr := simp)]
theorem mulSupport_nonempty_iff {f : α → M} : (mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne, mulSupport_eq_empty_iff]
#align function.mul_support_nonempty_iff Function.mulSupport_nonempty_iff
#align function.support_nonempty_iff Function.support_nonempty_iff

@[to_additive]
theorem range_subset_insert_image_mulSupport (f : α → M) :
    range f ⊆ insert 1 (f '' mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using
    fun x (hx : x ∈ mulSupport f) => mem_image_of_mem f hx
#align function.range_subset_insert_image_mul_support Function.range_subset_insert_image_mulSupport
#align function.range_subset_insert_image_support Function.range_subset_insert_image_support

@[to_additive]
lemma range_eq_image_or_of_mulSupport_subset {f : α → M} {k : Set α} (h : mulSupport f ⊆ k) :
    range f = f '' k ∨ range f = insert 1 (f '' k) := by
  apply (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _)
  exact (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_subset f h))

@[to_additive (attr := simp)]
theorem mulSupport_one' : mulSupport (1 : α → M) = ∅ :=
  mulSupport_eq_empty_iff.2 rfl
#align function.mul_support_one' Function.mulSupport_one'
#align function.support_zero' Function.support_zero'

@[to_additive (attr := simp)]
theorem mulSupport_one : (mulSupport fun _ : α => (1 : M)) = ∅ :=
  mulSupport_one'
#align function.mul_support_one Function.mulSupport_one
#align function.support_zero Function.support_zero

@[to_additive]
theorem mulSupport_const {c : M} (hc : c ≠ 1) : (mulSupport fun _ : α => c) = Set.univ := by
  ext x
  simp [hc]
#align function.mul_support_const Function.mulSupport_const
#align function.support_const Function.support_const

@[to_additive]
theorem mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (mulSupport fun x => op (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := fun x hx =>
  not_or_of_imp fun hf hg => hx <| by simp only [hf, hg, op1]
#align function.mul_support_binop_subset Function.mulSupport_binop_subset
#align function.support_binop_subset Function.support_binop_subset

@[to_additive]
theorem mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) :
    mulSupport (g ∘ f) ⊆ mulSupport f := fun x => mt fun h => by simp only [(· ∘ ·), *]
#align function.mul_support_comp_subset Function.mulSupport_comp_subset
#align function.support_comp_subset Function.support_comp_subset

@[to_additive]
theorem mulSupport_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    mulSupport f ⊆ mulSupport (g ∘ f) := fun _ => mt hg
#align function.mul_support_subset_comp Function.mulSupport_subset_comp
#align function.support_subset_comp Function.support_subset_comp

@[to_additive]
theorem mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun _ => not_congr hg
#align function.mul_support_comp_eq Function.mulSupport_comp_eq
#align function.support_comp_eq Function.support_comp_eq

@[to_additive]
theorem mulSupport_comp_eq_of_range_subset {g : M → N} {f : α → M}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun x ↦ not_congr <| by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]
theorem mulSupport_comp_eq_preimage (g : β → M) (f : α → β) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g :=
  rfl
#align function.mul_support_comp_eq_preimage Function.mulSupport_comp_eq_preimage
#align function.support_comp_eq_preimage Function.support_comp_eq_preimage

@[to_additive support_prod_mk]
theorem mulSupport_prod_mk (f : α → M) (g : α → N) :
    (mulSupport fun x => (f x, g x)) = mulSupport f ∪ mulSupport g :=
  Set.ext fun x => by
    simp only [mulSupport, not_and_or, mem_union, mem_setOf_eq, Prod.mk_eq_one, Ne]
#align function.mul_support_prod_mk Function.mulSupport_prod_mk
#align function.support_prod_mk Function.support_prod_mk

@[to_additive support_prod_mk']
theorem mulSupport_prod_mk' (f : α → M × N) :
    mulSupport f = (mulSupport fun x => (f x).1) ∪ mulSupport fun x => (f x).2 := by
  simp only [← mulSupport_prod_mk]
#align function.mul_support_prod_mk' Function.mulSupport_prod_mk'
#align function.support_prod_mk' Function.support_prod_mk'

@[to_additive]
theorem mulSupport_along_fiber_subset (f : α × β → M) (a : α) :
    (mulSupport fun b => f (a, b)) ⊆ (mulSupport f).image Prod.snd :=
  fun x hx => ⟨(a, x), by simpa using hx⟩
#align function.mul_support_along_fiber_subset Function.mulSupport_along_fiber_subset
#align function.support_along_fiber_subset Function.support_along_fiber_subset

@[to_additive]
theorem mulSupport_curry (f : α × β → M) :
    (mulSupport f.curry) = (mulSupport f).image Prod.fst := by
  simp [mulSupport, funext_iff, image]

@[to_additive]
theorem mulSupport_curry' (f : α × β → M) :
    (mulSupport fun a b ↦ f (a, b)) = (mulSupport f).image Prod.fst :=
  mulSupport_curry f

end One

@[to_additive]
theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x => f x * g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g
#align function.mul_support_mul Function.mulSupport_mul
#align function.support_add Function.support_add

@[to_additive]
theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction' n with n hfn
  · simp [pow_zero, mulSupport_one]
  · simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)
#align function.mul_support_pow Function.mulSupport_pow
#align function.support_nsmul Function.support_nsmul

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[to_additive (attr := simp)]
theorem mulSupport_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one
#align function.mul_support_inv Function.mulSupport_inv
#align function.support_neg Function.support_neg

@[to_additive (attr := simp)]
theorem mulSupport_inv' : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_inv f
#align function.mul_support_inv' Function.mulSupport_inv'
#align function.support_neg' Function.support_neg'

@[to_additive]
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g
#align function.mul_support_mul_inv Function.mulSupport_mul_inv
#align function.support_add_neg Function.support_add_neg

@[to_additive]
theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g
#align function.mul_support_div Function.mulSupport_div
#align function.support_sub Function.support_sub

end DivisionMonoid

end Function

namespace Set

open Function

variable {α β M : Type*} [One M] {f : α → M}

@[to_additive]
theorem image_inter_mulSupport_eq {s : Set β} {g : β → α} :
    g '' s ∩ mulSupport f = g '' (s ∩ mulSupport (f ∘ g)) := by
  rw [mulSupport_comp_eq_preimage f g, image_inter_preimage]
#align set.image_inter_mul_support_eq Set.image_inter_mulSupport_eq
#align set.image_inter_support_eq Set.image_inter_support_eq

end Set

namespace Pi

variable {A : Type*} {B : Type*} [DecidableEq A] [One B] {a : A} {b : B}

open Function

@[to_additive]
theorem mulSupport_mulSingle_subset : mulSupport (mulSingle a b) ⊆ {a} := fun _ hx =>
  by_contra fun hx' => hx <| mulSingle_eq_of_ne hx' _
#align pi.mul_support_mul_single_subset Pi.mulSupport_mulSingle_subset
#align pi.support_single_subset Pi.support_single_subset

@[to_additive]
theorem mulSupport_mulSingle_one : mulSupport (mulSingle a (1 : B)) = ∅ := by simp
#align pi.mul_support_mul_single_one Pi.mulSupport_mulSingle_one
#align pi.support_single_zero Pi.support_single_zero

@[to_additive (attr := simp)]
theorem mulSupport_mulSingle_of_ne (h : b ≠ 1) : mulSupport (mulSingle a b) = {a} :=
  mulSupport_mulSingle_subset.antisymm fun x (hx : x = a) => by
    rwa [mem_mulSupport, hx, mulSingle_eq_same]
#align pi.mul_support_mul_single_of_ne Pi.mulSupport_mulSingle_of_ne
#align pi.support_single_of_ne Pi.support_single_of_ne

@[to_additive]
theorem mulSupport_mulSingle [DecidableEq B] :
    mulSupport (mulSingle a b) = if b = 1 then ∅ else {a} := by split_ifs with h <;> simp [h]
#align pi.mul_support_mul_single Pi.mulSupport_mulSingle
#align pi.support_single Pi.support_single

@[to_additive]
theorem mulSupport_mulSingle_disjoint {b' : B} (hb : b ≠ 1) (hb' : b' ≠ 1) {i j : A} :
    Disjoint (mulSupport (mulSingle i b)) (mulSupport (mulSingle j b')) ↔ i ≠ j := by
  rw [mulSupport_mulSingle_of_ne hb, mulSupport_mulSingle_of_ne hb', disjoint_singleton]
#align pi.mul_support_mul_single_disjoint Pi.mulSupport_mulSingle_disjoint
#align pi.support_single_disjoint Pi.support_single_disjoint

end Pi
