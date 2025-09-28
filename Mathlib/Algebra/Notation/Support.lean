/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Prod
import Mathlib.Data.Set.Image

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/

assert_not_exists Monoid CompleteLattice

open Function Set

variable {ι κ M N P : Type*}

namespace Function
variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

/-- `mulSupport` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive /-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/]
def mulSupport (f : ι → M) : Set ι := {x | f x ≠ 1}

@[to_additive]
lemma mulSupport_eq_preimage (f : ι → M) : mulSupport f = f ⁻¹' {1}ᶜ := rfl

@[to_additive]
lemma notMem_mulSupport : x ∉ mulSupport f ↔ f x = 1 := not_not

@[deprecated (since := "2025-05-24")] alias nmem_support := notMem_support

@[to_additive existing, deprecated (since := "2025-05-24")]
alias nmem_mulSupport := notMem_mulSupport

@[to_additive]
lemma compl_mulSupport : (mulSupport f)ᶜ = {x | f x = 1} := ext fun _ ↦ notMem_mulSupport

@[to_additive (attr := simp)]
lemma mem_mulSupport : x ∈ mulSupport f ↔ f x ≠ 1 := .rfl

@[to_additive (attr := simp)]
lemma mulSupport_subset_iff : mulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s := .rfl

@[to_additive]
lemma mulSupport_subset_iff' : mulSupport f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
  forall_congr' fun _ ↦ not_imp_comm

@[to_additive]
lemma mulSupport_eq_iff : mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp +contextual only [Set.ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]
lemma ext_iff_mulSupport : f = g ↔ f.mulSupport = g.mulSupport ∧ ∀ x ∈ f.mulSupport, f x = g x where
  mp h := h ▸ ⟨rfl, fun _ _ ↦ rfl⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ funext fun x ↦ by
    if hx : x ∈ f.mulSupport then exact h₂ x hx
    else rw [notMem_mulSupport.1 hx, notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

@[to_additive]
lemma mulSupport_update_of_ne_one [DecidableEq ι] (f : ι → M) (x : ι) {y : M} (hy : y ≠ 1) :
    mulSupport (update f x y) = insert x (mulSupport f) := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
lemma mulSupport_update_one [DecidableEq ι] (f : ι → M) (x : ι) :
    mulSupport (update f x 1) = mulSupport f \ {x} := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
lemma mulSupport_update_eq_ite [DecidableEq ι] [DecidableEq M] (f : ι → M) (x : ι) (y : M) :
    mulSupport (update f x y) = if y = 1 then mulSupport f \ {x} else insert x (mulSupport f) := by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]
lemma mulSupport_extend_one_subset {f : ι → κ} {g : ι → N} :
    mulSupport (f.extend g 1) ⊆ f '' mulSupport g :=
  mulSupport_subset_iff'.mpr fun x hfg ↦ by
    by_cases hf : ∃ a, f a = x
    · rw [extend, dif_pos hf, ← notMem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg ↦ hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]
lemma mulSupport_extend_one {f : ι → κ} {g : ι → N} (hf : f.Injective) :
    mulSupport (f.extend g 1) = f '' mulSupport g :=
  mulSupport_extend_one_subset.antisymm <| by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]
lemma mulSupport_disjoint_iff : Disjoint (mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]
lemma disjoint_mulSupport_iff : Disjoint s (mulSupport f) ↔ EqOn f 1 s := by
  rw [disjoint_comm, mulSupport_disjoint_iff]

@[to_additive (attr := simp)]
lemma mulSupport_eq_empty_iff : mulSupport f = ∅ ↔ f = 1 := by
  rw [← subset_empty_iff, mulSupport_subset_iff', funext_iff]
  simp

@[to_additive (attr := simp)]
lemma mulSupport_nonempty_iff : (mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne, mulSupport_eq_empty_iff]

@[to_additive]
lemma range_subset_insert_image_mulSupport (f : ι → M) :
    range f ⊆ insert 1 (f '' mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using
    fun x (hx : x ∈ mulSupport f) ↦ mem_image_of_mem f hx

@[to_additive]
lemma range_eq_image_or_of_mulSupport_subset {k : Set ι} (h : mulSupport f ⊆ k) :
    range f = f '' k ∨ range f = insert 1 (f '' k) := by
  have : range f ⊆ insert 1 (f '' k) :=
    (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

@[to_additive (attr := simp)]
lemma mulSupport_one : mulSupport (1 : ι → M) = ∅ := mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]
lemma mulSupport_fun_one : mulSupport (fun _ ↦ 1 : ι → M) = ∅ := mulSupport_one

@[deprecated (since := "2025-07-31")] alias support_zero' := support_zero
@[deprecated (since := "2025-07-31")] alias mulSupport_one' := mulSupport_one

@[to_additive]
lemma mulSupport_const {c : M} (hc : c ≠ 1) : (mulSupport fun _ : ι ↦ c) = Set.univ := by
  ext x; simp [hc]

@[to_additive]
lemma mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : ι → M) (g : ι → N) :
    mulSupport (fun x ↦ op (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := fun x hx ↦
  not_or_of_imp fun hf hg ↦ hx <| by simp only [hf, hg, op1]

@[to_additive]
lemma mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : ι → M) :
    mulSupport (g ∘ f) ⊆ mulSupport f := fun x ↦ mt fun h ↦ by simp only [(· ∘ ·), *]

@[to_additive]
lemma mulSupport_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : ι → M) :
    mulSupport f ⊆ mulSupport (g ∘ f) := fun _ ↦ mt hg

@[to_additive]
lemma mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : ι → M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun _ ↦ not_congr hg

@[to_additive]
lemma mulSupport_comp_eq_of_range_subset {g : M → N} {f : ι → M}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun x ↦ not_congr <| by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]
lemma mulSupport_comp_eq_preimage (g : κ → M) (f : ι → κ) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g := rfl

@[to_additive support_prodMk]
lemma mulSupport_prodMk (f : ι → M) (g : ι → N) :
    mulSupport (fun x ↦ (f x, g x)) = mulSupport f ∪ mulSupport g :=
  Set.ext fun x ↦ by
    simp only [mulSupport, not_and_or, mem_union, mem_setOf_eq, Prod.mk_eq_one, Ne]

@[to_additive support_prodMk']
lemma mulSupport_prodMk' (f : ι → M × N) :
    mulSupport f = (mulSupport fun x ↦ (f x).1) ∪ mulSupport fun x ↦ (f x).2 := by
  simp only [← mulSupport_prodMk]

@[deprecated (since := "2025-07-31")] alias support_prod_mk := support_prodMk
@[deprecated (since := "2025-07-31")] alias mulSupport_prod_mk := mulSupport_prodMk
@[deprecated (since := "2025-07-31")] alias support_prod_mk' := support_prodMk'
@[deprecated (since := "2025-07-31")] alias mulSupport_prod_mk' := mulSupport_prodMk'

@[to_additive]
lemma mulSupport_along_fiber_subset (f : ι × κ → M) (i : ι) :
    (mulSupport fun j ↦ f (i, j)) ⊆ (mulSupport f).image Prod.snd :=
  fun j hj ↦ ⟨(i, j), by simpa using hj⟩

@[to_additive]
lemma mulSupport_curry (f : ι × κ → M) : (mulSupport f.curry) = (mulSupport f).image Prod.fst := by
  simp [mulSupport, funext_iff, image]

@[to_additive]
lemma mulSupport_fun_curry (f : ι × κ → M) :
    mulSupport (fun i j ↦ f (i, j)) = (mulSupport f).image Prod.fst := mulSupport_curry f

@[deprecated (since := "2025-07-31")] alias support_curry' := support_fun_curry
@[deprecated (since := "2025-07-31")] alias mulSupport_curry' := mulSupport_fun_curry

end Function

namespace Set
variable [One M] {f : ι → M} {s : Set κ} {g : κ → ι}

@[to_additive]
lemma image_inter_mulSupport_eq : g '' s ∩ mulSupport f = g '' (s ∩ mulSupport (f ∘ g)) := by
  rw [mulSupport_comp_eq_preimage f g, image_inter_preimage]

end Set

namespace Pi
variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

@[to_additive]
lemma mulSupport_mulSingle_subset : mulSupport (mulSingle i a) ⊆ {i} := fun _ hx ↦
  by_contra fun hx' ↦ hx <| mulSingle_eq_of_ne hx' _

@[to_additive]
lemma mulSupport_mulSingle_one : mulSupport (mulSingle i (1 : M)) = ∅ := by simp

@[to_additive (attr := simp)]
lemma mulSupport_mulSingle_of_ne (h : a ≠ 1) : mulSupport (mulSingle i a) = {i} :=
  mulSupport_mulSingle_subset.antisymm fun x hx ↦ by rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]
lemma mulSupport_mulSingle [DecidableEq M] :
    mulSupport (mulSingle i a) = if a = 1 then ∅ else {i} := by split_ifs with h <;> simp [h]

@[to_additive]
lemma mulSupport_mulSingle_disjoint (ha : a ≠ 1) (hb : b ≠ 1) :
    Disjoint (mulSupport (mulSingle i a)) (mulSupport (mulSingle j b)) ↔ i ≠ j := by
  rw [mulSupport_mulSingle_of_ne ha, mulSupport_mulSingle_of_ne hb, disjoint_singleton]

end Pi
