/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.NoncommProd

#align_import group_theory.submonoid.membership from "leanprover-community/mathlib"@"e655e4ea5c6d02854696f97494997ba4c31be802"

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_iSup_of_directed`, `coe_iSup_of_directed`, `mem_sSup_of_directedOn`,
  `coe_sSup_of_directedOn`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
submonoid, submonoids
-/

open BigOperators

variable {M A B : Type*}

section Assoc

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {S : B}

namespace SubmonoidClass

@[to_additive (attr := norm_cast, simp)]
theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod :=
  (SubmonoidClass.subtype S : _ →* M).map_list_prod l
#align submonoid_class.coe_list_prod SubmonoidClass.coe_list_prod
#align add_submonoid_class.coe_list_sum AddSubmonoidClass.coe_list_sum

@[to_additive (attr := norm_cast, simp)]
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m
#align submonoid_class.coe_multiset_prod SubmonoidClass.coe_multiset_prod
#align add_submonoid_class.coe_multiset_sum AddSubmonoidClass.coe_multiset_sum

@[to_additive (attr := norm_cast)] --Porting note: removed `simp`, `simp` can prove it
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  (SubmonoidClass.subtype S : _ →* M).map_prod f s
#align submonoid_class.coe_finset_prod SubmonoidClass.coe_finset_prod
#align add_submonoid_class.coe_finset_sum AddSubmonoidClass.coe_finset_sum

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S := by
  lift l to List S using hl
  -- ⊢ List.prod (List.map Subtype.val l) ∈ S
  rw [← coe_list_prod]
  -- ⊢ ↑(List.prod l) ∈ S
  exact l.prod.coe_prop
  -- 🎉 no goals
#align list_prod_mem list_prod_mem
#align list_sum_mem list_sum_mem

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := by
  lift m to Multiset S using hm
  -- ⊢ Multiset.prod (Multiset.map Subtype.val m) ∈ S
  rw [← coe_multiset_prod]
  -- ⊢ ↑(Multiset.prod m) ∈ S
  exact m.prod.coe_prop
  -- 🎉 no goals
#align multiset_prod_mem multiset_prod_mem
#align multiset_sum_mem multiset_sum_mem

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`."]
theorem prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align prod_mem prod_mem
#align sum_mem sum_mem

namespace Submonoid

variable (s : Submonoid M)

@[to_additive (attr := norm_cast)] --Porting note: removed `simp`, `simp` can prove it
theorem coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod :=
  s.subtype.map_list_prod l
#align submonoid.coe_list_prod Submonoid.coe_list_prod
#align add_submonoid.coe_list_sum AddSubmonoid.coe_list_sum

@[to_additive (attr := norm_cast)] --Porting note: removed `simp`, `simp` can prove it
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  S.subtype.map_multiset_prod m
#align submonoid.coe_multiset_prod Submonoid.coe_multiset_prod
#align add_submonoid.coe_multiset_sum AddSubmonoid.coe_multiset_sum

@[to_additive (attr := norm_cast, simp)]
theorem coe_finset_prod {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  S.subtype.map_prod f s
#align submonoid.coe_finset_prod Submonoid.coe_finset_prod
#align add_submonoid.coe_finset_sum AddSubmonoid.coe_finset_sum

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.prod ∈ s := by
  lift l to List s using hl
  -- ⊢ List.prod (List.map Subtype.val l) ∈ s
  rw [← coe_list_prod]
  -- ⊢ ↑(List.prod l) ∈ s
  exact l.prod.coe_prop
  -- 🎉 no goals
#align submonoid.list_prod_mem Submonoid.list_prod_mem
#align add_submonoid.list_sum_mem AddSubmonoid.list_sum_mem

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := by
  lift m to Multiset S using hm
  -- ⊢ Multiset.prod (Multiset.map Subtype.val m) ∈ S
  rw [← coe_multiset_prod]
  -- ⊢ ↑(Multiset.prod m) ∈ S
  exact m.prod.coe_prop
  -- 🎉 no goals
#align submonoid.multiset_prod_mem Submonoid.multiset_prod_mem
#align add_submonoid.multiset_sum_mem AddSubmonoid.multiset_sum_mem

@[to_additive]
theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction' m using Quotient.inductionOn with l
  -- ⊢ Multiset.noncommProd (Quotient.mk (List.isSetoid M) l) comm ∈ S
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  -- ⊢ List.prod l ∈ S
  exact Submonoid.list_prod_mem _ h
  -- 🎉 no goals
#align submonoid.multiset_noncomm_prod_mem Submonoid.multiset_noncommProd_mem
#align add_submonoid.multiset_noncomm_sum_mem AddSubmonoid.multiset_noncommSum_mem

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`."]
theorem prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align submonoid.prod_mem Submonoid.prod_mem
#align add_submonoid.sum_mem AddSubmonoid.sum_mem

@[to_additive]
theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply multiset_noncommProd_mem
  -- ⊢ ∀ (x : M), x ∈ Multiset.map f t.val → x ∈ S
  intro y
  -- ⊢ y ∈ Multiset.map f t.val → y ∈ S
  rw [Multiset.mem_map]
  -- ⊢ (∃ a, a ∈ t.val ∧ f a = y) → y ∈ S
  rintro ⟨x, ⟨hx, rfl⟩⟩
  -- ⊢ f x ∈ S
  exact h x hx
  -- 🎉 no goals
#align submonoid.noncomm_prod_mem Submonoid.noncommProd_mem
#align add_submonoid.noncomm_sum_mem AddSubmonoid.noncommSum_mem

end Submonoid

end Assoc

section NonAssoc

variable [MulOneClass M]

open Set

namespace Submonoid

-- TODO: this section can be generalized to `[SubmonoidClass B M] [CompleteLattice B]`
-- such that `CompleteLattice.LE` coincides with `SetLike.LE`
@[to_additive]
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S)
    {x : M} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  -- ⊢ x ∈ ⨆ (i : ι), S i → ∃ i, x ∈ S i
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine' fun hx => closure_induction hx (fun _ => mem_iUnion.1) _ _
  -- ⊢ ∃ i, 1 ∈ S i
  · exact hι.elim fun i => ⟨i, (S i).one_mem⟩
    -- 🎉 no goals
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    -- ⊢ ∃ i, x * y ∈ S i
    rcases hS i j with ⟨k, hki, hkj⟩
    -- ⊢ ∃ i, x * y ∈ S i
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
    -- 🎉 no goals
#align submonoid.mem_supr_of_directed Submonoid.mem_iSup_of_directed
#align add_submonoid.mem_supr_of_directed AddSubmonoid.mem_iSup_of_directed

@[to_additive]
theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
                      -- 🎉 no goals
#align submonoid.coe_supr_of_directed Submonoid.coe_iSup_of_directed
#align add_submonoid.coe_supr_of_directed AddSubmonoid.coe_iSup_of_directed

@[to_additive]
theorem mem_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  -- ⊢ x ∈ sSup S ↔ ∃ s, s ∈ S ∧ x ∈ s
  simp [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk]
  -- 🎉 no goals
#align submonoid.mem_Sup_of_directed_on Submonoid.mem_sSup_of_directedOn
#align add_submonoid.mem_Sup_of_directed_on AddSubmonoid.mem_sSup_of_directedOn

@[to_additive]
theorem coe_sSup_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
                      -- 🎉 no goals
#align submonoid.coe_Sup_of_directed_on Submonoid.coe_sSup_of_directedOn
#align add_submonoid.coe_Sup_of_directed_on AddSubmonoid.coe_sSup_of_directedOn

@[to_additive]
theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ S ≤ S ⊔ T
  exact le_sup_left
  -- 🎉 no goals
#align submonoid.mem_sup_left Submonoid.mem_sup_left
#align add_submonoid.mem_sup_left AddSubmonoid.mem_sup_left

@[to_additive]
theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  rw [←SetLike.le_def]
  -- ⊢ T ≤ S ⊔ T
  exact le_sup_right
  -- 🎉 no goals
#align submonoid.mem_sup_right Submonoid.mem_sup_right
#align add_submonoid.mem_sup_right AddSubmonoid.mem_sup_right

@[to_additive]
theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align submonoid.mul_mem_sup Submonoid.mul_mem_sup
#align add_submonoid.add_mem_sup AddSubmonoid.add_mem_sup

@[to_additive]
theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Submonoid M} (i : ι) :
    ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  rw [←SetLike.le_def]
  -- ⊢ S i ≤ iSup S
  exact le_iSup _ _
  -- 🎉 no goals
#align submonoid.mem_supr_of_mem Submonoid.mem_iSup_of_mem
#align add_submonoid.mem_supr_of_mem AddSubmonoid.mem_iSup_of_mem

@[to_additive]
theorem mem_sSup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  rw [←SetLike.le_def]
  -- ⊢ s ≤ sSup S
  exact le_sSup hs
  -- 🎉 no goals
#align submonoid.mem_Sup_of_mem Submonoid.mem_sSup_of_mem
#align add_submonoid.mem_Sup_of_mem AddSubmonoid.mem_sSup_of_mem

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[to_additive (attr := elab_as_elim)
      " An induction principle for elements of `⨆ i, S i`.
      If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
      then it holds for all elements of the supremum of `S`. "]
theorem iSup_induction {ι : Sort*} (S : ι → Submonoid M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
    (hp : ∀ (i), ∀ x ∈ S i, C x) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C x := by
  rw [iSup_eq_closure] at hx
  -- ⊢ C x
  refine closure_induction hx (fun x hx => ?_) h1 hmul
  -- ⊢ C x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  -- ⊢ C x
  exact hp _ _ hi
  -- 🎉 no goals
#align submonoid.supr_induction Submonoid.iSup_induction
#align add_submonoid.supr_induction AddSubmonoid.iSup_induction

/-- A dependent version of `Submonoid.iSup_induction`. -/
@[to_additive (attr := elab_as_elim) "A dependent version of `AddSubmonoid.iSup_induction`. "]
theorem iSup_induction' {ι : Sort*} (S : ι → Submonoid M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ (x) (hxS : x ∈ S i), C x (mem_iSup_of_mem i hxS)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : C x hx := by
  refine' Exists.elim (_ : ∃ Hx, C x Hx) fun (hx : x ∈ ⨆ i, S i) (hc : C x hx) => hc
  -- ⊢ ∃ Hx, C x Hx
  refine' @iSup_induction _ _ ι S (fun m => ∃ hm, C m hm) _ hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
    -- 🎉 no goals
  · exact ⟨_, h1⟩
    -- 🎉 no goals
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    -- ⊢ ∃ hm, C (x * y) hm
    refine' ⟨_, hmul _ _ _ _ Cx Cy⟩
    -- 🎉 no goals
#align submonoid.supr_induction' Submonoid.iSup_induction'
#align add_submonoid.supr_induction' AddSubmonoid.iSup_induction'

end Submonoid

end NonAssoc

namespace FreeMonoid

variable {α : Type*}

open Submonoid

@[to_additive]
theorem closure_range_of : closure (Set.range <| @of α) = ⊤ :=
  eq_top_iff.2 fun x _ =>
    FreeMonoid.recOn x (one_mem _) fun _x _xs hxs =>
      mul_mem (subset_closure <| Set.mem_range_self _) hxs
#align free_monoid.closure_range_of FreeMonoid.closure_range_of
#align free_add_monoid.closure_range_of FreeAddMonoid.closure_range_of

end FreeMonoid

namespace Submonoid

variable [Monoid M]

open MonoidHom

theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = mrange (powersHom M x) :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_one x⟩) fun _ ⟨_, hn⟩ =>
    hn ▸ pow_mem (subset_closure <| Set.mem_singleton _) _
#align submonoid.closure_singleton_eq Submonoid.closure_singleton_eq

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [closure_singleton_eq, mem_mrange]; rfl
  -- ⊢ (∃ x_1, ↑(↑(powersHom M) x) x_1 = y) ↔ ∃ n, x ^ n = y
                                         -- 🎉 no goals
#align submonoid.mem_closure_singleton Submonoid.mem_closure_singleton

theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) :=
  mem_closure_singleton.2 ⟨1, pow_one y⟩
#align submonoid.mem_closure_singleton_self Submonoid.mem_closure_singleton_self

theorem closure_singleton_one : closure ({1} : Set M) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton]
  -- 🎉 no goals
#align submonoid.closure_singleton_one Submonoid.closure_singleton_one

@[to_additive]
theorem _root_.FreeMonoid.mrange_lift {α} (f : α → M) :
    mrange (FreeMonoid.lift f) = closure (Set.range f) := by
  rw [mrange_eq_map, ← FreeMonoid.closure_range_of, map_mclosure, ← Set.range_comp,
    FreeMonoid.lift_comp_of]
#align free_monoid.mrange_lift FreeMonoid.mrange_lift
#align free_add_monoid.mrange_lift FreeAddMonoid.mrange_lift

@[to_additive]
theorem closure_eq_mrange (s : Set M) : closure s = mrange (FreeMonoid.lift ((↑) : s → M)) := by
  rw [FreeMonoid.mrange_lift, Subtype.range_coe]
  -- 🎉 no goals
#align submonoid.closure_eq_mrange Submonoid.closure_eq_mrange
#align add_submonoid.closure_eq_mrange AddSubmonoid.closure_eq_mrange

@[to_additive]
theorem closure_eq_image_prod (s : Set M) :
    (closure s : Set M) = List.prod '' { l : List M | ∀ x ∈ l, x ∈ s } := by
  rw [closure_eq_mrange, coe_mrange, ← Set.range_list_map_coe, ← Set.range_comp]
  -- ⊢ Set.range ↑(↑FreeMonoid.lift Subtype.val) = Set.range (List.prod ∘ List.map  …
  exact congrArg _ (funext <| FreeMonoid.lift_apply _)
  -- 🎉 no goals
#align submonoid.closure_eq_image_prod Submonoid.closure_eq_image_prod
#align add_submonoid.closure_eq_image_sum AddSubmonoid.closure_eq_image_sum

@[to_additive]
theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ (l : List M) (_ : ∀ y ∈ l, y ∈ s), l.prod = x := by
  rwa [← SetLike.mem_coe, closure_eq_image_prod, Set.mem_image_iff_bex] at hx
  -- 🎉 no goals
#align submonoid.exists_list_of_mem_closure Submonoid.exists_list_of_mem_closure
#align add_submonoid.exists_list_of_mem_closure AddSubmonoid.exists_list_of_mem_closure

@[to_additive]
theorem exists_multiset_of_mem_closure {M : Type*} [CommMonoid M] {s : Set M} {x : M}
    (hx : x ∈ closure s) : ∃ (l : Multiset M) (_ : ∀ y ∈ l, y ∈ s), l.prod = x := by
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx
  -- ⊢ ∃ l x_1, Multiset.prod l = x
  exact ⟨l, h1, (Multiset.coe_prod l).trans h2⟩
  -- 🎉 no goals
#align submonoid.exists_multiset_of_mem_closure Submonoid.exists_multiset_of_mem_closure
#align add_submonoid.exists_multiset_of_mem_closure AddSubmonoid.exists_multiset_of_mem_closure

@[to_additive]
theorem closure_induction_left {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x := by
  rw [closure_eq_mrange] at h
  -- ⊢ p x
  obtain ⟨l, rfl⟩ := h
  -- ⊢ p (↑(↑FreeMonoid.lift Subtype.val) l)
  induction' l using FreeMonoid.recOn with x y ih
  -- ⊢ p (↑(↑FreeMonoid.lift Subtype.val) 1)
  · exact H1
    -- 🎉 no goals
  · simpa only [map_mul, FreeMonoid.lift_eval_of] using Hmul _ x.prop _ ih
    -- 🎉 no goals
#align submonoid.closure_induction_left Submonoid.closure_induction_left
#align add_submonoid.closure_induction_left AddSubmonoid.closure_induction_left

@[to_additive (attr := elab_as_elim)]
theorem induction_of_closure_eq_top_left {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x :=
  closure_induction_left
    (by
      rw [hs]
      -- ⊢ x ∈ ⊤
      exact mem_top _)
      -- 🎉 no goals
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_left Submonoid.induction_of_closure_eq_top_left
#align add_submonoid.induction_of_closure_eq_top_left AddSubmonoid.induction_of_closure_eq_top_left

@[to_additive]
theorem closure_induction_right {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  @closure_induction_left _ _ (MulOpposite.unop ⁻¹' s) (p ∘ MulOpposite.unop) (MulOpposite.op x)
    (closure_induction h (fun _x hx => subset_closure hx) (one_mem _)
      fun _x _y hx hy => mul_mem hy hx)
    H1 fun _x hx _y => Hmul _ _ hx
#align submonoid.closure_induction_right Submonoid.closure_induction_right
#align add_submonoid.closure_induction_right AddSubmonoid.closure_induction_right

@[to_additive (attr := elab_as_elim)]
theorem induction_of_closure_eq_top_right {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  closure_induction_right
    (by rw [hs]; exact mem_top _)
        -- ⊢ x ∈ ⊤
                 -- 🎉 no goals
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_right Submonoid.induction_of_closure_eq_top_right
#align add_submonoid.induction_of_closure_eq_top_right AddSubmonoid.induction_of_closure_eq_top_right

/-- The submonoid generated by an element. -/
def powers (n : M) : Submonoid M :=
  Submonoid.copy (mrange (powersHom M n)) (Set.range ((· ^ ·) n : ℕ → M)) <|
    Set.ext fun n => exists_congr fun i => by simp; rfl
                                              -- ⊢ n✝ ^ i = n ↔ n✝ ^ ↑Multiplicative.toAdd i = n
                                                    -- 🎉 no goals
#align submonoid.powers Submonoid.powers

theorem mem_powers (n : M) : n ∈ powers n :=
  ⟨1, pow_one _⟩
#align submonoid.mem_powers Submonoid.mem_powers

theorem coe_powers (x : M) : ↑(powers x) = Set.range fun n : ℕ => x ^ n :=
  rfl
#align submonoid.coe_powers Submonoid.coe_powers

theorem mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x :=
  Iff.rfl
#align submonoid.mem_powers_iff Submonoid.mem_powers_iff

theorem powers_eq_closure (n : M) : powers n = closure {n} := by
  ext
  -- ⊢ x✝ ∈ powers n ↔ x✝ ∈ closure {n}
  exact mem_closure_singleton.symm
  -- 🎉 no goals
#align submonoid.powers_eq_closure Submonoid.powers_eq_closure

theorem powers_subset {n : M} {P : Submonoid M} (h : n ∈ P) : powers n ≤ P := fun x hx =>
  match x, hx with
  | _, ⟨i, rfl⟩ => pow_mem h i
#align submonoid.powers_subset Submonoid.powers_subset

theorem powers_one : powers (1 : M) = ⊥ :=
  bot_unique <| powers_subset (one_mem _)
#align submonoid.powers_one Submonoid.powers_one

/-- Exponentiation map from natural numbers to powers. -/
@[simps!]
def pow (n : M) (m : ℕ) : powers n :=
  (powersHom M n).mrangeRestrict (Multiplicative.ofAdd m)
#align submonoid.pow Submonoid.pow
#align submonoid.pow_coe Submonoid.pow_coe

theorem pow_apply (n : M) (m : ℕ) : Submonoid.pow n m = ⟨n ^ m, m, rfl⟩ :=
  rfl
#align submonoid.pow_apply Submonoid.pow_apply

/-- Logarithms from powers to natural numbers. -/
def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.find <| (mem_powers_iff p.val n).mp p.prop
#align submonoid.log Submonoid.log

@[simp]
theorem pow_log_eq_self [DecidableEq M] {n : M} (p : powers n) : pow n (log p) = p :=
  Subtype.ext <| Nat.find_spec p.prop
#align submonoid.pow_log_eq_self Submonoid.pow_log_eq_self

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (pow n) :=
  Subtype.coe_injective.of_comp_iff (pow n)
#align submonoid.pow_right_injective_iff_pow_injective Submonoid.pow_right_injective_iff_pow_injective

@[simp]
theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (m : ℕ) : log (pow n m) = m :=
  pow_right_injective_iff_pow_injective.mp h <| pow_log_eq_self _
#align submonoid.log_pow_eq_self Submonoid.log_pow_eq_self

/-- The exponentiation map is an isomorphism from the additive monoid on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def powLogEquiv [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) :
    Multiplicative ℕ ≃* powers n where
  toFun m := pow n (Multiplicative.toAdd m)
  invFun m := Multiplicative.ofAdd (log m)
  left_inv := log_pow_eq_self h
  right_inv := pow_log_eq_self
  map_mul' _ _ := by simp only [pow, map_mul, ofAdd_add, toAdd_mul]
                     -- 🎉 no goals
#align submonoid.pow_log_equiv Submonoid.powLogEquiv
#align submonoid.pow_log_equiv_symm_apply Submonoid.powLogEquiv_symm_apply
#align submonoid.pow_log_equiv_apply Submonoid.powLogEquiv_apply

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : powers (n : M)) : log (x * y) = log x + log y :=
  (powLogEquiv h).symm.map_mul x y
#align submonoid.log_mul Submonoid.log_mul

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : log (pow x m) = m :=
  (powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _
#align submonoid.log_pow_int_eq_self Submonoid.log_pow_int_eq_self

@[simp]
theorem map_powers {N : Type*} {F : Type*} [Monoid N] [MonoidHomClass F M N] (f : F) (m : M) :
    (powers m).map f = powers (f m) := by
  simp only [powers_eq_closure, map_mclosure f, Set.image_singleton]
  -- 🎉 no goals
#align submonoid.map_powers Submonoid.map_powers

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive
      "If all the elements of a set `s` commute, then `closure s` forms an additive
      commutative monoid."]
def closureCommMonoidOfComm {s : Set M} (hcomm : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a * b = b * a) :
    CommMonoid (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun x y => by
      ext
      -- ⊢ ↑(x * y) = ↑(y * x)
      simp only [Submonoid.coe_mul]
      -- ⊢ ↑x * ↑y = ↑y * ↑x
      exact
        closure_induction₂ x.prop y.prop hcomm Commute.one_left Commute.one_right
          (fun x y z => Commute.mul_left) fun x y z => Commute.mul_right }
#align submonoid.closure_comm_monoid_of_comm Submonoid.closureCommMonoidOfComm
#align add_submonoid.closure_add_comm_monoid_of_comm AddSubmonoid.closureAddCommMonoidOfComm

end Submonoid

@[to_additive]
theorem IsScalarTower.of_mclosure_eq_top {N α} [Monoid M] [MulAction M N] [SMul N α] [MulAction M α]
    {s : Set M} (htop : Submonoid.closure s = ⊤)
    (hs : ∀ x ∈ s, ∀ (y : N) (z : α), (x • y) • z = x • y • z) : IsScalarTower M N α := by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  -- ⊢ ∀ (y : N) (z : α), (1 • y) • z = 1 • y • z
  · intro y z
    -- ⊢ (1 • y) • z = 1 • y • z
    rw [one_smul, one_smul]
    -- 🎉 no goals
  · clear x
    -- ⊢ ∀ (x : M), x ∈ s → ∀ (y : M), (∀ (y_1 : N) (z : α), (y • y_1) • z = y • y_1  …
    intro x hx x' hx' y z
    -- ⊢ ((x * x') • y) • z = (x * x') • y • z
    rw [mul_smul, mul_smul, hs x hx, hx']
    -- 🎉 no goals
#align is_scalar_tower.of_mclosure_eq_top IsScalarTower.of_mclosure_eq_top
#align vadd_assoc_class.of_mclosure_eq_top VAddAssocClass.of_mclosure_eq_top

@[to_additive]
theorem SMulCommClass.of_mclosure_eq_top {N α} [Monoid M] [SMul N α] [MulAction M α] {s : Set M}
    (htop : Submonoid.closure s = ⊤) (hs : ∀ x ∈ s, ∀ (y : N) (z : α), x • y • z = y • x • z) :
    SMulCommClass M N α := by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  -- ⊢ ∀ (n : N) (a : α), 1 • n • a = n • 1 • a
  · intro y z
    -- ⊢ 1 • y • z = y • 1 • z
    rw [one_smul, one_smul]
    -- 🎉 no goals
  · clear x
    -- ⊢ ∀ (x : M), x ∈ s → ∀ (y : M), (∀ (n : N) (a : α), y • n • a = n • y • a) → ∀ …
    intro x hx x' hx' y z
    -- ⊢ (x * x') • y • z = y • (x * x') • z
    rw [mul_smul, mul_smul, hx', hs x hx]
    -- 🎉 no goals
#align smul_comm_class.of_mclosure_eq_top SMulCommClass.of_mclosure_eq_top
#align vadd_comm_class.of_mclosure_eq_top VAddCommClass.of_mclosure_eq_top

namespace Submonoid

variable {N : Type*} [CommMonoid N]

open MonoidHom

@[to_additive]
theorem sup_eq_range (s t : Submonoid N) : s ⊔ t = mrange (s.subtype.coprod t.subtype) := by
  rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl, map_mrange,
    coprod_comp_inr, range_subtype, range_subtype]
#align submonoid.sup_eq_range Submonoid.sup_eq_range
#align add_submonoid.sup_eq_range AddSubmonoid.sup_eq_range

@[to_additive]
theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  simp only [ge_iff_le, sup_eq_range, mem_mrange, coprod_apply, coe_subtype, Prod.exists,
    Subtype.exists, exists_prop]
#align submonoid.mem_sup Submonoid.mem_sup
#align add_submonoid.mem_sup AddSubmonoid.mem_sup

end Submonoid

namespace AddSubmonoid

variable [AddMonoid A]

open Set

theorem closure_singleton_eq (x : A) :
    closure ({x} : Set A) = AddMonoidHom.mrange (multiplesHom A x) :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩) fun _ ⟨_n, hn⟩ =>
    hn ▸ nsmul_mem (subset_closure <| Set.mem_singleton _) _
#align add_submonoid.closure_singleton_eq AddSubmonoid.closure_singleton_eq

/-- The `AddSubmonoid` generated by an element of an `AddMonoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y := by
  rw [closure_singleton_eq, AddMonoidHom.mem_mrange]; rfl
  -- ⊢ (∃ x_1, ↑(↑(multiplesHom A) x) x_1 = y) ↔ ∃ n, n • x = y
                                                      -- 🎉 no goals
#align add_submonoid.mem_closure_singleton AddSubmonoid.mem_closure_singleton

theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]
  -- 🎉 no goals
#align add_submonoid.closure_singleton_zero AddSubmonoid.closure_singleton_zero

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (AddMonoidHom.mrange (multiplesHom A x)) (Set.range (fun i => i • x : ℕ → A)) <|
    Set.ext fun n => exists_congr fun i => by simp
                                              -- 🎉 no goals
#align add_submonoid.multiples AddSubmonoid.multiples

attribute [to_additive existing multiples] Submonoid.powers

attribute [to_additive (attr := simp) mem_multiples] Submonoid.mem_powers
#align add_submonoid.mem_multiples AddSubmonoid.mem_multiples

attribute [to_additive (attr := norm_cast) coe_multiples] Submonoid.coe_powers
#align add_submonoid.coe_multiples AddSubmonoid.coe_multiples

attribute [to_additive mem_multiples_iff] Submonoid.mem_powers_iff
#align add_submonoid.mem_multiples_iff AddSubmonoid.mem_multiples_iff

attribute [to_additive multiples_eq_closure] Submonoid.powers_eq_closure
#align add_submonoid.multiples_eq_closure AddSubmonoid.multiples_eq_closure

attribute [to_additive multiples_subset] Submonoid.powers_subset
#align add_submonoid.multiples_subset AddSubmonoid.multiples_subset

attribute [to_additive (attr := simp) multiples_zero] Submonoid.powers_one
#align add_submonoid.multiples_zero AddSubmonoid.multiples_zero

end AddSubmonoid

/-! Lemmas about additive closures of `Subsemigroup`. -/


namespace MulMemClass

variable {R : Type*} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
theorem mul_right_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert b
  -- ⊢ ∀ {b : R}, b ∈ S → a * b ∈ AddSubmonoid.closure ↑S
  refine' @AddSubmonoid.closure_induction _ _ _
    (fun z => ∀ (b : R), b ∈ S → z * b ∈ AddSubmonoid.closure S) _ ha _ _ _ <;> clear ha a
                                                                                -- ⊢ ∀ (x : R), x ∈ ↑S → (fun z => ∀ (b : R), b ∈ S → z * b ∈ AddSubmonoid.closur …
                                                                                -- ⊢ (fun z => ∀ (b : R), b ∈ S → z * b ∈ AddSubmonoid.closure ↑S) 0
                                                                                -- ⊢ ∀ (x y : R), (fun z => ∀ (b : R), b ∈ S → z * b ∈ AddSubmonoid.closure ↑S) x …
  · exact fun r hr b hb => AddSubmonoid.mem_closure.mpr fun y hy => hy (mul_mem hr hb)
    -- 🎉 no goals
  · exact fun b _ => by simp only [zero_mul, (AddSubmonoid.closure (S : Set R)).zero_mem]
    -- 🎉 no goals
  · simp_rw [add_mul]
    -- ⊢ ∀ (x y : R), (∀ (b : R), b ∈ S → x * b ∈ AddSubmonoid.closure ↑S) → (∀ (b :  …
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr _ hb) (hs _ hb)
    -- 🎉 no goals
#align mul_mem_class.mul_right_mem_add_closure MulMemClass.mul_right_mem_add_closure

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
theorem mul_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R))
    (hb : b ∈ AddSubmonoid.closure (S : Set R)) : a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert a
  -- ⊢ ∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * b ∈ AddSubmonoid.closure ↑S
  refine' @AddSubmonoid.closure_induction _ _ _
    (fun z => ∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * z ∈ AddSubmonoid.closure ↑S)
      _ hb _ _ _ <;> clear hb b
                     -- ⊢ ∀ (x : R), x ∈ ↑S → (fun z => ∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * z …
                     -- ⊢ (fun z => ∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * z ∈ AddSubmonoid.clos …
                     -- ⊢ ∀ (x y : R), (fun z => ∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * z ∈ AddS …
  · exact fun r hr b hb => MulMemClass.mul_right_mem_add_closure hb hr
    -- 🎉 no goals
  · exact fun _ => by simp only [mul_zero, (AddSubmonoid.closure (S : Set R)).zero_mem]
    -- 🎉 no goals
  · simp_rw [mul_add]
    -- ⊢ ∀ (x y : R), (∀ {a : R}, a ∈ AddSubmonoid.closure ↑S → a * x ∈ AddSubmonoid. …
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
    -- 🎉 no goals
#align mul_mem_class.mul_mem_add_closure MulMemClass.mul_mem_add_closure

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
    a * b ∈ AddSubmonoid.closure (S : Set R) :=
  mul_mem_add_closure (AddSubmonoid.mem_closure.mpr fun _sT hT => hT ha) hb
#align mul_mem_class.mul_left_mem_add_closure MulMemClass.mul_left_mem_add_closure

end MulMemClass

namespace Submonoid

/-- An element is in the closure of a two-element set if it is a linear combination of those two
elements. -/
@[to_additive
      "An element is in the closure of a two-element set if it is a linear combination of
      those two elements."]
theorem mem_closure_pair {A : Type*} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  rw [← Set.singleton_union, Submonoid.closure_union, mem_sup]
  -- ⊢ (∃ y, y ∈ closure {a} ∧ ∃ z, z ∈ closure {b} ∧ y * z = c) ↔ ∃ m n, a ^ m * b …
  simp_rw [mem_closure_singleton, exists_exists_eq_and]
  -- 🎉 no goals
#align submonoid.mem_closure_pair Submonoid.mem_closure_pair
#align add_submonoid.mem_closure_pair AddSubmonoid.mem_closure_pair

end Submonoid

section mul_add

theorem ofMul_image_powers_eq_multiples_ofMul [Monoid M] {x : M} :
    Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) := by
  ext
  -- ⊢ x✝ ∈ ↑Additive.ofMul '' ↑(Submonoid.powers x) ↔ x✝ ∈ ↑(AddSubmonoid.multiple …
  constructor
  -- ⊢ x✝ ∈ ↑Additive.ofMul '' ↑(Submonoid.powers x) → x✝ ∈ ↑(AddSubmonoid.multiple …
  · rintro ⟨y, ⟨n, hy1⟩, hy2⟩
    -- ⊢ x✝ ∈ ↑(AddSubmonoid.multiples (↑Additive.ofMul x))
    use n
    -- ⊢ (fun i => i • ↑Additive.ofMul x) n = x✝
    simpa [← ofMul_pow, hy1]
    -- 🎉 no goals
  · rintro ⟨n, hn⟩
    -- ⊢ x✝ ∈ ↑Additive.ofMul '' ↑(Submonoid.powers x)
    refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
    -- ⊢ ↑Additive.ofMul (x ^ n) = x✝
    rwa [ofMul_pow]
    -- 🎉 no goals
#align of_mul_image_powers_eq_multiples_of_mul ofMul_image_powers_eq_multiples_ofMul

theorem ofAdd_image_multiples_eq_powers_ofAdd [AddMonoid A] {x : A} :
    Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) =
      Submonoid.powers (Multiplicative.ofAdd x) := by
  symm
  -- ⊢ ↑(Submonoid.powers (↑Multiplicative.ofAdd x)) = ↑Multiplicative.ofAdd '' ↑(A …
  rw [Equiv.eq_image_iff_symm_image_eq]
  -- ⊢ ↑Multiplicative.ofAdd.symm '' ↑(Submonoid.powers (↑Multiplicative.ofAdd x))  …
  exact ofMul_image_powers_eq_multiples_ofMul
  -- 🎉 no goals
#align of_add_image_multiples_eq_powers_of_add ofAdd_image_multiples_eq_powers_ofAdd

end mul_add
