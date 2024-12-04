/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria for products and sums

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;

## Tags
submonoid, submonoids
-/

-- We don't need ordered structures to establish basic membership facts for submonoids
assert_not_exists OrderedSemiring

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {S : B}

namespace SubmonoidClass

@[to_additive (attr := norm_cast, simp)]
theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod (SubmonoidClass.subtype S : _ →* M) l

@[to_additive (attr := norm_cast, simp)]
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m

@[to_additive (attr := norm_cast, simp)]
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) :=
  map_prod (SubmonoidClass.subtype S) f s

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S := by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`."]
theorem prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S :=
  multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

namespace Submonoid

variable (s : Submonoid M)

@[to_additive (attr := norm_cast)]
theorem coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod s.subtype l

@[to_additive (attr := norm_cast)]
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  S.subtype.map_multiset_prod m

@[to_additive (attr := norm_cast)]
theorem coe_finset_prod {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) :=
  map_prod S.subtype f s

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.prod ∈ s := by
  lift l to List s using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

@[to_additive]
theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`."]
theorem prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S :=
  S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]
theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

end Submonoid
