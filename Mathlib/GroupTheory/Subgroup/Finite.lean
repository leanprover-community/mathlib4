/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module group_theory.subgroup.finite
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Subgroups

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/


open BigOperators

variable {G : Type _} [Group G]

variable {A : Type _} [AddGroup A]

namespace Subgroup

@[to_additive]
instance (K : Subgroup G) [d : DecidablePred (· ∈ K)] [Fintype G] : Fintype K :=
  show Fintype { g : G // g ∈ K } from inferInstance

@[to_additive]
instance (K : Subgroup G) [Finite G] : Finite K :=
  Subtype.finite

end Subgroup

/-!
### Conversion to/from `additive`/`multiplicative`
-/


namespace Subgroup

variable (H K : Subgroup G)

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive "Sum of a list of elements in an `add_subgroup` is in the `add_subgroup`."]
protected theorem list_prod_mem {l : List G} : (∀ x ∈ l, x ∈ K) → l.Prod ∈ K :=
  list_prod_mem
#align subgroup.list_prod_mem Subgroup.list_prod_mem
#align add_subgroup.list_sum_mem AddSubgroup.list_sum_mem

/-- Product of a multiset of elements in a subgroup of a `comm_group` is in the subgroup. -/
@[to_additive
      "Sum of a multiset of elements in an `add_subgroup` of an `add_comm_group`\nis in the `add_subgroup`."]
protected theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (∀ a ∈ g, a ∈ K) → g.Prod ∈ K :=
  multiset_prod_mem g
#align subgroup.multiset_prod_mem Subgroup.multiset_prod_mem
#align add_subgroup.multiset_sum_mem AddSubgroup.multiset_sum_mem

@[to_additive]
theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K :=
  K.toSubmonoid.multiset_noncomm_prod_mem g comm
#align subgroup.multiset_noncomm_prod_mem Subgroup.multiset_noncommProd_mem
#align add_subgroup.multiset_noncomm_sum_mem AddSubgroup.multiset_noncomm_sum_mem

/-- Product of elements of a subgroup of a `comm_group` indexed by a `finset` is in the
    subgroup. -/
@[to_additive
      "Sum of elements in an `add_subgroup` of an `add_comm_group` indexed by a `finset`\nis in the `add_subgroup`."]
protected theorem prod_mem {G : Type _} [CommGroup G] (K : Subgroup G) {ι : Type _} {t : Finset ι}
    {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) : (∏ c in t, f c) ∈ K :=
  prod_mem h
#align subgroup.prod_mem Subgroup.prod_mem
#align add_subgroup.sum_mem AddSubgroup.sum_mem

@[to_additive]
theorem noncommProd_mem (K : Subgroup G) {ι : Type _} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K :=
  K.toSubmonoid.noncomm_prod_mem t f comm
#align subgroup.noncomm_prod_mem Subgroup.noncommProd_mem
#align add_subgroup.noncomm_sum_mem AddSubgroup.noncomm_sum_mem

@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List H) : (l.Prod : G) = (l.map coe).Prod :=
  SubmonoidClass.coe_list_prod l
#align subgroup.coe_list_prod Subgroup.coe_list_prod
#align add_subgroup.coe_list_sum AddSubgroup.coe_list_sum

@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.Prod : G) = (m.map coe).Prod :=
  SubmonoidClass.coe_multiset_prod m
#align subgroup.coe_multiset_prod Subgroup.coe_multiset_prod
#align add_subgroup.coe_multiset_sum AddSubgroup.coe_multiset_sum

@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι G} [CommGroup G] (H : Subgroup G) (f : ι → H) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : G) :=
  SubmonoidClass.coe_finset_prod f s
#align subgroup.coe_finset_prod Subgroup.coe_finset_prod
#align add_subgroup.coe_finset_sum AddSubgroup.coe_finset_sum

@[to_additive]
instance fintypeBot : Fintype (⊥ : Subgroup G) :=
  ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩
#align subgroup.fintype_bot Subgroup.fintypeBot
#align add_subgroup.fintype_bot AddSubgroup.fintypeBot

/- curly brackets `{}` are used here instead of instance brackets `[]` because
  the instance in a goal is often not the same as the one inferred by type class inference.  -/
@[simp, to_additive]
theorem card_bot {_ : Fintype ↥(⊥ : Subgroup G)} : Fintype.card (⊥ : Subgroup G) = 1 :=
  Fintype.card_eq_one_iff.2
    ⟨⟨(1 : G), Set.mem_singleton 1⟩, fun ⟨y, hy⟩ => Subtype.eq <| Subgroup.mem_bot.1 hy⟩
#align subgroup.card_bot Subgroup.card_bot
#align add_subgroup.card_bot AddSubgroup.card_bot

@[to_additive]
theorem eq_top_of_card_eq [Fintype H] [Fintype G] (h : Fintype.card H = Fintype.card G) : H = ⊤ :=
  by
  haveI : Fintype (H : Set G) := ‹Fintype H›
  rw [SetLike.ext'_iff, coe_top, ← Finset.coe_univ, ← (H : Set G).coe_to_finset, Finset.coe_inj, ←
    Finset.card_eq_iff_eq_univ, ← h, Set.toFinset_card]
  congr
#align subgroup.eq_top_of_card_eq Subgroup.eq_top_of_card_eq
#align add_subgroup.eq_top_of_card_eq AddSubgroup.eq_top_of_card_eq

@[to_additive]
theorem eq_top_of_le_card [Fintype H] [Fintype G] (h : Fintype.card G ≤ Fintype.card H) : H = ⊤ :=
  eq_top_of_card_eq H (le_antisymm (Fintype.card_le_of_injective coe Subtype.coe_injective) h)
#align subgroup.eq_top_of_le_card Subgroup.eq_top_of_le_card
#align add_subgroup.eq_top_of_le_card AddSubgroup.eq_top_of_le_card

@[to_additive]
theorem eq_bot_of_card_le [Fintype H] (h : Fintype.card H ≤ 1) : H = ⊥ :=
  let _ := Fintype.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H
#align subgroup.eq_bot_of_card_le Subgroup.eq_bot_of_card_le
#align add_subgroup.eq_bot_of_card_le AddSubgroup.eq_bot_of_card_le

@[to_additive]
theorem eq_bot_of_card_eq [Fintype H] (h : Fintype.card H = 1) : H = ⊥ :=
  H.eq_bot_of_card_le (le_of_eq h)
#align subgroup.eq_bot_of_card_eq Subgroup.eq_bot_of_card_eq
#align add_subgroup.eq_bot_of_card_eq AddSubgroup.eq_bot_of_card_eq

@[to_additive]
theorem card_le_one_iff_eq_bot [Fintype H] : Fintype.card H ≤ 1 ↔ H = ⊥ :=
  ⟨fun h =>
    (eq_bot_iff_forall _).2 fun x hx => by
      simpa [Subtype.ext_iff] using Fintype.card_le_one_iff.1 h ⟨x, hx⟩ 1,
    fun h => by simp [h]⟩
#align subgroup.card_le_one_iff_eq_bot Subgroup.card_le_one_iff_eq_bot
#align add_subgroup.card_nonpos_iff_eq_bot AddSubgroup.card_nonpos_iff_eq_bot

@[to_additive]
theorem one_lt_card_iff_ne_bot [Fintype H] : 1 < Fintype.card H ↔ H ≠ ⊥ :=
  lt_iff_not_le.trans H.card_le_one_iff_eq_bot.Not
#align subgroup.one_lt_card_iff_ne_bot Subgroup.one_lt_card_iff_ne_bot
#align add_subgroup.pos_card_iff_ne_bot AddSubgroup.pos_card_iff_ne_bot

end Subgroup

namespace Subgroup

section Pi

open Set

variable {η : Type _} {f : η → Type _} [∀ i, Group (f i)]

@[to_additive]
theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := by
  induction' I using Finset.induction_on with i I hnmem ih generalizing x
  · convert one_mem H
    ext i
    exact h1 i (not_mem_empty i)
  · have : x = Function.update x i 1 * Pi.mulSingle i (x i) :=
      by
      ext j
      by_cases heq : j = i
      · subst HEq
        simp
      · simp [HEq]
    rw [this]
    clear this
    apply mul_mem
    · apply ih <;> clear ih
      · intro j hj
        by_cases heq : j = i
        · subst HEq
          simp
        · simp [HEq]
          apply h1 j
          simpa [HEq] using hj
      · intro j hj
        have : j ≠ i := by
          rintro rfl
          contradiction
        simp [this]
        exact h2 _ (Finset.mem_insert_of_mem hj)
    · apply h2
      simp
#align subgroup.pi_mem_of_mul_single_mem_aux Subgroup.pi_mem_of_mulSingle_mem_aux
#align add_subgroup.pi_mem_of_single_mem_aux AddSubgroup.pi_mem_of_single_mem_aux

@[to_additive]
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H :=
  by
  cases nonempty_fintype η
  exact pi_mem_of_mul_single_mem_aux Finset.univ x (by simp) fun i _ => h i
#align subgroup.pi_mem_of_mul_single_mem Subgroup.pi_mem_of_mulSingle_mem
#align add_subgroup.pi_mem_of_single_mem AddSubgroup.pi_mem_of_single_mem

/-- For finite index types, the `subgroup.pi` is generated by the embeddings of the groups.  -/
@[to_additive
      "For finite index types, the `subgroup.pi` is generated by the embeddings of the\nadditive groups."]
theorem pi_le_iff [DecidableEq η] [Finite η] {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    pi univ H ≤ J ↔ ∀ i : η, map (MonoidHom.single f i) (H i) ≤ J :=
  by
  constructor
  · rintro h i _ ⟨x, hx, rfl⟩
    apply h
    simpa using hx
  · exact fun h x hx => pi_mem_of_mul_single_mem x fun i => h i (mem_map_of_mem _ (hx i trivial))
#align subgroup.pi_le_iff Subgroup.pi_le_iff
#align add_subgroup.pi_le_iff AddSubgroup.pi_le_iff

end Pi

end Subgroup

namespace Subgroup

section Normalizer

theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.setNormalizer S := by
  haveI := Classical.propDecidable <;> cases nonempty_fintype S <;>
      haveI := Set.fintypeImage S fun n => x * n * x⁻¹ <;>
    exact fun n =>
      ⟨h n, fun h₁ =>
        have heq : (fun n => x * n * x⁻¹) '' S = S :=
          Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
            (by rw [Set.card_image_of_injective S conj_injective])
        have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := HEq.symm ▸ h₁
        let ⟨y, hy⟩ := this
        conj_injective hy.2 ▸ hy.1⟩
#align subgroup.mem_normalizer_fintype Subgroup.mem_normalizer_fintype

end Normalizer

end Subgroup

namespace MonoidHom

variable {N : Type _} [Group N]

open Subgroup

@[to_additive]
instance decidableMemRange (f : G →* N) [Fintype G] [DecidableEq N] : DecidablePred (· ∈ f.range) :=
  fun x => Fintype.decidableExistsFintype
#align monoid_hom.decidable_mem_range MonoidHom.decidableMemRange
#align add_monoid_hom.decidable_mem_range AddMonoidHom.decidableMemRange

-- this instance can't go just after the definition of `mrange` because `fintype` is
-- not imported at that stage
/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
presence of `fintype N`. -/
@[to_additive
      "The range of a finite additive monoid under an additive monoid homomorphism is\nfinite.\n\nNote: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the\npresence of `fintype N`."]
instance fintypeMrange {M N : Type _} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
    (f : M →* N) : Fintype (mrange f) :=
  Set.fintypeRange f
#align monoid_hom.fintype_mrange MonoidHom.fintypeMrange
#align add_monoid_hom.fintype_mrange AddMonoidHom.fintypeMrange

/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the
presence of `fintype N`. -/
@[to_additive
      "The range of a finite additive group under an additive group homomorphism is finite.\n\nNote: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the\npresence of `fintype N`."]
instance fintypeRange [Fintype G] [DecidableEq N] (f : G →* N) : Fintype (range f) :=
  Set.fintypeRange f
#align monoid_hom.fintype_range MonoidHom.fintypeRange
#align add_monoid_hom.fintype_range AddMonoidHom.fintypeRange

end MonoidHom

