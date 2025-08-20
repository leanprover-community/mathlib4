/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Finite.Range

/-!
# Subgroups

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/

assert_not_exists Field

variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

namespace Subgroup

@[to_additive]
instance (K : Subgroup G) [DecidablePred (· ∈ K)] [Fintype G] : Fintype K :=
  show Fintype { g : G // g ∈ K } from inferInstance

@[to_additive]
instance (K : Subgroup G) [Finite G] : Finite K :=
  Subtype.finite

end Subgroup

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


namespace Subgroup

variable (H K : Subgroup G)

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive /-- Sum of a list of elements in an `AddSubgroup` is in the `AddSubgroup`. -/]
protected theorem list_prod_mem {l : List G} : (∀ x ∈ l, x ∈ K) → l.prod ∈ K :=
  list_prod_mem

/-- Product of a multiset of elements in a subgroup of a `CommGroup` is in the subgroup. -/
@[to_additive /-- Sum of a multiset of elements in an `AddSubgroup` of an `AddCommGroup` is in
the `AddSubgroup`. -/]
protected theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (∀ a ∈ g, a ∈ K) → g.prod ∈ K :=
  multiset_prod_mem g

@[to_additive]
theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K :=
  K.toSubmonoid.multiset_noncommProd_mem g comm

/-- Product of elements of a subgroup of a `CommGroup` indexed by a `Finset` is in the
    subgroup. -/
@[to_additive /-- Sum of elements in an `AddSubgroup` of an `AddCommGroup` indexed by a `Finset`
is in the `AddSubgroup`. -/]
protected theorem prod_mem {G : Type*} [CommGroup G] (K : Subgroup G) {ι : Type*} {t : Finset ι}
    {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) : (∏ c ∈ t, f c) ∈ K :=
  prod_mem h

@[to_additive]
theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K :=
  K.toSubmonoid.noncommProd_mem t f comm

@[to_additive (attr := simp 1100, norm_cast)]
theorem val_list_prod (l : List H) : (l.prod : G) = (l.map Subtype.val).prod :=
  SubmonoidClass.coe_list_prod l

@[to_additive (attr := simp 1100, norm_cast)]
theorem val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.prod : G) = (m.map Subtype.val).prod :=
  SubmonoidClass.coe_multiset_prod m

@[to_additive (attr := simp 1100, norm_cast)]
theorem val_finset_prod {ι G} [CommGroup G] (H : Subgroup G) (f : ι → H) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : G) :=
  SubmonoidClass.coe_finset_prod f s

@[to_additive]
instance fintypeBot : Fintype (⊥ : Subgroup G) :=
  ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩

@[to_additive]
theorem card_bot : Nat.card (⊥ : Subgroup G) = 1 := by simp

@[to_additive]
theorem card_top : Nat.card (⊤ : Subgroup G) = Nat.card G :=
  Nat.card_congr Subgroup.topEquiv.toEquiv

@[to_additive]
theorem eq_of_le_of_card_ge {H K : Subgroup G} [Finite K] (hle : H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) :
    H = K :=
  SetLike.coe_injective <| Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hle hcard

@[to_additive]
theorem eq_top_of_le_card [Finite G] (h : Nat.card G ≤ Nat.card H) : H = ⊤ :=
  eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

@[to_additive]
theorem eq_top_of_card_eq [Finite H] (h : Nat.card H = Nat.card G) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ Nat.card_pos.ne')
  exact eq_top_of_le_card _ (Nat.le_of_eq h.symm)

@[to_additive (attr := simp)]
theorem card_eq_iff_eq_top [Finite H] : Nat.card H = Nat.card G ↔ H = ⊤ :=
  Iff.intro (eq_top_of_card_eq H) (fun h ↦ by simpa only [h] using card_top)

@[to_additive]
theorem eq_bot_of_card_le [Finite H] (h : Nat.card H ≤ 1) : H = ⊥ :=
  let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

@[to_additive]
theorem eq_bot_of_card_eq (h : Nat.card H = 1) : H = ⊥ :=
  let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

@[to_additive card_le_one_iff_eq_bot]
theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H ≤ 1 ↔ H = ⊥ :=
  ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

@[to_additive] lemma eq_bot_iff_card : H = ⊥ ↔ Nat.card H = 1 :=
  ⟨by rintro rfl; exact card_bot, eq_bot_of_card_eq _⟩

@[to_additive one_lt_card_iff_ne_bot]
theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H ≠ ⊥ :=
  lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

@[to_additive]
theorem card_le_card_group [Finite G] : Nat.card H ≤ Nat.card G :=
  Nat.card_le_card_of_injective _ Subtype.coe_injective

@[to_additive]
theorem card_le_of_le {H K : Subgroup G} [Finite K] (h : H ≤ K) : Nat.card H ≤ Nat.card K :=
  Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h)

@[to_additive]
theorem card_map_of_injective {H : Type*} [Group H] {K : Subgroup G} {f : G →* H}
    (hf : Function.Injective f) :
    Nat.card (map f K) = Nat.card K := by
  apply Nat.card_image_of_injective hf

@[to_additive]
theorem card_subtype (K : Subgroup G) (L : Subgroup K) :
    Nat.card (map K.subtype L) = Nat.card L :=
  card_map_of_injective K.subtype_injective

end Subgroup

namespace Subgroup

section Pi

open Set

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

@[to_additive]
theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := by
  induction I using Finset.induction_on generalizing x with
  | empty =>
    have : x = 1 := by
      ext i
      exact h1 i (Finset.notMem_empty i)
    rw [this]
    exact one_mem H
  | insert i I hnotMem ih =>
    have : x = Function.update x i 1 * Pi.mulSingle i (x i) := by
      ext j
      by_cases heq : j = i
      · subst heq
        simp
      · simp [heq]
    rw [this]
    clear this
    apply mul_mem
    · apply ih <;> clear ih
      · intro j hj
        by_cases heq : j = i
        · subst heq
          simp
        · simpa [heq] using h1 j (by simpa [heq] using hj)
      · intro j hj
        have : j ≠ i := by
          rintro rfl
          contradiction
        simp only [ne_eq, this, not_false_eq_true, Function.update_of_ne]
        exact h2 _ (Finset.mem_insert_of_mem hj)
    · apply h2
      simp

@[to_additive]
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  cases nonempty_fintype η
  exact pi_mem_of_mulSingle_mem_aux Finset.univ x (by simp) fun i _ => h i

/-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the groups. -/
@[to_additive /-- For finite index types, the `Subgroup.pi` is generated by the embeddings of the
additive groups. -/]
theorem pi_le_iff [DecidableEq η] [Finite η] {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    pi univ H ≤ J ↔ ∀ i : η, map (MonoidHom.mulSingle f i) (H i) ≤ J := by
  constructor
  · rintro h i _ ⟨x, hx, rfl⟩
    apply h
    simpa using hx
  · exact fun h x hx => pi_mem_of_mulSingle_mem x fun i => h i (mem_map_of_mem _ (hx i trivial))

end Pi

end Subgroup

namespace Subgroup

section Normalizer

theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.setNormalizer S := by
  haveI := Classical.propDecidable; cases nonempty_fintype S
  haveI := Set.fintypeImage S fun n => x * n * x⁻¹
  exact fun n =>
    ⟨h n, fun h₁ =>
      have heq : (fun n => x * n * x⁻¹) '' S = S :=
        Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
          (by rw [Set.card_image_of_injective S conj_injective])
      have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := heq.symm ▸ h₁
      let ⟨y, hy⟩ := this
      conj_injective hy.2 ▸ hy.1⟩

end Normalizer

end Subgroup

namespace MonoidHom

variable {N : Type*} [Group N]

open Subgroup

@[to_additive]
instance decidableMemRange (f : G →* N) [Fintype G] [DecidableEq N] : DecidablePred (· ∈ f.range) :=
  fun _ => Fintype.decidableExistsFintype

-- this instance can't go just after the definition of `mrange` because `Fintype` is
-- not imported at that stage
/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
presence of `Fintype N`. -/
@[to_additive /-- The range of a finite additive monoid under an additive monoid homomorphism is
finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the presence
of `Fintype N`. -/]
instance fintypeMrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
    (f : M →* N) : Fintype (mrange f) :=
  Set.fintypeRange f

/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/
@[to_additive
/-- The range of a finite additive group under an additive group homomorphism is finite.

Note: this instance can form a diamond with `Subtype.fintype` or `Subgroup.fintype` in the
presence of `Fintype N`. -/]
instance fintypeRange [Fintype G] [DecidableEq N] (f : G →* N) : Fintype (range f) :=
  Set.fintypeRange f

lemma _root_.Fintype.card_coeSort_mrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M]
    [DecidableEq N] {f : M →* N} (hf : Function.Injective f) :
    Fintype.card (mrange f) = Fintype.card M :=
  Set.card_range_of_injective hf

lemma _root_.Fintype.card_coeSort_range [Fintype G] [DecidableEq N] {f : G →* N}
    (hf : Function.Injective f) :
    Fintype.card (range f) = Fintype.card G :=
  Set.card_range_of_injective hf

end MonoidHom
