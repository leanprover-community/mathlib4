/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.Coset.Defs

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with  `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`)

If instead `G` is an additive group, we can write (with  `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a • s` with `open AddOpposite`)

## Main definitions

* `Subgroup.leftCosetEquivSubgroup`: the natural bijection between a left coset and the subgroup,
  for an `AddGroup` this is `AddSubgroup.leftCosetEquivAddSubgroup`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

assert_not_exists Cardinal Multiset

open Function MulOpposite Set
open scoped Pointwise

variable {α : Type*}

section CosetMul

variable [Mul α]

@[to_additive mem_leftAddCoset]
theorem mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a • s :=
  mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_rightAddCoset]
theorem mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ op a • s :=
  mem_image_of_mem (fun b : α => b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence /-- Equality of two left cosets `a + s` and `b + s`. -/]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a • s = b • s

@[to_additive leftAddCosetEquivalence_rel]
theorem leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) :=
  @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence /-- Equality of two right cosets `s + a` and `s + b`. -/]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  op a • s = op b • s

@[to_additive rightAddCosetEquivalence_rel]
theorem rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) :=
  @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans

end CosetMul

section CosetSemigroup

variable [Semigroup α]

@[to_additive leftAddCoset_assoc]
theorem leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive rightAddCoset_assoc]
theorem rightCoset_assoc (s : Set α) (a b : α) : op b • op a • s = op (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive leftAddCoset_rightAddCoset]
theorem leftCoset_rightCoset (s : Set α) (a b : α) : op b • a • s = a • (op b • s) := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

end CosetSemigroup

section CosetMonoid

variable [Monoid α] (s : Set α)

@[to_additive zero_leftAddCoset]
theorem one_leftCoset : (1 : α) • s = s :=
  Set.ext <| by simp

@[to_additive rightAddCoset_zero]
theorem rightCoset_one : op (1 : α) • s = s :=
  Set.ext <| by simp

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoid α] (s : Submonoid α)

@[to_additive mem_own_leftAddCoset]
theorem mem_own_leftCoset (a : α) : a ∈ a • (s : Set α) :=
  suffices a * 1 ∈ a • (s : Set α) by simpa
  mem_leftCoset a (one_mem s : 1 ∈ s)

@[to_additive mem_own_rightAddCoset]
theorem mem_own_rightCoset (a : α) : a ∈ op a • (s : Set α) :=
  suffices 1 * a ∈ op a • (s : Set α) by simpa
  mem_rightCoset a (one_mem s : 1 ∈ s)

@[to_additive mem_leftAddCoset_leftAddCoset]
theorem mem_leftCoset_leftCoset {a : α} (ha : a • (s : Set α) = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_leftCoset s a

@[to_additive mem_rightAddCoset_rightAddCoset]
theorem mem_rightCoset_rightCoset {a : α} (ha : op a • (s : Set α) = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_rightCoset s a

end CosetSubmonoid

section CosetGroup

variable [Group α] {s : Set α} {x : α}

@[to_additive mem_leftAddCoset_iff]
theorem mem_leftCoset_iff (a : α) : x ∈ a • s ↔ a⁻¹ * x ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩

@[to_additive mem_rightAddCoset_iff]
theorem mem_rightCoset_iff (a : α) : x ∈ op a • s ↔ x * a⁻¹ ∈ s :=
  Iff.intro (fun ⟨b, hb, Eq⟩ => by simp [Eq.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Group α] (s : Subgroup α)

@[to_additive leftAddCoset_mem_leftAddCoset]
theorem leftCoset_mem_leftCoset {a : α} (ha : a ∈ s) : a • (s : Set α) = s :=
  Set.ext <| by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive rightAddCoset_mem_rightAddCoset]
theorem rightCoset_mem_rightCoset {a : α} (ha : a ∈ s) : op a • (s : Set α) = s :=
  Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive]
theorem orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = op a • s :=
  Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩

@[to_additive]
theorem orbit_subgroup_eq_self_of_mem {a : α} (ha : a ∈ s) : MulAction.orbit s a = s :=
  (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)

@[to_additive]
theorem orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s :=
  orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_addCosets_of_normal]
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g • (s : Set α) = op g • s :=
  Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff, N.mem_comm_iff]

@[to_additive normal_of_eq_addCosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g • (s : Set α) = op g • s) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ ∈ (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩

@[to_additive normal_iff_eq_addCosets]
theorem normal_iff_eq_cosets : s.Normal ↔ ∀ g : α, g • (s : Set α) = op g • s :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive leftAddCoset_eq_iff]
theorem leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔ x⁻¹ * y ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [inv_mul_cancel]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h

@[to_additive rightAddCoset_eq_iff]
theorem rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op y • s ↔ y * x⁻¹ ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_inv_cancel]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h

end CosetSubgroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

theorem leftRel_r_eq_leftCosetEquivalence :
    ⇑(QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  rw [leftRel_eq]
  exact (leftCoset_eq_iff s).symm

@[to_additive leftRel_prod]
lemma leftRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    leftRel (s.prod s') = (leftRel s).prod (leftRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]
lemma leftRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    leftRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ leftRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]

theorem rightRel_r_eq_rightCosetEquivalence :
    ⇑(QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  rw [rightRel_eq]
  exact (rightCoset_eq_iff s).symm

@[to_additive rightRel_prod]
lemma rightRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    rightRel (s.prod s') = (rightRel s).prod (rightRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]
lemma rightRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    rightRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ rightRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

variable (s)

/-- Given a subgroup `s`, the function that sends a subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s` is strictly monotone, even though
it is not injective in general. -/
@[to_additive QuotientAddGroup.strictMono_comap_prod_image /-- Given an additive subgroup `s`,
the function that sends an additive subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s`
is strictly monotone, even though it is not injective in general. -/]
theorem strictMono_comap_prod_image :
    StrictMono fun t : Subgroup α ↦ (t.comap s.subtype, mk (s := s) '' t) := by
  refine fun t₁ t₂ h ↦ ⟨⟨Subgroup.comap_mono h.1, Set.image_mono h.1⟩,
    mt (fun ⟨le1, le2⟩ a ha ↦ ?_) h.2⟩
  obtain ⟨a', h', eq⟩ := le2 ⟨_, ha, rfl⟩
  convert ← t₁.mul_mem h' (@le1 ⟨_, QuotientGroup.eq.1 eq⟩ <| t₂.mul_mem (t₂.inv_mem <| h.1 h') ha)
  apply mul_inv_cancel_left

variable {s} {a b : α}

@[to_additive]
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    { x : α | (x : α ⧸ s) = g } = g • s :=
  Set.ext fun z => by
    rw [mem_leftCoset_iff, Set.mem_setOf_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]

open MulAction in
@[to_additive]
lemma orbit_mk_eq_smul (x : α) : MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) = x • s := by
  ext
  rw [orbitRel.Quotient.mem_orbit]
  simpa [mem_smul_set_iff_inv_smul_mem, ← leftRel_apply, Quotient.eq''] using Setoid.comm' _

@[to_additive]
lemma orbit_eq_out_smul (x : α ⧸ s) : MulAction.orbitRel.Quotient.orbit x = x.out • s := by
  induction x using QuotientGroup.induction_on
  simp only [orbit_mk_eq_smul, ← eq_class_eq_leftCoset, Quotient.out_eq']

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `g + s` and `s`. -/]
def leftCosetEquivSubgroup (g : α) : (g • s : Set α) ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
    fun ⟨x, _⟩ => Subtype.eq <| by simp, fun ⟨g, _⟩ => Subtype.eq <| by simp⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `s + g` and `s`. -/]
def rightCosetEquivSubgroup (g : α) : (op g • s : Set α) ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
    fun ⟨x, _⟩ => Subtype.eq <| by simp, fun ⟨g, _⟩ => Subtype.eq <| by simp⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive addGroupEquivQuotientProdAddSubgroup
  /-- A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s` -/]
noncomputable def groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ Σ L : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ Σ L : α ⧸ s, (Quotient.out L • s : Set α) :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        change
          (_root_.Subtype fun x : α => Quotient.mk'' x = L) ≃
            _root_.Subtype fun x : α => Quotient.mk'' x = Quotient.mk'' _
        simp
        rfl
    _ ≃ Σ _L : α ⧸ s, s := Equiv.sigmaCongrRight fun _ => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equiv.sigmaEquivProd _ _

variable {t : Subgroup α}

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `Subgroup.quotientEquivProdOfLE`. -/
@[to_additive (attr := simps) quotientEquivProdOfLE'
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
  of the quotient map `G → G/K`. The classical version is `AddSubgroup.quotientEquivProdOfLE`. -/]
def quotientEquivProdOfLE' (h_le : s ≤ t) (f : α ⧸ t → α)
    (hf : Function.RightInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t where
  toFun a :=
    ⟨a.map' id fun _ _ h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s
        have key : f b = f c :=
          congr_arg f (Quotient.sound' (leftRel_apply.mpr (h_le (leftRel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← leftRel_apply]⟩
  invFun a := by
    refine a.2.map' (fun (b : { x // x ∈ t}) => f a.1 * b) fun b c h => by
      rw [leftRel_apply] at h ⊢
      change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ s
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  left_inv := by
    refine Quotient.ind' fun a => ?_
    simp_rw [Quotient.map'_mk'', id, mul_inv_cancel_left]
  right_inv := by
    refine Prod.rec ?_
    refine Quotient.ind' fun a => ?_
    refine Quotient.ind' fun b => ?_
    have key : Quotient.mk'' (f (Quotient.mk'' a) * b) = Quotient.mk'' a :=
      (QuotientGroup.mk_mul_of_mem (f a) b.2).trans (hf a)
    simp_rw [Quotient.map'_mk'', id, key, inv_mul_cancel_left]

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotientEquivProdOfLE'`. -/
@[to_additive (attr := simps!) quotientEquivProdOfLE
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively. The
constructive version is `quotientEquivProdOfLE'`. -/]
noncomputable def quotientEquivProdOfLE (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLE' h_le Quotient.out Quotient.out_eq'

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t`. -/
@[to_additive
/-- If `s ≤ t`, there is an embedding `s ⧸ H.addSubgroupOf s ↪ t ⧸ H.addSubgroupOf t`. -/]
def quotientSubgroupOfEmbeddingOfLE (H : Subgroup α) (h : s ≤ t) :
    s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t where
  toFun :=
    Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      exact id
  inj' :=
    Quotient.ind₂' <| by
      intro a b h
      simpa only [Quotient.map'_mk'', QuotientGroup.eq] using h

@[to_additive (attr := simp)]
theorem quotientSubgroupOfEmbeddingOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : s) :
    quotientSubgroupOfEmbeddingOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk (inclusion h g) :=
  rfl

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H`. -/
@[to_additive
/-- If `s ≤ t`, then there is a map `H ⧸ s.addSubgroupOf H → H ⧸ t.addSubgroupOf H`. -/]
def quotientSubgroupOfMapOfLE (H : Subgroup α) (h : s ≤ t) :
    H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
theorem quotientSubgroupOfMapOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : H) :
    quotientSubgroupOfMapOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive /-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/]
def quotientMapOfLE (h : s ≤ t) : α ⧸ s → α ⧸ t :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
theorem quotientMapOfLE_apply_mk (h : s ≤ t) (g : α) :
    quotientMapOfLE h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroupOf H ↪ Π i, H ⧸ (f i).subgroupOf H`. -/
@[to_additive (attr := simps) /-- The natural embedding
`H ⧸ (⨅ i, f i).addSubgroupOf H) ↪ Π i, H ⧸ (f i).addSubgroupOf H`. -/]
def quotientiInfSubgroupOfEmbedding {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α) :
    H ⧸ (⨅ i, f i).subgroupOf H ↪ ∀ i, H ⧸ (f i).subgroupOf H where
  toFun q i := quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf,
        mem_iInf, imp_self, forall_const]

@[to_additive (attr := simp)]
theorem quotientiInfSubgroupOfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α)
    (g : H) (i : ι) :
    quotientiInfSubgroupOfEmbedding f H (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive (attr := simps) /-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/]
def quotientiInfEmbedding {ι : Type*} (f : ι → Subgroup α) : (α ⧸ ⨅ i, f i) ↪ ∀ i, α ⧸ f i where
  toFun q i := quotientMapOfLE (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, QuotientGroup.eq, mem_iInf, imp_self,
        forall_const]

@[to_additive (attr := simp)]
theorem quotientiInfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (g : α) (i : ι) :
    quotientiInfEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

end Subgroup

namespace MonoidHom

variable [Group α] {H : Type*} [Group H]

/-- An equivalence between any non-empty fiber of a `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any non-empty fiber of an `AddMonoidHom` and its kernel. -/]
def fiberEquivKer (f : α →* H) (a : α) : f ⁻¹' {f a} ≃ f.ker :=
  .trans
    (Equiv.setCongr <| Set.ext fun _ => by
      rw [mem_preimage, mem_singleton_iff, mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, mem_ker,
        smul_eq_mul, map_mul, map_inv, inv_mul_eq_one, eq_comm])
    (Subgroup.leftCosetEquivSubgroup a)

@[to_additive (attr := simp)]
lemma fiberEquivKer_apply (f : α →* H) (a : α) (g : f ⁻¹' {f a}) : f.fiberEquivKer a g = a⁻¹ * g :=
  rfl

@[to_additive (attr := simp)]
lemma fiberEquivKer_symm_apply (f : α →* H) (a : α) (g : f.ker) :
    (f.fiberEquivKer a).symm g = a * g :=
  rfl

/-- An equivalence between any fiber of a surjective `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any fiber of a surjective `AddMonoidHom` and its kernel. -/]
noncomputable def fiberEquivKerOfSurjective {f : α →* H} (hf : Function.Surjective f) (h : H) :
    f ⁻¹' {h} ≃ f.ker :=
  (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

/-- An equivalence between any two non-empty fibers of a `MonoidHom`. -/
@[to_additive /-- An equivalence between any two non-empty fibers of an `AddMonoidHom`. -/]
def fiberEquiv (f : α →* H) (a b : α) : f ⁻¹' {f a} ≃ f ⁻¹' {f b} :=
  (f.fiberEquivKer a).trans (f.fiberEquivKer b).symm

@[to_additive (attr := simp)]
lemma fiberEquiv_apply (f : α →* H) (a b : α) (g : f ⁻¹' {f a}) :
    f.fiberEquiv a b g = b * (a⁻¹ * g) :=
  rfl

@[to_additive (attr := simp)]
lemma fiberEquiv_symm_apply (f : α →* H) (a b : α) (g : f ⁻¹' {f b}) :
    (f.fiberEquiv a b).symm g = a * (b⁻¹ * g) :=
  rfl

/-- An equivalence between any two fibers of a surjective `MonoidHom`. -/
@[to_additive /-- An equivalence between any two fibers of a surjective `AddMonoidHom`. -/]
noncomputable def fiberEquivOfSurjective {f : α →* H} (hf : Function.Surjective f) (h h' : H) :
    f ⁻¹' {h} ≃ f ⁻¹' {h'} :=
  (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

end MonoidHom

namespace QuotientGroup

variable [Group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive preimageMkEquivAddSubgroupProdSet
/-- If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product
`s × t`. -/]
noncomputable def preimageMkEquivSubgroupProdSet (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t where
  toFun a :=
    ⟨⟨((Quotient.out (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out a.2.1 * a.1.1,
      show QuotientGroup.mk _ ∈ t by
        rw [mk_mul_of_mem _ a.1.2, out_eq']
        exact a.2.2⟩
  left_inv := fun ⟨a, _⟩ => Subtype.eq <| show _ * _ = a by simp
  right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ => by ext <;> simp [ha]

open MulAction in
/-- A group is made up of a disjoint union of cosets of a subgroup. -/
@[to_additive /-- An additive group is made up of a disjoint union of cosets of an additive
subgroup. -/]
lemma univ_eq_iUnion_smul (H : Subgroup α) :
    (Set.univ (α := α)) = ⋃ x : α ⧸ H, x.out • (H : Set _) := by
  simp_rw [univ_eq_iUnion_orbit H.op, orbit_eq_out_smul]
  rfl

variable (α) in
/-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientGroup.quotientBot` for a multiplicative
version. -/
@[to_additive /-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientAddGroup.quotientBot` for an
additive version. -/]
def quotientEquivSelf : α ⧸ (⊥ : Subgroup α) ≃ α where
  toFun := Quotient.lift id <| fun x y (h : leftRel ⊥ x y) ↦
    eq_of_inv_mul_eq_one <| by rwa [leftRel_apply, Subgroup.mem_bot] at h
  invFun := QuotientGroup.mk
  left_inv x := by induction x using Quotient.inductionOn; simp
  right_inv x := by simp

end QuotientGroup
