/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise actions on sets

This file proves that several kinds of actions of a type `α` on another type `β` transfer to actions
of `α`/`Set α` on `Set β`.

## Implementation notes

* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.
-/

assert_not_exists MonoidWithZero OrderedAddCommMonoid

open Function MulOpposite
open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

@[to_additive vadd_set_prod]
lemma smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t : Set β) :
    c • (s ×ˢ t) = (c • s) ×ˢ (c • t) :=
  prodMap_image_prod (c • ·) (c • ·) s t

@[deprecated (since := "2025-03-11")]
alias vadd_set_sum := vadd_set_prod

@[to_additive]
lemma smul_set_pi {G ι : Type*} {α : ι → Type*} [Group G] [∀ i, MulAction G (α i)]
    (c : G) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_surjective c I s fun _ _ ↦ (MulAction.bijective c).surjective

@[to_additive]
lemma smul_set_pi_of_isUnit {M ι : Type*} {α : ι → Type*} [Monoid M] [∀ i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  lift c to Mˣ using hc
  exact smul_set_pi c I s

section Mul
variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive] lemma smul_set_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image2_right

open scoped RightActions in
@[to_additive] lemma op_smul_set_subset_mul : a ∈ t → s <• a ⊆ s * t := image_subset_image2_left

@[to_additive]
theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  rfl

@[to_additive (attr := simp)]
theorem iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _

@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image2_subset_iff_left

@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image2_subset_iff_right

@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s ∪ b • s := by
  rw [insert_eq, union_mul, singleton_mul, singleton_mul]; rfl

open scoped RightActions
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a ∪ s <• b := by
  rw [insert_eq, mul_union, mul_singleton, mul_singleton]; rfl

@[to_additive] lemma range_mul {ι : Sort*} (a : α) (f : ι → α) :
    range (fun i ↦ a * f i) = a • range f := range_smul a f

end Mul

@[to_additive]
lemma image_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _

open scoped RightActions in
@[to_additive]
lemma image_op_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a := image_comm fun _ ↦ map_mul ..

section Semigroup
variable [Semigroup α]

@[to_additive]
lemma op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

@[to_additive]
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 * p.2 :=
  pairwiseDisjoint_image_right_iff fun _ _ ↦ mul_right_injective _

end IsLeftCancelMul

@[to_additive]
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ ↦ Commute.set_image <| smul_comm _ _⟩

@[to_additive]
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image_image2_distrib_right <| smul_comm _⟩

@[to_additive]
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_left_comm smul_comm⟩

@[to_additive]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]

@[to_additive]
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_image_left_comm <| smul_assoc _⟩

@[to_additive]
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc _ _ _ := image2_assoc smul_assoc

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun _ S ↦ (congr_arg fun f ↦ f '' S) <| funext fun _ ↦ op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `Set α`
on `Set β`. -/
@[to_additive
/-- An additive action of an additive monoid `α` on a type `β` gives an additive action of `Set α`
on `Set β` -/]
protected noncomputable def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Set β`. -/
@[to_additive
/-- An additive action of an additive monoid on a type `β` gives an additive action on `Set β`. -/]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul _ _ _ := by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]
lemma mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]
theorem smul_set_subset_smul_set_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
theorem smul_set_subset_iff_subset_inv_smul_set : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _

@[to_additive]
theorem subset_smul_set_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _

@[to_additive]
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a

@[to_additive]
theorem smul_set_iInter {ι : Sort*}
    (a : α) (t : ι → Set β) : (a • ⋂ i, t i) = ⋂ i, a • t i :=
  image_iInter (MulAction.bijective a) t

@[to_additive]
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective a) _ _

open scoped symmDiff in
@[to_additive]
theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a

@[to_additive (attr := simp)]
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]
theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_diff, smul_set_sdiff, smul_set_univ]

@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]

@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]
theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s :=
  (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl

@[to_additive]
theorem iUnion_smul_eq_setOf_exists {s : Set β} : ⋃ g : α, g • s = { a | ∃ g : α, g • a ∈ s } := by
  simp_rw [← iUnion_setOf, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[to_additive (attr := simp)]
lemma inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
lemma inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
lemma disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t :=
  disjoint_image_iff <| MulAction.injective _

@[to_additive]
lemma disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]
lemma disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)

/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(s⁻¹ * s) ∩ (t⁻¹ * t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup. -/
@[to_additive
/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(-s + s) ∩ (-t + t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup.
-/]
lemma exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a b : α) :
    ∃ z : α, a • s ∩ b • t ⊆ z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s ∩ b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s ∩ b • t ⊆ (z • s⁻¹) * s ∩ ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

end Group

section Monoid
variable [Monoid α] [MulAction α β] {s : Set β} {a : α} {b : β}

@[simp] lemma mem_invOf_smul_set [Invertible a] : b ∈ ⅟a • s ↔ a • b ∈ s :=
  mem_inv_smul_set_iff (a := unitOfInvertible a)

end Monoid

section Group
variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
lemma smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]
lemma smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a ↦ x.2 / f x.1 * f a := by simp [smul_graphOn]

end Group

section CommGroup
variable [CommGroup α]

@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]

end CommGroup
end Set
