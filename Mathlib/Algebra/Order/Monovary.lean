/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Order.Monotone.Monovary
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Synonym
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Monovarying functions and algebraic operations

This file characterises the interaction of ordered algebraic structures with monovariance
of functions.

## See also

`Mathlib.Algebra.Order.Rearrangement` for the n-ary rearrangement inequality
-/

public section

variable {ι α β : Type*}

/-! ### Algebraic operations on monovarying functions -/

section OrderedCommGroup

section
variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

@[to_additive (attr := simp)]
lemma monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)]
lemma antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)] lemma monovary_inv_left : Monovary f⁻¹ g ↔ Antivary f g := by
  simp [Monovary, Antivary]

@[to_additive (attr := simp)] lemma antivary_inv_left : Antivary f⁻¹ g ↔ Monovary f g := by
  simp [Monovary, Antivary]

@[to_additive] lemma MonovaryOn.mul_left (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    MonovaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

@[to_additive] lemma AntivaryOn.mul_left (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    AntivaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

@[to_additive] lemma MonovaryOn.div_left (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    MonovaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

@[to_additive] lemma AntivaryOn.div_left (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    AntivaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

@[to_additive] lemma MonovaryOn.pow_left (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left' (hfg hi hj hij) _

@[to_additive] lemma AntivaryOn.pow_left (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left' (hfg hi hj hij) _

@[to_additive]
lemma Monovary.mul_left (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) : Monovary (f₁ * f₂) g :=
  fun _i _j hij ↦ mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
lemma Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁ * f₂) g :=
  fun _i _j hij ↦ mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
lemma Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive]
lemma Antivary.div_left (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive] lemma Monovary.pow_left (hfg : Monovary f g) (n : ℕ) : Monovary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left' (hfg hij) _

@[to_additive] lemma Antivary.pow_left (hfg : Antivary f g) (n : ℕ) : Antivary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left' (hfg hij) _

end

section
variable [PartialOrder α] [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

@[to_additive (attr := simp)]
lemma monovaryOn_inv_right : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)]
lemma antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)] lemma monovary_inv_right : Monovary f g⁻¹ ↔ Antivary f g := by
  simpa [Monovary, Antivary] using forall_comm

@[to_additive (attr := simp)] lemma antivary_inv_right : Antivary f g⁻¹ ↔ Monovary f g := by
  simpa [Monovary, Antivary] using forall_comm
end

section
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

@[to_additive] lemma monovaryOn_inv : MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by simp
@[to_additive] lemma antivaryOn_inv : AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by simp

@[to_additive] lemma monovary_inv : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by simp
@[to_additive] lemma antivary_inv : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by simp

end

@[to_additive] alias ⟨MonovaryOn.of_inv_left, AntivaryOn.inv_left⟩ := monovaryOn_inv_left
@[to_additive] alias ⟨AntivaryOn.of_inv_left, MonovaryOn.inv_left⟩ := antivaryOn_inv_left
@[to_additive] alias ⟨MonovaryOn.of_inv_right, AntivaryOn.inv_right⟩ := monovaryOn_inv_right
@[to_additive] alias ⟨AntivaryOn.of_inv_right, MonovaryOn.inv_right⟩ := antivaryOn_inv_right
@[to_additive] alias ⟨MonovaryOn.of_inv, MonovaryOn.inv⟩ := monovaryOn_inv
@[to_additive] alias ⟨AntivaryOn.of_inv, AntivaryOn.inv⟩ := antivaryOn_inv
@[to_additive] alias ⟨Monovary.of_inv_left, Antivary.inv_left⟩ := monovary_inv_left
@[to_additive] alias ⟨Antivary.of_inv_left, Monovary.inv_left⟩ := antivary_inv_left
@[to_additive] alias ⟨Monovary.of_inv_right, Antivary.inv_right⟩ := monovary_inv_right
@[to_additive] alias ⟨Antivary.of_inv_right, Monovary.inv_right⟩ := antivary_inv_right
@[to_additive] alias ⟨Monovary.of_inv, Monovary.inv⟩ := monovary_inv
@[to_additive] alias ⟨Antivary.of_inv, Antivary.inv⟩ := antivary_inv

end OrderedCommGroup

section LinearOrderedCommGroup
variable [Preorder α] [CommGroup β] [LinearOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α}
  {g g₁ g₂ : ι → β}

@[to_additive] lemma MonovaryOn.mul_right (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    MonovaryOn f (g₁ * g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) <| h₂ hi hj

@[to_additive] lemma AntivaryOn.mul_right (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    AntivaryOn f (g₁ * g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) <| h₂ hi hj

@[to_additive] lemma MonovaryOn.div_right (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    MonovaryOn f (g₁ / g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) <| h₂ hj hi

@[to_additive] lemma AntivaryOn.div_right (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    AntivaryOn f (g₁ / g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) <| h₂ hj hi

@[to_additive] lemma MonovaryOn.pow_right (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn f (g ^ n) s := fun _i hi _j hj hij ↦ hfg hi hj <| lt_of_pow_lt_pow_left' _ hij

@[to_additive] lemma AntivaryOn.pow_right (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn f (g ^ n) s := fun _i hi _j hj hij ↦ hfg hi hj <| lt_of_pow_lt_pow_left' _ hij

@[to_additive] lemma Monovary.mul_right (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h

@[to_additive] lemma Antivary.mul_right (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h

@[to_additive] lemma Monovary.div_right (h₁ : Monovary f g₁) (h₂ : Antivary f g₂) :
    Monovary f (g₁ / g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_div_lt_div hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h

@[to_additive] lemma Antivary.div_right (h₁ : Antivary f g₁) (h₂ : Monovary f g₂) :
    Antivary f (g₁ / g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_div_lt_div hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h

@[to_additive] lemma Monovary.pow_right (hfg : Monovary f g) (n : ℕ) : Monovary f (g ^ n) :=
  fun _i _j hij ↦ hfg <| lt_of_pow_lt_pow_left' _ hij

@[to_additive] lemma Antivary.pow_right (hfg : Antivary f g) (n : ℕ) : Antivary f (g ^ n) :=
  fun _i _j hij ↦ hfg <| lt_of_pow_lt_pow_left' _ hij

end LinearOrderedCommGroup

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

lemma MonovaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : MonovaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)

lemma AntivaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : AntivaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)

lemma MonovaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn (f ^ n) g s :=
  fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _

lemma AntivaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn (f ^ n) g s :=
  fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _

lemma Monovary.mul_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) :
    Monovary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

lemma Antivary.mul_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) :
    Antivary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

lemma Monovary.pow_left₀ (hf : 0 ≤ f) (hfg : Monovary f g) (n : ℕ) : Monovary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _

lemma Antivary.pow_left₀ (hf : 0 ≤ f) (hfg : Antivary f g) (n : ℕ) : Antivary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _

end OrderedSemiring

section LinearOrderedSemiring
variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι → α} {g g₁ g₂ : ι → β}

lemma MonovaryOn.mul_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 ≤ g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : MonovaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

lemma AntivaryOn.mul_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 ≤ g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : AntivaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

lemma MonovaryOn.pow_right₀ (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm

lemma AntivaryOn.pow_right₀ (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm

lemma Monovary.mul_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

lemma Antivary.mul_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

lemma Monovary.pow_right₀ (hg : 0 ≤ g) (hfg : Monovary f g) (n : ℕ) : Monovary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm

lemma Antivary.pow_right₀ (hg : 0 ≤ g) (hfg : Antivary f g) (n : ℕ) : Antivary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm

end LinearOrderedSemiring

section LinearOrderedSemifield

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

@[simp]
lemma monovaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hi) (hf _ hj)

@[simp]
lemma antivaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hj) (hf _ hi)

@[simp] lemma monovary_inv_left₀ (hf : StrongLT 0 f) : Monovary f⁻¹ g ↔ Antivary f g :=
  forall₃_congr fun _i _j _ ↦ inv_le_inv₀ (hf _) (hf _)

@[simp] lemma antivary_inv_left₀ (hf : StrongLT 0 f) : Antivary f⁻¹ g ↔ Monovary f g :=
  forall₃_congr fun _i _j _ ↦ inv_le_inv₀ (hf _) (hf _)

lemma MonovaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : MonovaryOn (f₁ / f₂) g s :=
  fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) <| h₂ hi hj hij

lemma AntivaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : AntivaryOn (f₁ / f₂) g s :=
  fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) <| h₂ hi hj hij

lemma Monovary.div_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Monovary f₁ g)
    (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) <| h₂ hij

lemma Antivary.div_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
    (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) <| h₂ hij

end

section
variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

@[simp]
lemma monovaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s :=
  forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp]
lemma antivaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s :=
  forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp] lemma monovary_inv_right₀ (hg : StrongLT 0 g) : Monovary f g⁻¹ ↔ Antivary f g :=
  forall_comm.trans <| forall₂_congr fun i j ↦ by simp [inv_lt_inv₀ (hg _) (hg _)]

@[simp] lemma antivary_inv_right₀ (hg : StrongLT 0 g) : Antivary f g⁻¹ ↔ Monovary f g :=
  forall_comm.trans <| forall₂_congr fun i j ↦ by simp [inv_lt_inv₀ (hg _) (hg _)]

lemma MonovaryOn.div_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 < g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : MonovaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

lemma AntivaryOn.div_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 < g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : AntivaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

lemma Monovary.div_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Monovary f g₁)
    (h₂ : Antivary f g₂) : Monovary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

lemma Antivary.div_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
    (h₂ : Monovary f g₂) : Antivary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

end

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

lemma monovaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by
  rw [monovaryOn_inv_left₀ hf, antivaryOn_inv_right₀ hg]
lemma antivaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by
  rw [antivaryOn_inv_left₀ hf, monovaryOn_inv_right₀ hg]

lemma monovary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by
  rw [monovary_inv_left₀ hf, antivary_inv_right₀ hg]
lemma antivary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by
  rw [antivary_inv_left₀ hf, monovary_inv_right₀ hg]

end

alias ⟨MonovaryOn.of_inv_left₀, AntivaryOn.inv_left₀⟩ := monovaryOn_inv_left₀
alias ⟨AntivaryOn.of_inv_left₀, MonovaryOn.inv_left₀⟩ := antivaryOn_inv_left₀
alias ⟨MonovaryOn.of_inv_right₀, AntivaryOn.inv_right₀⟩ := monovaryOn_inv_right₀
alias ⟨AntivaryOn.of_inv_right₀, MonovaryOn.inv_right₀⟩ := antivaryOn_inv_right₀
alias ⟨MonovaryOn.of_inv₀, MonovaryOn.inv₀⟩ := monovaryOn_inv₀
alias ⟨AntivaryOn.of_inv₀, AntivaryOn.inv₀⟩ := antivaryOn_inv₀
alias ⟨Monovary.of_inv_left₀, Antivary.inv_left₀⟩ := monovary_inv_left₀
alias ⟨Antivary.of_inv_left₀, Monovary.inv_left₀⟩ := antivary_inv_left₀
alias ⟨Monovary.of_inv_right₀, Antivary.inv_right₀⟩ := monovary_inv_right₀
alias ⟨Antivary.of_inv_right₀, Monovary.inv_right₀⟩ := antivary_inv_right₀
alias ⟨Monovary.of_inv₀, Monovary.inv₀⟩ := monovary_inv₀
alias ⟨Antivary.of_inv₀, Antivary.inv₀⟩ := antivary_inv₀

end LinearOrderedSemifield

/-! ### Rearrangement inequality characterisation -/

section LinearOrderedAddCommGroup
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

lemma monovaryOn_iff_forall_smul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) • (g j - g i) := by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm

lemma antivaryOn_iff_forall_smul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) • (g j - g i) ≤ 0 :=
  monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_forall_smul_nonneg]; rfl

lemma monovary_iff_forall_smul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) • (g j - g i) :=
  monovaryOn_univ.symm.trans <| monovaryOn_iff_forall_smul_nonneg.trans <| by
    simp only [Set.mem_univ, forall_true_left]

lemma antivary_iff_forall_smul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) • (g j - g i) ≤ 0 :=
monovary_toDual_right.symm.trans <| by rw [monovary_iff_forall_smul_nonneg]; rfl

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovaryOn_iff_smul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g j + f j • g i ≤ f i • g i + f j • g j :=
  monovaryOn_iff_forall_smul_nonneg.trans <| forall₄_congr fun i _ j _ ↦ by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivaryOn_iff_smul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g i + f j • g j ≤ f i • g j + f j • g i :=
  monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_smul_rearrangement]; rfl

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_iff_smul_rearrangement :
    Monovary f g ↔ ∀ i j, f i • g j + f j • g i ≤ f i • g i + f j • g j :=
  monovaryOn_univ.symm.trans <| monovaryOn_iff_smul_rearrangement.trans <| by
    simp only [Set.mem_univ, forall_true_left]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_iff_smul_rearrangement :
    Antivary f g ↔ ∀ i j, f i • g i + f j • g j ≤ f i • g j + f j • g i :=
  monovary_toDual_right.symm.trans <| by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_smul_nonneg
alias ⟨Antivary.sub_smul_sub_nonpos, _⟩ := antivary_iff_forall_smul_nonpos
alias ⟨Monovary.smul_add_smul_le_smul_add_smul, _⟩ := monovary_iff_smul_rearrangement
alias ⟨Antivary.smul_add_smul_le_smul_add_smul, _⟩ := antivary_iff_smul_rearrangement
alias ⟨MonovaryOn.smul_add_smul_le_smul_add_smul, _⟩ := monovaryOn_iff_smul_rearrangement
alias ⟨AntivaryOn.smul_add_smul_le_smul_add_smul, _⟩ := antivaryOn_iff_smul_rearrangement

end LinearOrderedAddCommGroup

section LinearOrderedRing
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

lemma monovaryOn_iff_forall_mul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]

lemma antivaryOn_iff_forall_mul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]

lemma monovary_iff_forall_mul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

lemma antivary_iff_forall_mul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovaryOn_iff_mul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivaryOn_iff_mul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

/-- Two functions monovary iff the rearrangement inequality holds. -/
lemma monovary_iff_mul_rearrangement :
    Monovary f g ↔ ∀ i j, f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
lemma antivary_iff_mul_rearrangement :
    Antivary f g ↔ ∀ i j, f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Antivary.sub_mul_sub_nonpos, _⟩ := antivary_iff_forall_mul_nonpos
alias ⟨Monovary.mul_add_mul_le_mul_add_mul, _⟩ := monovary_iff_mul_rearrangement
alias ⟨Antivary.mul_add_mul_le_mul_add_mul, _⟩ := antivary_iff_mul_rearrangement
alias ⟨MonovaryOn.mul_add_mul_le_mul_add_mul, _⟩ := monovaryOn_iff_mul_rearrangement
alias ⟨AntivaryOn.mul_add_mul_le_mul_add_mul, _⟩ := antivaryOn_iff_mul_rearrangement

end LinearOrderedRing
