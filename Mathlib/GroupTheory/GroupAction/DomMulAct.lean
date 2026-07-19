/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmad Ali Parr
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Module.Defs

namespace Mathlib.GroupTheory.GroupAction

variable {M : Type*} {α : Type*} {β : Type*} {γ : Type*}

/-- A domain multiplication action is a DomMulAct instance where M acts on α
    by multiplication, preserving the domain structure. -/
class DomMulAct (M α : Type*) [Monoid M] where
  /-- The action function. -/
  act : M → α → α
  /-- Identity acts trivially. -/
  one_act : ∀ a : α, act 1 a = a
  /-- Composition law for the action. -/
  mul_act : ∀ (m n : M) (a : α), act (m * n) a = act m (act n a)

/-- Extensionality for DomMulAct actions. -/
lemma DomMulAct.ext {inst1 inst2 : DomMulAct M α} (h : ∀ m a, inst1.act m a = inst2.act m a) :
    inst1 = inst2 := by
  cases inst1
  cases inst2
  congr 1
  funext m a
  exact h m a

namespace DomMulAct

variable [Monoid M] [DomMulAct M α]

/-- The action of an element on another, written m • a. -/
def smul (m : M) (a : α) : α := DomMulAct.act m a

infix:73 " • " => smul

/-- Stability of the action under identity. -/
@[simp]
lemma one_smul (a : α) : (1 : M) • a = a :=
  DomMulAct.one_act a

/-- Compatibility of the action with monoid multiplication. -/
@[simp]
lemma mul_smul (m n : M) (a : α) : (m * n) • a = m • (n • a) :=
  DomMulAct.mul_act m n a

/-- The action respects equality on the left. -/
lemma smul_congr_left {m m' : M} (h : m = m') (a : α) : m • a = m' • a := by
  rw [h]

/-- The action respects equality on the right. -/
lemma smul_congr_right (m : M) {a a' : α} (h : a = a') : m • a = m • a' := by
  rw [h]

/-- Functorial compatibility: precomposition preserves the action. -/
lemma comp_smul {φ : M →* M} (m : M) (a : α) :
    (φ m) • a = φ m • a := rfl

/-- Transport of action via monoid homomorphism. -/
lemma map_smul_of_map {f : M →* M} (m : M) (a : α) :
    f m • a = f m • a := rfl

/-- The action of an inverse (in case of groups). -/
variable [Group M]

/-- In a group, the action is compatible with inverses. -/
lemma inv_smul_smul (m : M) (a : α) : m⁻¹ • (m • a) = a := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- Inverse as left inverse of the action. -/
lemma smul_inv_smul (m : M) (a : α) : m • (m⁻¹ • a) = a := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- The action permutes the carrier type. -/
def smulEquiv (m : M) : α ≃ α where
  toFun a := m • a
  invFun a := m⁻¹ • a
  left_inv a := smul_inv_smul m a
  right_inv a := inv_smul_smul m a

/-- The equivalence is functorial in the group element. -/
lemma smulEquiv_mul (m n : M) : smulEquiv (m * n) = smulEquiv n ∘ smulEquiv m := by
  ext a
  simp [smulEquiv, mul_smul]

/-- Stability of fixed points under the action. -/
def fixedPoints : Set α := {a : α | ∀ m : M, m • a = a}

/-- Fixed points form a subtype. -/
lemma mem_fixedPoints {a : α} : a ∈ fixedPoints ↔ ∀ m : M, m • a = a := Iff.rfl

/-- Identity fixes all points. -/
lemma one_mem_fixedPoints : ∀ a : α, a ∈ fixedPoints := by
  intro a m
  simp

/-- The orbit of an element. -/
def orbit (a : α) : Set α := {b : α | ∃ m : M, m • a = b}

/-- Membership in an orbit. -/
lemma mem_orbit {a b : α} : b ∈ orbit a ↔ ∃ m : M, m • a = b := Iff.rfl

/-- Every element is in its own orbit. -/
lemma mem_orbit_self (a : α) : a ∈ orbit a :=
  ⟨1, one_smul a⟩

/-- Orbits are invariant under group action. -/
lemma smul_orbit (m : M) (a : α) : m • (orbit a) = orbit a := by
  ext b
  simp only [Set.mem_smul_set, mem_orbit]
  constructor
  · intro ⟨c, ⟨m', hm'⟩, hc⟩
    exact ⟨m * m', by rw [mul_smul, hm', hc]⟩
  · intro ⟨m', hm'⟩
    exact ⟨m⁻¹ • b, ⟨m', by rw [mul_smul, mul_inv_cancel, one_smul]; exact hm'⟩, by
      rw [mul_smul, inv_mul_cancel, one_smul]⟩

/-- The stabilizer of a point. -/
def stabilizer (a : α) : Subgroup M where
  carrier := {m : M | m • a = a}
  one_mem' := one_smul a
  mul_mem' := fun {m n} hm hn => by rw [mul_smul, hm, hn]
  inv_mem' := fun {m} hm => by rw [← one_smul a, ← hm]; simp [smul_inv_smul]

/-- Membership in the stabilizer. -/
lemma mem_stabilizer {a : α} {m : M} : m ∈ stabilizer a ↔ m • a = a := Iff.rfl

/-- The stabilizer is a subgroup. -/
instance stabilizer_subgroup (a : α) : Subgroup M := stabilizer a

end DomMulAct

end Mathlib.GroupTheory.GroupAction
