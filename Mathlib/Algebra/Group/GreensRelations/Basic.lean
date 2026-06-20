/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.Defs
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Algebra.Group.Opposite

/-!
# Basic Properties of Green's Relations

This file proves the foundational equivalences and duality properties of Green's relations,
establishing them as setoids over a semigroup.

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

public section

variable {S : Type*} [Semigroup S]


section Duality

open MulOpposite

lemma op_rightDvd_op_iff {a b : S} : RightDvd (op a) (op b) ↔ a ∣ b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

lemma op_dvd_op_iff {a b : S} : op a ∣ op b ↔ RightDvd a b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

lemma isGreenRightDvd_iff_isGreenLeftDvd_op {a b : S} :
    IsGreenRightDvd a b ↔ IsGreenLeftDvd (op a) (op b) := by
  simp only [IsGreenRightDvd, IsGreenLeftDvd, op_rightDvd_op_iff, op_inj]

lemma isGreenLeftDvd_iff_isGreenRightDvd_op {a b : S} :
    IsGreenLeftDvd a b ↔ IsGreenRightDvd (op a) (op b) := by
  simp only [IsGreenRightDvd, IsGreenLeftDvd, op_dvd_op_iff, op_inj]

lemma isGreenR_iff_isGreenL_op {a b : S} : IsGreenR a b ↔ IsGreenL (op a) (op b) := by
  simp only [IsGreenR, IsGreenL, isGreenRightDvd_iff_isGreenLeftDvd_op]

lemma isGreenL_iff_isGreenR_op {a b : S} : IsGreenL a b ↔ IsGreenR (op a) (op b) := by
  simp only [IsGreenL, IsGreenR, isGreenLeftDvd_iff_isGreenRightDvd_op]

end Duality

section Equivalences

namespace IsGreenLeftDvd

/-- Left divisibility is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenLeftDvd a a := Or.inl rfl

/-- Left divisibility is transitive. -/
@[trans] theorem trans {a b c : S} : IsGreenLeftDvd a b → IsGreenLeftDvd b c → IsGreenLeftDvd a c
  | .inl rfl, hbc => hbc
  | hab, .inl rfl => hab
  | .inr ⟨x, hx⟩, .inr ⟨y, hy⟩ => .inr ⟨x * y, by rw [hx, hy, mul_assoc]⟩

end IsGreenLeftDvd

namespace IsGreenRightDvd

/-- Right divisibility is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenRightDvd a a := Or.inl rfl

open MulOpposite in
/-- Right divisibility is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenRightDvd a b)
    (hbc : IsGreenRightDvd b c) : IsGreenRightDvd a c := by
  rw [isGreenRightDvd_iff_isGreenLeftDvd_op] at hab hbc ⊢
  exact IsGreenLeftDvd.trans hab hbc

end IsGreenRightDvd

namespace IsGreenJRel

/-- The basic J-relation step is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenJRel a a := of_eq rfl

/-- The basic J-relation step is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenJRel a b)
    (hbc : IsGreenJRel b c) : IsGreenJRel a c := by
  rcases hab, hbc with
    ⟨(h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩), (h' | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, _, h'⟩)⟩ <;>
  (simp [← mul_assoc, h' ▸ h]; grind [mul_assoc, IsGreenJRel])

end IsGreenJRel

namespace IsGreenL

/-- Green's L relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenL a a := ⟨IsGreenLeftDvd.refl a, IsGreenLeftDvd.refl a⟩

/-- Green's L relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenL a b) : IsGreenL b a := ⟨h.right, h.left⟩

/-- Green's L relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenL a b) (hbc : IsGreenL b c) : IsGreenL a c :=
  ⟨IsGreenLeftDvd.trans hab.left hbc.left, IsGreenLeftDvd.trans hbc.right hab.right⟩

/-- Green's L relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenL
  iseqv := { refl := refl, symm := symm, trans := trans }

/-- Green's L relation is preserved by right multiplication. -/
theorem mul_right (c : S) {a b : S} (h : IsGreenL a b) : IsGreenL (a * c) (b * c) := by
  grind [mul_assoc, RightDvd]

/-- Right cancellation property for elements related by Green's L relation. -/
theorem cancellation {a x u v : S} (hx : IsGreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩ <;> simp [mul_assoc, h_cancel]

end IsGreenL

namespace IsGreenR

/-- Green's R relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenR a a :=
  ⟨IsGreenRightDvd.refl a, IsGreenRightDvd.refl a⟩

/-- Green's R relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenR a b) : IsGreenR b a := ⟨h.right, h.left⟩

/-- Green's R relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenR a b) (hbc : IsGreenR b c) : IsGreenR a c :=
  ⟨IsGreenRightDvd.trans hab.left hbc.left, IsGreenRightDvd.trans hbc.right hab.right⟩

/-- Green's R relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenR
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's R relation is preserved by left multiplication. -/
theorem mul_left (c : S) {a b : S} (h : IsGreenR a b) : IsGreenR (c * a) (c * b) := by
  rw [isGreenR_iff_isGreenL_op] at h ⊢
  exact IsGreenL.mul_right (op c) h

/-- Left cancellation property for elements related by Green's R relation. -/
theorem cancellation {a x u v : S} (hx : IsGreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩ <;> simp [← mul_assoc, h_cancel]

end IsGreenR

namespace IsGreenH

/-- Green's H relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenH a a := ⟨IsGreenL.refl a, IsGreenR.refl a⟩

/-- Green's H relation is symmetric. -/
@[symm] theorem symm {a b : S} (hab : IsGreenH a b) : IsGreenH b a :=
  ⟨hab.left.symm, hab.right.symm⟩

/-- Green's H relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenH a b) (hbc : IsGreenH b c) : IsGreenH a c :=
  ⟨hab.left.trans hbc.left, hab.right.trans hbc.right⟩

/-- Green's H relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenH
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's H relation is self-dual under the opposite semigroup. -/
lemma isGreenH_iff_isGreenH_op {a b : S} : IsGreenH a b ↔ IsGreenH (op a) (op b) :=
  ⟨fun ⟨hL, hR⟩ ↦ ⟨isGreenR_iff_isGreenL_op.mp hR, isGreenL_iff_isGreenR_op.mp hL⟩,
   fun ⟨hL, hR⟩ ↦ ⟨isGreenL_iff_isGreenR_op.mpr hR, isGreenR_iff_isGreenL_op.mpr hL⟩⟩

end IsGreenH

/-- Green's L and R relations commute: `L ∘ R = R ∘ L`. -/
lemma isGreenL_commutes_isGreenR {a b z : S} (hL : IsGreenL a z) (hR : IsGreenR z b) :
    ∃ z', IsGreenR a z' ∧ IsGreenL z' b :=
  match hL, hR with
  | ⟨.inl rfl, _⟩, hR' | ⟨_, .inl rfl⟩, hR' => ⟨b, hR', IsGreenL.refl b⟩
  | hL', ⟨.inl rfl, _⟩ | hL', ⟨_, .inl rfl⟩ => ⟨a, IsGreenR.refl a, hL'⟩
  | ⟨.inr ⟨u, hu⟩, .inr ⟨v, hv⟩⟩, ⟨.inr ⟨x, hx⟩, .inr ⟨y, hy⟩⟩ =>
    ⟨a * y,
      ⟨.inr ⟨x, by simp [hu, ← hy, ← hx, mul_assoc]⟩, .inr ⟨y, rfl⟩⟩,
      ⟨.inr ⟨u, by simp [hu, ← hy, mul_assoc]⟩, .inr ⟨v, by simp [← hv, hy, ← mul_assoc]⟩⟩⟩

namespace IsGreenD

/-- Green's D relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenD a a := ⟨a, IsGreenL.refl a, IsGreenR.refl a⟩

/-- Green's D relation is symmetric. -/
@[symm] theorem symm {a b : S} : IsGreenD a b → IsGreenD b a
  | ⟨_, hL, hR⟩ => let ⟨y, hyR, hyL⟩ := isGreenL_commutes_isGreenR hL hR; ⟨y, hyL.symm, hyR.symm⟩

/-- Green's D relation is transitive. -/
@[trans] theorem trans {a b c : S} : IsGreenD a b → IsGreenD b c → IsGreenD a c
  | ⟨_, hL1, hR1⟩, ⟨_, hL2, hR2⟩ =>
    let ⟨z, hR3, hL3⟩ := isGreenL_commutes_isGreenR hL2.symm hR1.symm
    ⟨z, hL1.trans hL3.symm, hR3.symm.trans hR2⟩

/-- Green's D relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenD
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's D relation is self-dual under the opposite semigroup. -/
lemma isGreenD_iff_isGreenD_op {a b : S} : IsGreenD a b ↔ IsGreenD (op a) (op b) :=
  ⟨fun ⟨_, hL, hR⟩ ↦
    let ⟨y, hyR, hyL⟩ := isGreenL_commutes_isGreenR hL hR
    ⟨op y, isGreenR_iff_isGreenL_op.mp hyR, isGreenL_iff_isGreenR_op.mp hyL⟩,
   fun ⟨_, hL, hR⟩ ↦
    let ⟨y, hyR, hyL⟩ := isGreenL_commutes_isGreenR (isGreenL_iff_isGreenR_op.mpr hR).symm
      (isGreenR_iff_isGreenL_op.mpr hL).symm
    ⟨y, hyL.symm, hyR.symm⟩⟩

end IsGreenD

namespace IsGreenJ

/-- Green's J relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenJ a a := ⟨IsGreenJRel.refl a, IsGreenJRel.refl a⟩

/-- Green's J relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenJ a b) : IsGreenJ b a := ⟨h.right, h.left⟩

/-- Green's J relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenJ a b) (hbc : IsGreenJ b c) : IsGreenJ a c :=
  ⟨hab.left.trans hbc.left, hbc.right.trans hab.right⟩

/-- Green's J relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenJ
  iseqv := { refl := refl, symm := symm, trans := trans }

end IsGreenJ

end Equivalences
