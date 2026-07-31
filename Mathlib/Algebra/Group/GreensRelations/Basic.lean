/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs

/-!
# Green's Relations: Definitions and Basic Properties

This file contains the fundamental definitions of Green's relations (L, R, H, D, and J)
on a general semigroup, proves their foundational equivalences and duality properties,
and establishes them as setoids over a semigroup. It also defines the corresponding
equivalence classes as sets and quotient types, and introduces the notions of
regular elements and regular D-classes.

## Main definitions

* `IsGreenLeftDvd`: Left divisibility in a semigroup.
* `IsGreenRightDvd`: Right divisibility in a semigroup.
* `IsGreenJRel`: The basic step of being a two-sided multiple.
* `IsGreenL`: Green's L relation (generating the same left ideal).
* `IsGreenR`: Green's R relation (generating the same right ideal).
* `IsGreenH`: Green's H relation (the intersection of L and R).
* `IsGreenD`: Green's D relation (the composition of L and R).
* `IsGreenJ`: Green's J relation (generating the same two-sided ideal).
* `IsGreenL.eqvClass` (and similar for R, H, D, J): The equivalence class as a `Set S`.
* `GreenLClass S` (and similar for R, H, D, J): The quotient type of `S` by Green's relations.
* `IsGreenRegular`: A predicate indicating that an element `a` is regular (`a * s * a = a`).
* `IsRegularDClass`: A predicate indicating that all elements in a D-class are regular.

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

variable {S : Type*} [Semigroup S]

/-- `IsGreenLeftDvd a b` means that `a` is a left multiple of `b`,
  i.e., `a = b` or `a = z * b`. -/
abbrev IsGreenLeftDvd (a b : S) : Prop := a = b ∨ RightDvd b a

/-- `IsGreenRightDvd a b` means that `a` is a right multiple of `b`,
  i.e., `a = b` or `a = b * z`. -/
abbrev IsGreenRightDvd (a b : S) : Prop := a = b ∨ b ∣ a

/-- `IsGreenHDvd a b` means `a` is both a left and a right multiple of `b`. -/
abbrev IsGreenHDvd (a b : S) : Prop := IsGreenLeftDvd a b ∧ IsGreenRightDvd a b

/-- `IsGreenJRel a b` represents the basic step of being a two-sided multiple.
  `a` is related to `b` if `a = b`, `a = u * b`, `a = b * v`, or `a = u * b * v`. -/
inductive IsGreenJRel (a b : S) : Prop
  /-- `a` and `b` are equal. -/
  | of_eq (h : a = b)
  /-- `a` is a left multiple of `b`. -/
  | mul_left (u : S) (h : a = u * b)
  /-- `a` is a right multiple of `b`. -/
  | mul_right (v : S) (h : a = b * v)
  /-- `a` is a two-sided multiple of `b`. -/
  | mul_both (u v : S) (h : a = u * b * v)

/-- Green's L relation: `a` and `b` generate the same left ideal. -/
abbrev IsGreenL (a b : S) : Prop := IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a

/-- Green's R relation: `a` and `b` generate the same right ideal. -/
abbrev IsGreenR (a b : S) : Prop := IsGreenRightDvd a b ∧ IsGreenRightDvd b a

/-- Green's H relation: the intersection of Green's L and Green's R relations. -/
abbrev IsGreenH (a b : S) : Prop := IsGreenL a b ∧ IsGreenR a b

/-- Green's D relation: the composition of Green's L and Green's R relations.
Here defined explicitly as the existence of an intermediate element `z`. -/
abbrev IsGreenD (a b : S) : Prop := ∃ z, IsGreenL a z ∧ IsGreenR z b

/-- Green's J relation: `a` and `b` generate the same two-sided ideal. -/
abbrev IsGreenJ (a b : S) : Prop := IsGreenJRel a b ∧ IsGreenJRel b a


section Duality

open MulOpposite

-- TODO: This lemma belongs upstream in mathlib
-- (e.g., `Mathlib.Algebra.Group.Opposite`).
-- It should be moved there in a future PR.
/-- Right divisibility in the opposite semigroup
  is equivalent to left divisibility. -/
lemma op_rightDvd_op_iff {a b : S} :
    RightDvd (op a) (op b) ↔ a ∣ b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

-- TODO: This lemma belongs upstream in mathlib
-- (e.g., `Mathlib.Algebra.Group.Opposite`).
-- It should be moved there in a future PR.
/-- Left divisibility in the opposite semigroup
  is equivalent to right divisibility. -/
lemma op_dvd_op_iff {a b : S} :
    op a ∣ op b ↔ RightDvd a b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

/-- Green's right divisibility is equivalent to
  left divisibility in the opposite semigroup. -/
lemma isGreenRightDvd_iff_isGreenLeftDvd_op {a b : S} :
    IsGreenRightDvd a b ↔ IsGreenLeftDvd (op a) (op b) := by
  simp only [IsGreenRightDvd, IsGreenLeftDvd, op_rightDvd_op_iff, op_inj]

/-- Green's left divisibility is equivalent to
  right divisibility in the opposite semigroup. -/
lemma isGreenLeftDvd_iff_isGreenRightDvd_op {a b : S} :
    IsGreenLeftDvd a b ↔ IsGreenRightDvd (op a) (op b) := by
  simp only [IsGreenRightDvd, IsGreenLeftDvd, op_dvd_op_iff, op_inj]

/-- Green's R relation is equivalent to L relation
  in the opposite semigroup. -/
lemma isGreenR_iff_isGreenL_op {a b : S} :
    IsGreenR a b ↔ IsGreenL (op a) (op b) := by
  simp only [IsGreenR, IsGreenL, isGreenRightDvd_iff_isGreenLeftDvd_op]

/-- Green's L relation is equivalent to R relation
  in the opposite semigroup. -/
lemma isGreenL_iff_isGreenR_op {a b : S} :
    IsGreenL a b ↔ IsGreenR (op a) (op b) := by
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

namespace IsGreenHDvd

/-- Green's H-divisibility relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenHDvd a a :=
  ⟨IsGreenLeftDvd.refl a, IsGreenRightDvd.refl a⟩

/-- Green's H-divisibility relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenHDvd a b) (hbc : IsGreenHDvd b c) :
    IsGreenHDvd a c :=
  ⟨IsGreenLeftDvd.trans hab.1 hbc.1, IsGreenRightDvd.trans hab.2 hbc.2⟩

end IsGreenHDvd

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
protected abbrev setoid (S : Type*) [Semigroup S] : Setoid S where
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
protected abbrev setoid (S : Type*) [Semigroup S] : Setoid S where
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
protected abbrev setoid (S : Type*) [Semigroup S] : Setoid S where
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
protected abbrev setoid (S : Type*) [Semigroup S] : Setoid S where
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
protected abbrev setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenJ
  iseqv := { refl := refl, symm := symm, trans := trans }

end IsGreenJ

end Equivalences

section SetsAndRegularity

namespace IsGreenL

/-- The equivalence class of `x` under Green's L relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := { y | IsGreenL y x }

end IsGreenL

namespace IsGreenR

/-- The equivalence class of `x` under Green's R relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := { y | IsGreenR y x }

end IsGreenR

namespace IsGreenH

/-- The equivalence class of `x` under Green's H relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := { y | IsGreenH y x }

/-- The H-class of `x` is the intersection of its L-class and R-class. -/
lemma eqvClass_eq_inter (x : S) :
    eqvClass x = IsGreenL.eqvClass x ∩ IsGreenR.eqvClass x := by
  ext y
  rfl

open MulOpposite in
/-- An equivalence between the H-class of `a` and the H-class of `op a`. -/
abbrev equivHClassOp (a : S) : eqvClass a ≃ eqvClass (op a) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨op x, isGreenH_iff_isGreenH_op.mp hx⟩
  invFun := fun ⟨y, hy⟩ ↦ ⟨unop y, isGreenH_iff_isGreenH_op.mpr (by rwa [op_unop])⟩
  left_inv := fun ⟨x, _⟩ ↦ Subtype.ext (unop_op x)
  right_inv := fun ⟨y, _⟩ ↦ Subtype.ext (op_unop y)

end IsGreenH

namespace IsGreenD

/-- The equivalence class of `x` under Green's D relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := { y | IsGreenD y x }

end IsGreenD

namespace IsGreenJ

/-- The equivalence class of `x` under Green's J relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := { y | IsGreenJ y x }

end IsGreenJ

/-- An element `a` is regular if there exists `s` such that `a * s * a = a`. -/
abbrev IsGreenRegular (a : S) := ∃ s, a * s * a = a

/-- A D-class is regular if all its elements are regular. -/
abbrev IsRegularDClass (D : Set S) := ∀ x ∈ D, IsGreenRegular x

end SetsAndRegularity

section QuotientAPI

/-- The quotient type of `S` by Green's L relation. -/
abbrev GreenLClass (S : Type*) [Semigroup S] := Quotient (IsGreenL.setoid S)

namespace GreenLClass

/-- Constructs the Green's L-class of an element `x`. -/
abbrev mk (x : S) : GreenLClass S := Quotient.mk (IsGreenL.setoid S) x

/-- The projection map to Green's L-classes is surjective. -/
lemma mk_surjective : Function.Surjective (mk : S → GreenLClass S) :=
  @Quotient.exists_rep _ (IsGreenL.setoid S)

/-- Two elements have the same Green's L-class if and only if they are L-related. -/
lemma mk_eq_mk_iff {a b : S} : mk a = mk b ↔ IsGreenL a b := by
  dsimp [mk, IsGreenL.setoid]
  exact Quotient.eq

instance [Inhabited S] : Inhabited (GreenLClass S) := ⟨mk default⟩

end GreenLClass

/-- The quotient type of `S` by Green's R relation. -/
abbrev GreenRClass (S : Type*) [Semigroup S] := Quotient (IsGreenR.setoid S)

namespace GreenRClass

/-- Constructs the Green's R-class of an element `x`. -/
abbrev mk (x : S) : GreenRClass S := Quotient.mk (IsGreenR.setoid S) x

/-- The projection map to Green's R-classes is surjective. -/
lemma mk_surjective : Function.Surjective (mk : S → GreenRClass S) :=
  @Quotient.exists_rep _ (IsGreenR.setoid S)

/-- Two elements have the same Green's R-class if and only if they are R-related. -/
lemma mk_eq_mk_iff {a b : S} : mk a = mk b ↔ IsGreenR a b :=
  @Quotient.eq _ (IsGreenR.setoid S) _ _

instance [Inhabited S] : Inhabited (GreenRClass S) := ⟨mk default⟩

end GreenRClass

/-- The quotient type of `S` by Green's J relation. -/
abbrev GreenJClass (S : Type*) [Semigroup S] := Quotient (IsGreenJ.setoid S)

namespace GreenJClass

/-- Constructs the Green's J-class of an element `x`. -/
abbrev mk (x : S) : GreenJClass S := Quotient.mk (IsGreenJ.setoid S) x

/-- The projection map to Green's J-classes is surjective. -/
lemma mk_surjective : Function.Surjective (mk : S → GreenJClass S) :=
  @Quotient.exists_rep _ (IsGreenJ.setoid S)

/-- Two elements have the same Green's J-class if and only if they are J-related. -/
lemma mk_eq_mk_iff {a b : S} : mk a = mk b ↔ IsGreenJ a b :=
  @Quotient.eq _ (IsGreenJ.setoid S) _ _

instance [Inhabited S] : Inhabited (GreenJClass S) := ⟨mk default⟩

end GreenJClass

/-- The quotient type of `S` by Green's H relation. -/
abbrev GreenHClass (S : Type*) [Semigroup S] := Quotient (IsGreenH.setoid S)

namespace GreenHClass

/-- Constructs the Green's H-class of an element `x`. -/
abbrev mk (x : S) : GreenHClass S := Quotient.mk (IsGreenH.setoid S) x

/-- The projection map to Green's H-classes is surjective. -/
lemma mk_surjective : Function.Surjective (mk : S → GreenHClass S) :=
  @Quotient.exists_rep _ (IsGreenH.setoid S)

/-- Two elements have the same Green's H-class if and only if they are H-related. -/
lemma mk_eq_mk_iff {a b : S} : mk a = mk b ↔ IsGreenH a b :=
  @Quotient.eq _ (IsGreenH.setoid S) _ _

instance [Inhabited S] : Inhabited (GreenHClass S) := ⟨mk default⟩

end GreenHClass

/-- The quotient type of `S` by Green's D relation. -/
abbrev GreenDClass (S : Type*) [Semigroup S] := Quotient (IsGreenD.setoid S)

namespace GreenDClass

/-- Constructs the Green's D-class of an element `x`. -/
abbrev mk (x : S) : GreenDClass S := Quotient.mk (IsGreenD.setoid S) x

/-- The projection map to Green's D-classes is surjective. -/
lemma mk_surjective : Function.Surjective (mk : S → GreenDClass S) :=
  @Quotient.exists_rep _ (IsGreenD.setoid S)

/-- Two elements have the same Green's D-class if and only if they are D-related. -/
lemma mk_eq_mk_iff {a b : S} : mk a = mk b ↔ IsGreenD a b :=
  @Quotient.eq _ (IsGreenD.setoid S) _ _

instance [Inhabited S] : Inhabited (GreenDClass S) := ⟨mk default⟩

end GreenDClass

end QuotientAPI
