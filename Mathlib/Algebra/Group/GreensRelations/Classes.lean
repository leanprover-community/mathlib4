/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.Finite.Defs

/-!
# Green's Equivalence Classes and Posets

This file defines the equivalence classes corresponding to Green's relations.
It establishes the Quotient API and proves that the relations L, R, and J
naturally induce a Partial Order (Poset) on their respective quotient spaces.
It also introduces the concepts of regular elements and regular D-classes.

## Main definitions

* `IsGreenL.eqvClass` (and similar for R, H, D, J): The equivalence class as a `Set S`.
* `GreenLClass S` (and similar for R, H, D, J): The quotient type of `S` by Green's L relation.
* `IsGreenRegular`: A predicate indicating that an element `a` is regular (`a * s * a = a`).
* `IsRegularDClass`: A predicate indicating that all elements in a D-class are regular.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

public section

variable {S : Type*} [Semigroup S]

section SetsAndRegularity

namespace IsGreenL

/-- The equivalence class of `x` under Green's L relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := setOf (IsGreenL · x)

end IsGreenL

namespace IsGreenR

/-- The equivalence class of `x` under Green's R relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := setOf (IsGreenR · x)

end IsGreenR

namespace IsGreenH

/-- The equivalence class of `x` under Green's H relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := setOf (IsGreenH · x)

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
abbrev eqvClass (x : S) : Set S := setOf (IsGreenD · x)

end IsGreenD

namespace IsGreenJ

/-- The equivalence class of `x` under Green's J relation as a `Set S`. -/
abbrev eqvClass (x : S) : Set S := setOf (IsGreenJ · x)

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

/-- `IsGreenLeftDvd` is well-defined with respect to Green's L relation. -/
lemma isGreenLeftDvd_respects (a₁ b₁ a₂ b₂ : S)
    (h1 : IsGreenL a₁ a₂) (h2 : IsGreenL b₁ b₂) :
    IsGreenLeftDvd a₁ b₁ = IsGreenLeftDvd a₂ b₂ :=
  propext ⟨
    fun h ↦ h1.right.trans (h.trans h2.left),
    fun h ↦ h1.left.trans (h.trans h2.right)
  ⟩

/-- Green's L relation induces a natural left-multiplication order on L-classes.
`[a] ≤ [b]` iff `a` is a left multiple of `b`. -/
instance : LE (GreenLClass S) where
  le := Quotient.lift₂ IsGreenLeftDvd isGreenLeftDvd_respects

/-- The partial order on L-classes. -/
instance : PartialOrder (GreenLClass S) where
  le_refl := by
    rintro ⟨a⟩
    dsimp [LE.le]
    exact IsGreenLeftDvd.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    dsimp [LE.le] at hab hbc ⊢
    exact hab.trans hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    dsimp [LE.le] at hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

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

/-- `IsGreenRightDvd` is well-defined with respect to Green's R relation. -/
lemma isGreenRightDvd_respects (a₁ b₁ a₂ b₂ : S)
    (ha : IsGreenR a₁ a₂) (hb : IsGreenR b₁ b₂) :
    IsGreenRightDvd a₁ b₁ = IsGreenRightDvd a₂ b₂ :=
  propext ⟨
    fun h ↦ IsGreenRightDvd.trans (IsGreenRightDvd.trans ha.right h) hb.left,
    fun h ↦ IsGreenRightDvd.trans (IsGreenRightDvd.trans ha.left h) hb.right
  ⟩

/-- Green's R relation induces a natural right-multiplication order on R-classes.
`[a] ≤ [b]` iff `a` is a right multiple of `b`. -/
instance : LE (GreenRClass S) where
  le := Quotient.lift₂ IsGreenRightDvd isGreenRightDvd_respects

/-- The partial order on R-classes. -/
instance : PartialOrder (GreenRClass S) where
  le_refl := by
    rintro ⟨a⟩
    dsimp [LE.le]
    exact IsGreenRightDvd.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    dsimp [LE.le] at hab hbc ⊢
    exact IsGreenRightDvd.trans hab hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    dsimp [LE.le] at hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

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

/-- `IsGreenJRel` is well-defined with respect to Green's J relation. -/
lemma isGreenJRel_respects (a₁ b₁ a₂ b₂ : S)
    (ha : IsGreenJ a₁ a₂) (hb : IsGreenJ b₁ b₂) :
    IsGreenJRel a₁ b₁ = IsGreenJRel a₂ b₂ :=
  propext ⟨
    fun h ↦ IsGreenJRel.trans (IsGreenJRel.trans ha.right h) hb.left,
    fun h ↦ IsGreenJRel.trans (IsGreenJRel.trans ha.left h) hb.right
  ⟩

/-- Green's J relation induces a natural two-sided order on J-classes.
`[a] ≤ [b]` iff `a` is a two-sided multiple of `b`. -/
instance : LE (GreenJClass S) where
  le := Quotient.lift₂ IsGreenJRel isGreenJRel_respects

/-- The partial order on J-classes. -/
instance : PartialOrder (GreenJClass S) where
  le_refl := by
    rintro ⟨a⟩
    dsimp [LE.le]
    exact IsGreenJRel.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    dsimp [LE.le] at hab hbc ⊢
    exact IsGreenJRel.trans hab hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    dsimp [LE.le] at hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

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
