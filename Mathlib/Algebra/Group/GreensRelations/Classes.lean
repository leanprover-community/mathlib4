/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finite.Defs

/-!
# Green's Equivalence Classes and Quotient API

This file defines the equivalence classes corresponding to Green's relations
as sets (`Set S`) and introduces their quotient types (`GreenLClass`, etc.).
It also introduces the concepts of regular elements and regular D-classes.

## Main definitions

* `IsGreenL.eqvClass` (and similar for R, H, D, J): The equivalence class as a `Set S`.
* `GreenLClass S` (and similar for R, H, D, J): The quotient type of `S` by Green's relations.
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

/-- The H-class of `x` is the intersection of its L-class and R-class. -/
lemma eqvClass_eq_inter (x : S) :
    eqvClass x = IsGreenL.eqvClass x ∩ IsGreenR.eqvClass x := by
  ext y
  simp [IsGreenH, eqvClass, IsGreenL.eqvClass, IsGreenR.eqvClass]

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
