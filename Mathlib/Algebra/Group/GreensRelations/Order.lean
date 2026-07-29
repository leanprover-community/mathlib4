/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/
module

public import Mathlib.Algebra.Group.GreensRelations.Theorems

/-!
# Green's Relations Partial Orders

This file defines the natural partial order structures (`LE` and `PartialOrder`)
on the quotient types `GreenLClass`, `GreenRClass`, `GreenJClass`, and `GreenDClass`.

## Main definitions
* `GreenLClass.instPartialOrder`: Partial order on L-classes.
* `GreenRClass.instPartialOrder`: Partial order on R-classes.
* `GreenJClass.instPartialOrder`: Partial order on J-classes.
* `GreenDClass.instPartialOrder`: Partial order on D-classes in a finite semigroup, via `D = J`.

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

public section

variable {S : Type*} [Semigroup S]

namespace GreenLClass

/-- `IsGreenLeftDvd` is well-defined with respect to Green's L relation. -/
lemma isGreenLeftDvd_respects (a₁ b₁ a₂ b₂ : S)
    (ha : IsGreenL a₁ a₂) (hb : IsGreenL b₁ b₂) :
    IsGreenLeftDvd a₁ b₁ = IsGreenLeftDvd a₂ b₂ :=
  propext ⟨fun h => ha.right.trans (h.trans hb.left),
          fun h => ha.left.trans (h.trans hb.right)⟩

/-- Green's L relation induces a natural left-multiplication order on L-classes.
`[a] ≤ [b]` iff `a` is a left multiple of `b`. -/
instance : LE (GreenLClass S) where
  le := Quotient.lift₂ IsGreenLeftDvd isGreenLeftDvd_respects

/-- The partial order on L-classes. -/
instance : PartialOrder (GreenLClass S) where
  le_refl := by
    rintro ⟨a⟩
    exact IsGreenLeftDvd.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    exact IsGreenLeftDvd.trans hab hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenLClass


namespace GreenRClass

/-- `IsGreenRightDvd` is well-defined with respect to Green's R relation. -/
lemma isGreenRightDvd_respects (a₁ b₁ a₂ b₂ : S)
    (ha : IsGreenR a₁ a₂) (hb : IsGreenR b₁ b₂) :
    IsGreenRightDvd a₁ b₁ = IsGreenRightDvd a₂ b₂ :=
  propext ⟨fun h => ha.right.trans (h.trans hb.left),
          fun h => ha.left.trans (h.trans hb.right)⟩

/-- Green's R relation induces a natural right-multiplication order on R-classes.
`[a] ≤ [b]` iff `a` is a right multiple of `b`. -/
instance : LE (GreenRClass S) where
  le := Quotient.lift₂ IsGreenRightDvd isGreenRightDvd_respects

/-- The partial order on R-classes. -/
instance : PartialOrder (GreenRClass S) where
  le_refl := by
    rintro ⟨a⟩
    exact IsGreenRightDvd.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    exact IsGreenRightDvd.trans hab hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenRClass


namespace GreenJClass

/-- `IsGreenJRel` is well-defined with respect to Green's J relation. -/
lemma isGreenJRel_respects (a₁ b₁ a₂ b₂ : S)
    (ha : IsGreenJ a₁ a₂) (hb : IsGreenJ b₁ b₂) :
    IsGreenJRel a₁ b₁ = IsGreenJRel a₂ b₂ :=
  propext ⟨fun h => ha.right.trans (h.trans hb.left),
          fun h => ha.left.trans (h.trans hb.right)⟩

/-- Green's J relation induces a natural two-sided order on J-classes.
`[a] ≤ [b]` iff `a` is a two-sided multiple of `b`. -/
instance : LE (GreenJClass S) where
  le := Quotient.lift₂ IsGreenJRel isGreenJRel_respects

/-- The partial order on J-classes. -/
instance : PartialOrder (GreenJClass S) where
  le_refl := by
    rintro ⟨a⟩
    exact IsGreenJRel.refl a
  le_trans := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc
    exact IsGreenJRel.trans hab hbc
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ hab hba
    exact mk_eq_mk_iff.mpr ⟨hab, hba⟩

end GreenJClass


namespace GreenDClass

/-- In a finite semigroup, equivalence of D and J relations yields an equivalence
between `GreenDClass S` and `GreenJClass S`. -/
noncomputable def equivGreenJClass [Finite S] : GreenDClass S ≃ GreenJClass S where
  toFun := Quotient.map id (fun _ _ h => isGreenJ_of_isGreenD h)
  invFun := Quotient.map id (fun _ _ h => isGreenD_of_isGreenJ h)
  left_inv := by
    rintro ⟨a⟩
    rfl
  right_inv := by
    rintro ⟨a⟩
    rfl

/-- Green's D relation induces an order on D-classes in a finite semigroup via `D = J`. -/
noncomputable instance [Finite S] : LE (GreenDClass S) where
  le x y := equivGreenJClass x ≤ equivGreenJClass y

/-- The partial order on D-classes in a finite semigroup. -/
noncomputable instance [Finite S] : PartialOrder (GreenDClass S) where
  le_refl x := le_refl (equivGreenJClass x)
  le_trans x y z hxy hyz := le_trans (α := GreenJClass S) hxy hyz
  le_antisymm x y hxy hyx := equivGreenJClass.injective (le_antisymm (α := GreenJClass S) hxy hyx)

end GreenDClass
