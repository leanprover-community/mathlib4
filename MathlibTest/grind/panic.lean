import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic.FastInstance

/-!
From `v4.23.0-rc2` through to `nightly-2025-09-02`, `grind` panicked here.

We keep this example as a regression test in Mathlib.
-/

set_option warn.sorry false

variable {R : Type} [CommRing R]

class DivisionRing (K : Type) extends Ring K, DivInvMonoid K, Nontrivial K where
  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
  protected inv_zero : (0 : K)⁻¹ = 0

class Field (K : Type) extends CommRing K, DivisionRing K

instance {K : Type} [Field K] : Lean.Grind.Field K :=
  { CommRing.toGrindCommRing K, ‹Field K› with
    zpow := ⟨fun a n => a^n⟩
    zpow_zero a := sorry
    zpow_succ a n := sorry
    zpow_neg a n := sorry
    zero_ne_one := sorry }

instance {K : Type} [Field K] : IsDomain K := sorry
instance [IsDomain R] : CancelCommMonoidWithZero R := sorry
noncomputable def normalizedFactors {α : Type} [CancelCommMonoidWithZero α] (a : α) : Set α := sorry

structure Ideal (R : Type) [CommRing R] where
structure Ideal.Quotient (I : Ideal R) where
class Ideal.IsMaximal (I : Ideal R) : Prop where

namespace Ideal.Quotient

variable (I J : Ideal R)

instance commRing {R} [CommRing R] (I : Ideal R) : CommRing I.Quotient := sorry

protected noncomputable abbrev groupWithZero [hI : I.IsMaximal] :
    GroupWithZero (I.Quotient) :=
  { inv := sorry
    mul_inv_cancel := sorry
    inv_zero := sorry
    exists_pair_ne := sorry }

protected noncomputable abbrev divisionRing [I.IsMaximal] : DivisionRing (I.Quotient) :=
  fast_instance% -- The panic seems to rely on this specific `fast_instance%`.
  { __ := commRing _
    __ := Quotient.groupWithZero _ }

protected noncomputable abbrev field {R} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Field (I.Quotient) :=
  { __ := commRing _
    __ := Quotient.divisionRing I }

end Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

open Classical in
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span.extracted_1_3
  {R : Type} [CommRing R] {I : Ideal R} [I.IsMaximal] {mapQ mapMinpoly : I.Quotient}
  (_ : mapQ ∈ normalizedFactors mapMinpoly) :
  0 = 0 := by grind
