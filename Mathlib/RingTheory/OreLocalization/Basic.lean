/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Group.Submonoid.DistribMulAction
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!

# Localization over left Ore sets.

This file proves results on the localization of rings (monoids with zeros) over a left Ore set.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/

@[expose] public section

assert_not_exists RelIso

universe u

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

@[simp]
theorem zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp [Submonoid.smul_def]⟩

instance : MonoidWithZero R[S⁻¹] where
  zero_mul x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def, oreDiv_mul_char 0 r 1 s 0 1 (by simp), zero_mul, one_mul]
  mul_zero x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def, mul_div_one, mul_zero, zero_oreDiv', zero_oreDiv']

theorem subsingleton_iff :
    Subsingleton R[S⁻¹] ↔ 0 ∈ S := by
  rw [← subsingleton_iff_zero_eq_one, OreLocalization.one_def,
    OreLocalization.zero_def, oreDiv_eq_iff]
  simp

theorem nontrivial_iff :
    Nontrivial R[S⁻¹] ↔ 0 ∉ S := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {S : Submonoid R} [OreSet S]

instance : CommMonoidWithZero R[S⁻¹] where
  __ := (inferInstance : MonoidWithZero R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommMonoidWithZero

section DistribMulAction

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S] {X : Type*} [AddMonoid X]
variable [DistribMulAction R X]

/-- Auxiliary definition for addition on the Ore localization. -/
private def add'' (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
  (oreDenom (s₁ : R) s₂ • r₁ + oreNum (s₁ : R) s₂ • r₂) /ₒ (oreDenom (s₁ : R) s₂ * s₁)

private theorem add''_char (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
    (hb : sb * s₁ = rb * s₂) (h : sb * s₁ ∈ S) :
    add'' r₁ s₁ r₂ s₂ = (sb • r₁ + rb • r₂) /ₒ ⟨sb * s₁, h⟩ := by
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  generalize oreNum (s₁ : R) s₂ = ra at *
  generalize oreDenom (s₁ : R) s₂ = sa at *
  rw [oreDiv_eq_iff]
  rcases oreCondition sb sa with ⟨rc, sc, hc⟩
  have : sc * rb * s₂ = rc * ra * s₂ := by
    rw [mul_assoc rc, ← ha, ← mul_assoc, ← hc, mul_assoc, mul_assoc, hb]
  rcases ore_right_cancel _ _ s₂ this with ⟨sd, hd⟩
  use sd * sc
  use sd * rc
  simp only [smul_add, smul_smul, Submonoid.smul_def, Submonoid.coe_mul]
  constructor
  · rw [mul_assoc _ _ rb, hd, mul_assoc, hc, mul_assoc, mul_assoc]
  · rw [mul_assoc, ← mul_assoc (sc : R), hc, mul_assoc, mul_assoc]

attribute [local instance] OreLocalization.oreEqv

/-- Auxiliary definition for addition on the Ore localization, with one argument fixed. -/
private def add' (r₂ : X) (s₂ : S) : X[S⁻¹] → X[S⁻¹] :=
  (--plus tilde
      Quotient.lift
      fun r₁s₁ : X × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    rcases oreCondition rb sc with ⟨rd, sd, hd⟩
    -- s#, r#
    dsimp at *
    rw [add''_char _ _ _ _ rc sc hc (sc * s₁').2]
    have : sd * sb * s₁ = rd * rc * s₂ := by
      rw [mul_assoc, hb', ← mul_assoc, hd, mul_assoc, hc, ← mul_assoc]
    rw [add''_char _ _ _ _ (rd * rc : R) (sd * sb) this (sd * sb * s₁).2]
    rw [mul_smul, ← Submonoid.smul_def sb, hb, smul_smul, hd, oreDiv_eq_iff]
    use 1
    use rd
    simp only [mul_smul, smul_add, one_smul, OneMemClass.coe_one, one_mul, true_and]
    rw [this, hc, mul_assoc]

/-- The addition on the Ore localization. -/
@[irreducible]
private def add : X[S⁻¹] → X[S⁻¹] → X[S⁻¹] := fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction x with | _ r₃ s₃
      change add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition rc sb with ⟨rd, sd, hd⟩
      have : rd * rb * s₁ = sd * sc * s₃ := by
        rw [mul_assoc, ← hb', ← mul_assoc, ← hd, mul_assoc, ← hc, mul_assoc]
      rw [add''_char _ _ _ _ rc sc hc (sc * s₃).2]
      rw [add''_char _ _ _ _ _ _ this.symm (sd * sc * s₃).2]
      refine oreDiv_eq_iff.mpr ?_
      simp only [smul_add]
      use sd, 1
      simp only [one_smul, one_mul, mul_smul, ← hb, Submonoid.smul_def, ← mul_assoc, and_true]
      simp only [smul_smul, hd])

@[no_expose]
instance : Add X[S⁻¹] :=
  ⟨add⟩

theorem oreDiv_add_oreDiv {r r' : X} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (oreDenom (s : R) s' * s) := by
  with_unfolding_all rfl

theorem oreDiv_add_char' {r r' : X} (s s' : S) (rb : R) (sb : R)
    (h : sb * s = rb * s') (h' : sb * s ∈ S) :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ ⟨sb * s, h'⟩ := by
  with_unfolding_all exact add''_char r s r' s' rb sb h h'

/-- A characterization of the addition on the Ore localization, allowing for arbitrary Ore
numerator and Ore denominator. -/
theorem oreDiv_add_char {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s') :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ (sb * s) :=
  oreDiv_add_char' s s' rb sb h (sb * s).2

/-- Another characterization of the addition on the Ore localization, bundling up all witnesses
and conditions into a sigma type. -/
def oreDivAddChar' (r r' : X) (s s' : S) :
    Σ' r'' : R,
      Σ' s'' : S, s'' * s = r'' * s' ∧ r /ₒ s + r' /ₒ s' = (s'' • r + r'' • r') /ₒ (s'' * s) :=
  ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩

@[simp]
theorem add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s := by
  simp [oreDiv_add_char s s 1 1 (by simp)]

protected theorem add_assoc (x y z : X[S⁻¹]) : x + y + z = x + (y + z) := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, add_assoc]
  simp_rw [← add_oreDiv, ← OreLocalization.expand']
  congr 2
  · rw [OreLocalization.expand r₂ s₂ ra (ha.symm ▸ (sa * s₁).2)]; congr; ext; exact ha
  · rw [OreLocalization.expand r₃ s₃ rc (hc.symm ▸ (sc * (sa * s₁)).2)]; congr; ext; exact hc

@[simp]
theorem zero_oreDiv (s : S) : (0 : X) /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩

protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
  induction x
  rw [← zero_oreDiv, add_oreDiv]; simp

protected theorem add_zero (x : X[S⁻¹]) : x + 0 = x := by
  induction x
  rw [← zero_oreDiv, add_oreDiv]; simp

/-- Scalar multiplication by natural numbers on the Ore localization. -/
@[irreducible]
def nsmul : ℕ → X[S⁻¹] → X[S⁻¹] := nsmulRec

instance : AddMonoid X[S⁻¹] where
    add_assoc := OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmul
    nsmul_zero _ := by with_unfolding_all rfl
    nsmul_succ _ _ := by with_unfolding_all rfl

protected theorem smul_zero (x : R[S⁻¹]) : x • (0 : X[S⁻¹]) = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def, smul_div_one, smul_zero, zero_oreDiv, zero_oreDiv]

protected theorem smul_add (z : R[S⁻¹]) (x y : X[S⁻¹]) :
    z • (x + y) = z • x + z • y := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  rw [← Subtype.coe_eq_of_eq_mk ha]
  repeat rw [oreDiv_smul_oreDiv]
  simp only [smul_add, add_oreDiv]

instance : DistribMulAction R[S⁻¹] X[S⁻¹] where
  smul_zero := OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add

instance {R₀} [Monoid R₀] [MulAction R₀ X] [MulAction R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    DistribMulAction R₀ X[S⁻¹] where
  smul_zero _ := by rw [← smul_one_oreDiv_one_smul, smul_zero]
  smul_add _ _ _ := by simp only [← smul_one_oreDiv_one_smul, smul_add]

end DistribMulAction

section AddCommMonoid

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [DistribMulAction R X]

protected theorem add_comm (x y : X[S⁻¹]) : x + y = y + x := by
  induction x with | _ r s
  induction y with | _ r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha', oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2), add_comm]
  congr; ext; exact ha

instance instAddCommMonoidOreLocalization : AddCommMonoid X[S⁻¹] where
  add_comm := OreLocalization.add_comm

end AddCommMonoid

section AddGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddGroup X] [DistribMulAction R X]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
@[irreducible]
protected def neg : X[S⁻¹] → X[S⁻¹] :=
  liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/12129): additional beta reduction needed
    beta_reduce
    rw [← smul_neg, ← OreLocalization.expand]

instance instNegOreLocalization : Neg X[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
protected theorem neg_def (r : X) (s : S) : -(r /ₒ s) = -r /ₒ s := by
  with_unfolding_all rfl

protected theorem neg_add_cancel (x : X[S⁻¹]) : -x + x = 0 := by
  induction x with | _ r s; simp

/-- `zsmul` of `OreLocalization` -/
@[irreducible]
protected def zsmul : ℤ → X[S⁻¹] → X[S⁻¹] := zsmulRec

unseal OreLocalization.zsmul in
instance instAddGroupOreLocalization : AddGroup X[S⁻¹] where
  neg_add_cancel := OreLocalization.neg_add_cancel
  zsmul := OreLocalization.zsmul

end AddGroup

section AddCommGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [DistribMulAction R X]

instance : AddCommGroup X[S⁻¹] where
  __ := (inferInstance : AddGroup X[S⁻¹])
  __ := (inferInstance : AddCommMonoid X[S⁻¹])

end AddCommGroup

end OreLocalization
