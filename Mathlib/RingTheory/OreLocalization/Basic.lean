/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.Algebra.Group.Submonoid.Operations

#align_import ring_theory.ore_localization.basic from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!

# Localization over left Ore sets.

This file defines the localization of a monoid over a left Ore set and proves its universal
mapping property.

## Notations

Introduces the notation `R[S⁻¹]` for the Ore localization of a monoid `R` at a right Ore
subset `S`. Also defines a new heterogeneous division notation `r /ₒ s` for a numerator `r : R` and
a denominator `s : S`.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/


universe u

open OreLocalization

namespace OreLocalization

variable {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S] (X) [MulAction R X]

/-- The setoid on `R × S` used for the Ore localization. -/
@[to_additive AddOreLocalization.oreEqv "The setoid on `R × S` used for the Ore localization."]
def oreEqv : Setoid (X × S) where
  r rs rs' := ∃ (u : S) (v : R), u • rs'.1 = v • rs.1 ∧ u * rs'.2 = v * rs.2
  iseqv := by
    refine ⟨fun _ => ⟨1, 1, by simp⟩, ?_, ?_⟩
    · rintro ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩; dsimp only at *
      rcases oreCondition (s : R) s' with ⟨r₂, s₂, h₁⟩
      rcases oreCondition r₂ u with ⟨r₃, s₃, h₂⟩
      have : r₃ * v * s = s₃ * s₂ * s := by
        -- Porting note: the proof used `assoc_rw`
        rw [mul_assoc _ (s₂ : R), h₁, ← mul_assoc, h₂, mul_assoc, ← hsu, ← mul_assoc]
      rcases ore_right_cancel (r₃ * v) (s₃ * s₂) s this with ⟨w, hw⟩
      refine ⟨w * (s₃ * s₂), w * (r₃ * u), ?_, ?_⟩ <;>
        simp only [Submonoid.coe_mul, Submonoid.smul_def, ← hw]
      · simp only [mul_smul, hru, ← Submonoid.smul_def]
      · simp only [mul_assoc, hsu]
    · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩
      rcases oreCondition v' u with ⟨r', s', h⟩; dsimp only at *
      refine ⟨s' * u', r' * v, ?_, ?_⟩ <;>
        simp only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul, mul_assoc] at *
      · rw [hur₂, smul_smul, h, mul_smul, hur₁]
      · rw [hs₂u, ← mul_assoc, h, mul_assoc, hs₁u]
#align ore_localization.ore_eqv OreLocalization.oreEqv

end OreLocalization

/-- The Ore localization of a monoid and a submonoid fulfilling the Ore condition. -/
@[to_additive AddOreLocalization "The Ore localization of an additive monoid and a submonoid
fulfilling the Ore condition."]
def OreLocalization {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S]
    (X : Type*) [MulAction R X] :=
  Quotient (OreLocalization.oreEqv S X)
#align ore_localization OreLocalization

namespace OreLocalization

section Monoid

variable {R : Type*} [Monoid R] {S : Submonoid R}
variable (R S) [OreSet S]

@[inherit_doc OreLocalization]
scoped syntax:1075 term noWs atomic("[" term "⁻¹" noWs "]") : term
macro_rules | `($R[$S⁻¹]) => ``(OreLocalization $S $R)

attribute [local instance] oreEqv

variable {R S}
variable {X} [MulAction R X]

/-- The division in the Ore localization `X[S⁻¹]`, as a fraction of an element of `X` and `S`. -/
@[to_additive "The subtraction in the Ore localization,
as a difference of an element of `X` and `S`."]
def oreDiv (r : X) (s : S) : X[S⁻¹] :=
  Quotient.mk' (r, s)
#align ore_localization.ore_div OreLocalization.oreDiv

@[inherit_doc]
infixl:70 " /ₒ " => oreDiv

@[inherit_doc]
infixl:65 " -ₒ " => _root_.AddOreLocalization.oreSub

@[to_additive (attr := elab_as_elim)]
protected theorem ind {β : X[S⁻¹] → Prop}
    (c : ∀ (r : X) (s : S), β (r /ₒ s)) : ∀ q, β q := by
  apply Quotient.ind
  rintro ⟨r, s⟩
  exact c r s
#align ore_localization.ind OreLocalization.ind

@[to_additive]
theorem oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} :
    r₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ ∃ (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁ :=
  Quotient.eq''
#align ore_localization.ore_div_eq_iff OreLocalization.oreDiv_eq_iff

/-- A fraction `r /ₒ s` is equal to its expansion by an arbitrary factor `t` if `t * s ∈ S`. -/
@[to_additive "A difference `r -ₒ s` is equal to its expansion by an
arbitrary translation `t` if `t + s ∈ S`."]
protected theorem expand (r : X) (s : S) (t : R) (hst : t * (s : R) ∈ S) :
    r /ₒ s = t • r /ₒ ⟨t * s, hst⟩ := by
  apply Quotient.sound
  exact ⟨s, s * t, by rw [mul_smul, Submonoid.smul_def], by rw [← mul_assoc]⟩
#align ore_localization.expand OreLocalization.expand

/-- A fraction is equal to its expansion by a factor from `S`. -/
@[to_additive "A difference is equal to its expansion by a summand from `S`."]
protected theorem expand' (r : X) (s s' : S) : r /ₒ s = s' • r /ₒ (s' * s) :=
  OreLocalization.expand r s s' (by norm_cast; apply SetLike.coe_mem)
#align ore_localization.expand' OreLocalization.expand'

/-- Fractions which differ by a factor of the numerator can be proven equal if
those factors expand to equal elements of `R`. -/
@[to_additive "Differences whose minuends differ by a common summand can be proven equal if
those summands expand to equal elements of `R`."]
protected theorem eq_of_num_factor_eq {r r' r₁ r₂ : R} {s t : S} (h : t * r = t * r') :
    r₁ * r * r₂ /ₒ s = r₁ * r' * r₂ /ₒ s := by
  rcases oreCondition r₁ t with ⟨r₁', t', hr₁⟩
  rw [OreLocalization.expand' _ s t', OreLocalization.expand' _ s t']
  congr 1
  -- Porting note (#11215): TODO: use `assoc_rw`?
  calc (t' : R) * (r₁ * r * r₂)
      = t' * r₁ * r * r₂ := by simp [← mul_assoc]
    _ = r₁' * t * r * r₂ := by rw [hr₁]
    _ = r₁' * (t * r) * r₂ := by simp [← mul_assoc]
    _ = r₁' * (t * r') * r₂ := by rw [h]
    _ = r₁' * t * r' * r₂ := by simp [← mul_assoc]
    _ = t' * r₁ * r' * r₂ := by rw [hr₁]
    _ = t' * (r₁ * r' * r₂) := by simp [← mul_assoc]
#align ore_localization.eq_of_num_factor_eq OreLocalization.eq_of_num_factor_eq

/-- A function or predicate over `X` and `S` can be lifted to `X[S⁻¹]` if it is invariant
under expansion on the left. -/
@[to_additive "A function or predicate over `X` and `S` can be lifted to the localizaton if it is
invariant under expansion on the left."]
def liftExpand {C : Sort*} (P : X → S → C)
    (hP : ∀ (r : X) (t : R) (s : S) (ht : t * s ∈ S), P r s = P (t • r) ⟨t * s, ht⟩) :
    X[S⁻¹] → C :=
  Quotient.lift (fun p : X × S => P p.1 p.2) fun (r₁, s₁) (r₂, s₂) ⟨u, v, hr₂, hs₂⟩ => by
    dsimp at *
    have s₁vS : v * s₁ ∈ S := by
      rw [← hs₂, ← S.coe_mul]
      exact SetLike.coe_mem (u * s₂)
    replace hs₂ : u * s₂ = ⟨_, s₁vS⟩ := by ext; simp [hs₂]
    rw [hP r₁ v s₁ s₁vS, hP r₂ u s₂ (by norm_cast; rwa [hs₂]), ← hr₂]
    simp only [← hs₂]; rfl
#align ore_localization.lift_expand OreLocalization.liftExpand

@[to_additive (attr := simp)]
theorem liftExpand_of {C : Sort*} {P : X → S → C}
    {hP : ∀ (r : X) (t : R) (s : S) (ht : t * s ∈ S), P r s = P (t • r) ⟨t * s, ht⟩} (r : X)
    (s : S) : liftExpand P hP (r /ₒ s) = P r s :=
  rfl
#align ore_localization.lift_expand_of OreLocalization.liftExpand_of

/-- A version of `liftExpand` used to simultaneously lift functions with two arguments
in `X[S⁻¹]`. -/
@[to_additive "A version of `liftExpand` used to simultaneously lift functions with two arguments"]
def lift₂Expand {C : Sort*} (P : X → S → X → S → C)
    (hP :
      ∀ (r₁ : X) (t₁ : R) (s₁ : S) (ht₁ : t₁ * s₁ ∈ S) (r₂ : X) (t₂ : R) (s₂ : S)
        (ht₂ : t₂ * s₂ ∈ S),
        P r₁ s₁ r₂ s₂ = P (t₁ • r₁) ⟨t₁ * s₁, ht₁⟩ (t₂ • r₂) ⟨t₂ * s₂, ht₂⟩) :
    X[S⁻¹] → X[S⁻¹] → C :=
  liftExpand
    (fun r₁ s₁ => liftExpand (P r₁ s₁) fun r₂ t₂ s₂ ht₂ => by
      have := hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂
      simp [this])
    fun r₁ t₁ s₁ ht₁ => by
    ext x; induction' x using OreLocalization.ind with r₂ s₂
    dsimp only
    rw [liftExpand_of, liftExpand_of, hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)]; simp
#align ore_localization.lift₂_expand OreLocalization.lift₂Expand

@[to_additive (attr := simp)]
theorem lift₂Expand_of {C : Sort*} {P : X → S → X → S → C}
    {hP :
      ∀ (r₁ : X) (t₁ : R) (s₁ : S) (ht₁ : t₁ * s₁ ∈ S) (r₂ : X) (t₂ : R) (s₂ : S)
        (ht₂ : t₂ * s₂ ∈ S),
        P r₁ s₁ r₂ s₂ = P (t₁ • r₁) ⟨t₁ * s₁, ht₁⟩ (t₂ • r₂) ⟨t₂ * s₂, ht₂⟩}
    (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : lift₂Expand P hP (r₁ /ₒ s₁) (r₂ /ₒ s₂) = P r₁ s₁ r₂ s₂ :=
  rfl
#align ore_localization.lift₂_expand_of OreLocalization.lift₂Expand_of

@[to_additive]
private def smul' (r₁ : R) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
  oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁)

@[to_additive]
private theorem smul'_char (r₁ : R) (r₂ : X) (s₁ s₂ : S) (u : S) (v : R) (huv : u * r₁ = v * s₂) :
    OreLocalization.smul' r₁ s₁ r₂ s₂ = v • r₂ /ₒ (u * s₁) := by
  -- Porting note: `assoc_rw` was not ported yet
  simp only [smul']
  have h₀ := ore_eq r₁ s₂; set v₀ := oreNum r₁ s₂; set u₀ := oreDenom r₁ s₂
  rcases oreCondition (u₀ : R) u with ⟨r₃, s₃, h₃⟩
  have :=
    calc
      r₃ * v * s₂ = r₃ * (u * r₁) := by rw [mul_assoc, ← huv]
      _ = s₃ * (u₀ * r₁) := by rw [← mul_assoc, ← mul_assoc, h₃]
      _ = s₃ * v₀ * s₂ := by rw [mul_assoc, h₀]
  rcases ore_right_cancel _ _ _ this with ⟨s₄, hs₄⟩
  symm; rw [oreDiv_eq_iff]
  use s₄ * s₃
  use s₄ * r₃
  simp only [Submonoid.coe_mul, Submonoid.smul_def, smul_eq_mul]
  constructor
  · rw [smul_smul, mul_assoc (c := v₀), ← hs₄]
    simp only [smul_smul, mul_assoc]
  · rw [← mul_assoc (b := (u₀ : R)), mul_assoc (c := (u₀ : R)), h₃]
    simp only [mul_assoc]

/-- The multiplication on the Ore localization of monoids. -/
@[to_additive]
private def smul'' (r : R) (s : S) : X[S⁻¹] → X[S⁻¹] :=
  liftExpand (smul' r s) fun r₁ r₂ s' hs => by
    rcases oreCondition r s' with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition r ⟨_, hs⟩ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₁' : R) (s₂') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₁' * s' = (r₃' * r₂' * r₂) * s' := by
      rw [mul_assoc, ← h₁, ← mul_assoc, h₃, mul_assoc, h₂]
      simp [mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₂' * s) ∈ S := by
      rw [mul_assoc, ← mul_assoc r₃', ← h₃]
      exact (s₄' * (s₃' * s₁' * s)).2
    rw [OreLocalization.expand' _ _ (s₄' * s₃'), OreLocalization.expand _ (s₂' * s) _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc (s₄' : R), h₃, ← mul_assoc]

/-- The scalar multiplication on the Ore localization of monoids. -/
@[to_additive "the vector addition on the Ore localization of additive monoids."]
protected def smul : R[S⁻¹] → X[S⁻¹] → X[S⁻¹] :=
  liftExpand smul'' fun r₁ r₂ s hs => by
    ext x
    induction' x using OreLocalization.ind with x s₂
    show OreLocalization.smul' r₁ s x s₂ = OreLocalization.smul' (r₂ * r₁) ⟨_, hs⟩ x s₂
    rcases oreCondition r₁ s₂ with ⟨r₁', s₁', h₁⟩
    rw [smul'_char _ _ _ _ _ _ h₁]
    rcases oreCondition (r₂ * r₁) s₂ with ⟨r₂', s₂', h₂⟩
    rw [smul'_char _ _ _ _ _ _ h₂]
    rcases oreCondition (s₂' * r₂) (s₁') with ⟨r₃', s₃', h₃⟩
    have : s₃' * r₂' * s₂ = r₃' * r₁' * s₂ := by
      rw [mul_assoc, ← h₂, ← mul_assoc _ r₂, ← mul_assoc, h₃, mul_assoc, h₁, mul_assoc]
    rcases ore_right_cancel _ _ _ this with ⟨s₄', h₄⟩
    have : (s₄' * r₃') * (s₁' * s) ∈ S := by
      rw [← mul_assoc, mul_assoc _ r₃', ← h₃, ← mul_assoc, ← mul_assoc, mul_assoc]
      exact mul_mem (s₄' * s₃' * s₂').2 hs
    rw [OreLocalization.expand' (r₂' • x) _ (s₄' * s₃'), OreLocalization.expand _ _ _ this]
    simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, mul_assoc, h₄]
    congr 1
    ext; simp only [Submonoid.coe_mul, ← mul_assoc]
    rw [mul_assoc _ r₃', ← h₃, ← mul_assoc, ← mul_assoc]
#align ore_localization.mul OreLocalization.smul

@[to_additive]
instance : SMul R[S⁻¹] X[S⁻¹] :=
  ⟨OreLocalization.smul⟩

@[to_additive]
instance : Mul R[S⁻¹] :=
  ⟨OreLocalization.smul⟩

@[to_additive]
theorem oreDiv_smul_oreDiv {r₁ : R} {r₂ : X} {s₁ s₂ : S} :
    (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * s₁) :=
  rfl

@[to_additive]
theorem oreDiv_mul_oreDiv {r₁ : R} {r₂ : R} {s₁ s₂ : S} :
    (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = oreNum r₁ s₂ * r₂ /ₒ (oreDenom r₁ s₂ * s₁) :=
  rfl
#align ore_localization.ore_div_mul_ore_div OreLocalization.oreDiv_mul_oreDiv

/-- A characterization lemma for the scalar multiplication on the Ore localization,
allowing for a choice of Ore numerator and Ore denominator. -/
@[to_additive "A characterization lemma for the vector addition on the Ore localization,
allowing for a choice of Ore minuend and Ore subtrahend."]
theorem oreDiv_smul_char (r₁ : R) (r₂ : X) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) :
    (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = r' • r₂ /ₒ (s' * s₁) :=
  smul'_char r₁ r₂ s₁ s₂ s' r' huv

/-- A characterization lemma for the multiplication on the Ore localization, allowing for a choice
of Ore numerator and Ore denominator. -/
@[to_additive "A characterization lemma for the addition on the Ore localization,
allowing for a choice of Ore minuend and Ore subtrahend."]
theorem oreDiv_mul_char (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r' * r₂ /ₒ (s' * s₁) :=
  smul'_char r₁ r₂ s₁ s₂ s' r' huv
#align ore_localization.ore_div_mul_char OreLocalization.oreDiv_mul_char

/-- Another characterization lemma for the scalar multiplication on the Ore localizaion delivering
Ore witnesses and conditions bundled in a sigma type. -/
@[to_additive "Another characterization lemma for the vector addition on the
  Ore localizaion delivering Ore witnesses and conditions bundled in a sigma type."]
def oreDivSMulChar' (r₁ : R) (r₂ : X) (s₁ s₂ : S) :
    Σ'r' : R, Σ's' : S, s' * r₁ = r' * s₂ ∧ (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = r' • r₂ /ₒ (s' * s₁) :=
  ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_smul_oreDiv⟩

/-- Another characterization lemma for the multiplication on the Ore localizaion delivering
Ore witnesses and conditions bundled in a sigma type. -/
@[to_additive "Another characterization lemma for the addition on the Ore localizaion delivering
  Ore witnesses and conditions bundled in a sigma type."]
def oreDivMulChar' (r₁ r₂ : R) (s₁ s₂ : S) :
    Σ'r' : R, Σ's' : S, s' * r₁ = r' * s₂ ∧ r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r' * r₂ /ₒ (s' * s₁) :=
  ⟨oreNum r₁ s₂, oreDenom r₁ s₂, ore_eq r₁ s₂, oreDiv_mul_oreDiv⟩
#align ore_localization.ore_div_mul_char' OreLocalization.oreDivMulChar'

@[to_additive AddOreLocalization.instZeroAddOreLocalization]
instance : One R[S⁻¹] :=
  ⟨1 /ₒ 1⟩

@[to_additive]
protected theorem one_def : (1 : R[S⁻¹]) = 1 /ₒ 1 :=
  rfl
#align ore_localization.one_def OreLocalization.one_def

@[to_additive]
instance : Inhabited R[S⁻¹] :=
  ⟨1⟩

@[to_additive (attr := simp)]
protected theorem div_eq_one' {r : R} (hr : r ∈ S) : r /ₒ ⟨r, hr⟩ = 1 := by
  rw [OreLocalization.one_def, oreDiv_eq_iff]
  exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩
#align ore_localization.div_eq_one' OreLocalization.div_eq_one'

@[to_additive (attr := simp)]
protected theorem div_eq_one {s : S} : (s : R) /ₒ s = 1 :=
  OreLocalization.div_eq_one' _
#align ore_localization.div_eq_one OreLocalization.div_eq_one

@[to_additive]
protected theorem one_smul (x : X[S⁻¹]) : (1 : R[S⁻¹]) • x = x := by
  induction' x using OreLocalization.ind with r s
  simp [OreLocalization.one_def, oreDiv_smul_char 1 r 1 s 1 s (by simp)]

@[to_additive]
protected theorem one_mul (x : R[S⁻¹]) : 1 * x = x :=
  OreLocalization.one_smul x
#align ore_localization.one_mul OreLocalization.one_mul

@[to_additive]
protected theorem mul_one (x : R[S⁻¹]) : x * 1 = x := by
  induction' x using OreLocalization.ind with r s
  simp [OreLocalization.one_def, oreDiv_mul_char r (1 : R) s (1 : S) r 1 (by simp)]
#align ore_localization.mul_one OreLocalization.mul_one

@[to_additive]
protected theorem mul_smul (x y : R[S⁻¹]) (z : X[S⁻¹]) : (x * y) • z = x • y • z := by
  -- Porting note: `assoc_rw` was not ported yet
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivSMulChar' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩; rw [hb']; clear hb'
  rcases oreCondition ra sb with ⟨rc, sc, hc⟩
  rw [oreDiv_smul_char (ra * r₂) r₃ (sa * s₁) s₃ (rc * rb) sc]; swap
  · rw [← mul_assoc _ ra, hc, mul_assoc, hb, ← mul_assoc]
  rw [← mul_assoc, mul_smul]
  symm; apply oreDiv_smul_char
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mul_assoc, ← hc, mul_assoc _ ra, ← ha, mul_assoc]

@[to_additive]
protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) :=
  OreLocalization.mul_smul x y z
#align ore_localization.mul_assoc OreLocalization.mul_assoc

@[to_additive]
instance : Monoid R[S⁻¹] where
  one_mul := OreLocalization.one_mul
  mul_one := OreLocalization.mul_one
  mul_assoc := OreLocalization.mul_assoc

@[to_additive]
instance instMulActionOreLocalization : MulAction R[S⁻¹] X[S⁻¹] where
  one_smul := OreLocalization.one_smul
  mul_smul := OreLocalization.mul_smul

@[to_additive]
protected theorem mul_inv (s s' : S) : ((s : R) /ₒ s') * ((s' : R) /ₒ s) = 1 := by
  simp [oreDiv_mul_char (s : R) s' s' s 1 1 (by simp)]
#align ore_localization.mul_inv OreLocalization.mul_inv

@[to_additive (attr := simp)]
protected theorem one_div_smul {r : X} {s t : S} : ((1 : R) /ₒ t) • (r /ₒ s) = r /ₒ (s * t) := by
  simp [oreDiv_smul_char 1 r t s 1 s (by simp)]

@[to_additive (attr := simp)]
protected theorem one_div_mul {r : R} {s t : S} : (1 /ₒ t) * (r /ₒ s) = r /ₒ (s * t) := by
  simp [oreDiv_mul_char 1 r t s 1 s (by simp)]
#align ore_localization.mul_one_div OreLocalization.one_div_mul

@[to_additive (attr := simp)]
protected theorem smul_cancel {r : X} {s t : S} : ((s : R) /ₒ t) • (r /ₒ s) = r /ₒ t := by
  simp [oreDiv_smul_char s.1 r t s 1 1 (by simp)]

@[to_additive (attr := simp)]
protected theorem mul_cancel {r : R} {s t : S} : ((s : R) /ₒ t) * (r /ₒ s) = r /ₒ t := by
  simp [oreDiv_mul_char s.1 r t s 1 1 (by simp)]
#align ore_localization.mul_cancel OreLocalization.mul_cancel

@[to_additive (attr := simp)]
protected theorem smul_cancel' {r₁ : R} {r₂ : X} {s t : S} :
    ((r₁ * s) /ₒ t) • (r₂ /ₒ s) = (r₁ • r₂) /ₒ t := by
  simp [oreDiv_smul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]

@[to_additive (attr := simp)]
protected theorem mul_cancel' {r₁ r₂ : R} {s t : S} :
    ((r₁ * s) /ₒ t) * (r₂ /ₒ s) = (r₁ * r₂) /ₒ t := by
  simp [oreDiv_mul_char (r₁ * s) r₂ t s r₁ 1 (by simp)]
#align ore_localization.mul_cancel' OreLocalization.mul_cancel'

@[to_additive (attr := simp)]
theorem smul_div_one {p : R} {r : X} {s : S} : (p /ₒ s) • (r /ₒ 1) = (p • r) /ₒ s := by
  simp [oreDiv_smul_char p r s 1 p 1 (by simp)]

@[to_additive (attr := simp)]
theorem mul_div_one {p r : R} {s : S} : (p /ₒ s) * (r /ₒ 1) = (p * r) /ₒ s := by
  --TODO use coercion r ↦ r /ₒ 1
  simp [oreDiv_mul_char p r s 1 p 1 (by simp)]
#align ore_localization.div_one_mul OreLocalization.mul_div_one

@[to_additive]
instance : SMul R X[S⁻¹] where
  smul r := liftExpand (fun x s ↦ oreNum r s • x /ₒ (oreDenom r s)) (by
    intro x r' s h
    dsimp only
    rw [← mul_one (oreDenom r s), ← oreDiv_smul_oreDiv, ← mul_one (oreDenom _ _),
      ← oreDiv_smul_oreDiv, ← OreLocalization.expand])

@[to_additive]
theorem smul_oreDiv (r : R) (x : X) (s : S) : r • (x /ₒ s) = oreNum r s • x /ₒ (oreDenom r s) :=
  rfl

@[to_additive (attr := simp)]
theorem oreDiv_one_smul (r : R) (x : X[S⁻¹]) : (r /ₒ (1 : S)) • x = r • x := by
  induction' x using OreLocalization.ind with r s
  rw [smul_oreDiv, oreDiv_smul_oreDiv, mul_one]

@[to_additive]
instance : MulAction R X[S⁻¹] where
  one_smul := OreLocalization.ind fun x s ↦ by
    rw [← oreDiv_one_smul, ← OreLocalization.one_def, one_smul]
  mul_smul r r' := OreLocalization.ind fun x s ↦ by
    rw [← oreDiv_one_smul, ← oreDiv_one_smul, ← oreDiv_one_smul, ← mul_div_one, mul_smul]

@[to_additive]
instance : IsScalarTower R R[S⁻¹] X[S⁻¹] where
  smul_assoc a b c := by rw [← oreDiv_one_smul, ← oreDiv_one_smul, smul_smul, smul_eq_mul]

/-- The fraction `s /ₒ 1` as a unit in `R[S⁻¹]`, where `s : S`. -/
@[to_additive "The difference `s -ₒ 0` as a an additive unit."]
def numeratorUnit (s : S) : Units R[S⁻¹] where
  val := (s : R) /ₒ 1
  inv := (1 : R) /ₒ s
  val_inv := OreLocalization.mul_inv s 1
  inv_val := OreLocalization.mul_inv 1 s
#align ore_localization.numerator_unit OreLocalization.numeratorUnit

/-- The multiplicative homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the
fraction `r /ₒ 1`. -/
@[to_additive "The additive homomorphism from `R` to `AddOreLocalization R S`,
  mapping `r : R` to the difference `r -ₒ 0`."]
def numeratorHom : R →* R[S⁻¹] where
  toFun r := r /ₒ 1
  map_one' := rfl
  map_mul' _ _ := mul_div_one.symm
#align ore_localization.numerator_hom OreLocalization.numeratorHom

@[to_additive]
theorem numeratorHom_apply {r : R} : numeratorHom r = r /ₒ (1 : S) :=
  rfl
#align ore_localization.numerator_hom_apply OreLocalization.numeratorHom_apply

@[to_additive]
theorem numerator_isUnit (s : S) : IsUnit (numeratorHom (s : R) : R[S⁻¹]) :=
  ⟨numeratorUnit s, rfl⟩
#align ore_localization.numerator_is_unit OreLocalization.numerator_isUnit

section UMP

variable {T : Type*} [Monoid T]
variable (f : R →* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a morphism `R →* T`, which maps elements of `S` to units of `T`,
to a morphism `R[S⁻¹] →* T`. -/
@[to_additive "The universal lift from a morphism `R →+ T`, which maps elements of `S` to
  additive-units of `T`, to a morphism `AddOreLocalization R S →+ T`."]
def universalMulHom : R[S⁻¹] →* T where
  -- Porting note(#12129): additional beta reduction needed
  toFun x :=
    x.liftExpand (fun r s => ((fS s)⁻¹ : Units T) * f r) fun r t s ht => by
      simp only [smul_eq_mul]
      have : (fS ⟨t * s, ht⟩ : T) = f t * fS s := by
        simp only [← hf, MonoidHom.map_mul]
      conv_rhs =>
        rw [MonoidHom.map_mul, ← one_mul (f r), ← Units.val_one, ← mul_right_inv (fS s)]
        rw [Units.val_mul, mul_assoc, ← mul_assoc _ (fS s : T), ← this, ← mul_assoc]
      simp only [one_mul, Units.inv_mul]
  map_one' := by beta_reduce; rw [OreLocalization.one_def, liftExpand_of]; simp
  map_mul' x y := by
    -- Porting note: `simp only []` required, not just for beta reductions
    beta_reduce
    simp only [] -- TODO more!
    induction' x using OreLocalization.ind with r₁ s₁
    induction' y using OreLocalization.ind with r₂ s₂
    rcases oreDivMulChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
    rw [liftExpand_of, liftExpand_of, liftExpand_of, Units.inv_mul_eq_iff_eq_mul, map_mul, map_mul,
      Units.val_mul, mul_assoc, ← mul_assoc (fS s₁ : T), ← mul_assoc (fS s₁ : T), Units.mul_inv,
      one_mul, ← hf, ← mul_assoc, ← map_mul _ _ r₁, ha, map_mul, hf s₂, mul_assoc,
      ← mul_assoc (fS s₂ : T), (fS s₂).mul_inv, one_mul]
#align ore_localization.universal_mul_hom OreLocalization.universalMulHom

@[to_additive]
theorem universalMulHom_apply {r : R} {s : S} :
    universalMulHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl
#align ore_localization.universal_mul_hom_apply OreLocalization.universalMulHom_apply

@[to_additive]
theorem universalMulHom_commutes {r : R} : universalMulHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalMulHom_apply]
#align ore_localization.universal_mul_hom_commutes OreLocalization.universalMulHom_commutes

/-- The universal morphism `universalMulHom` is unique. -/
@[to_additive "The universal morphism `universalAddHom` is unique."]
theorem universalMulHom_unique (φ : R[S⁻¹] →* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalMulHom f fS hf := by
  ext x; induction' x using OreLocalization.ind with r s
  rw [universalMulHom_apply, ← huniv r, numeratorHom_apply, ← one_mul (φ (r /ₒ s)), ←
    Units.val_one, ← mul_left_inv (fS s), Units.val_mul, mul_assoc, ← hf, ← huniv, ← φ.map_mul,
    numeratorHom_apply, OreLocalization.mul_cancel]
#align ore_localization.universal_mul_hom_unique OreLocalization.universalMulHom_unique

end UMP

end Monoid

section CommMonoid

variable {R : Type*} [CommMonoid R] {S : Submonoid R} [OreSet S]

@[to_additive]
theorem oreDiv_mul_oreDiv_comm {r₁ r₂ : R} {s₁ s₂ : S} :
    r₁ /ₒ s₁ * (r₂ /ₒ s₂) = r₁ * r₂ /ₒ (s₁ * s₂) := by
  rw [oreDiv_mul_char r₁ r₂ s₁ s₂ r₁ s₂ (by simp [mul_comm]), mul_comm s₂]
#align ore_localization.ore_div_mul_ore_div_comm OreLocalization.oreDiv_mul_oreDiv_comm

@[to_additive]
instance : CommMonoid R[S⁻¹] where
  mul_comm := fun x y => by
    induction' x using OreLocalization.ind with r₁ s₁
    induction' y using OreLocalization.ind with r₂ s₂
    rw [oreDiv_mul_oreDiv_comm, oreDiv_mul_oreDiv_comm, mul_comm r₁, mul_comm s₁]

end CommMonoid

section DistribMulAction

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S] {X : Type*} [AddMonoid X]
variable [DistribMulAction R X]

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
private def add : X[S⁻¹] → X[S⁻¹] → X[S⁻¹] := fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction' x using OreLocalization.ind with r₃ s₃
      show add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition rc sb with ⟨rd, sd, hd⟩
      have : rd * rb * s₁ = sd * sc * s₃ := by
        rw [mul_assoc, ← hb', ← mul_assoc, ← hd, mul_assoc, ← hc, mul_assoc]
      rw [add''_char _ _ _ _ rc sc hc (sc * s₃).2]
      rw [add''_char _ _ _ _ _ _ this.symm (sd * sc * s₃).2]
      refine oreDiv_eq_iff.mpr ?_
      simp only [Submonoid.mk_smul, smul_add]
      use sd, 1
      simp only [one_smul, one_mul, mul_smul, ← hb, Submonoid.smul_def, ← mul_assoc, and_true]
      simp only [smul_smul, hd])

instance : Add X[S⁻¹] :=
  ⟨add⟩

theorem oreDiv_add_oreDiv {r r' : X} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (oreDenom (s : R) s' * s) :=
  rfl
#align ore_localization.ore_div_add_ore_div OreLocalization.oreDiv_add_oreDiv

theorem oreDiv_add_char' {r r' : X} (s s' : S) (rb : R) (sb : R)
    (h : sb * s = rb * s') (h' : sb * s ∈ S) :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ ⟨sb * s, h'⟩ :=
  add''_char r s r' s' rb sb h h'

/-- A characterization of the addition on the Ore localizaion, allowing for arbitrary Ore
numerator and Ore denominator. -/
theorem oreDiv_add_char {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s') :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ (sb * s) :=
  oreDiv_add_char' s s' rb sb h (sb * s).2
#align ore_localization.ore_div_add_char OreLocalization.oreDiv_add_char

/-- Another characterization of the addition on the Ore localization, bundling up all witnesses
and conditions into a sigma type. -/
def oreDivAddChar' (r r' : X) (s s' : S) :
    Σ'r'' : R,
      Σ's'' : S, s'' * s = r'' * s' ∧ r /ₒ s + r' /ₒ s' = (s'' • r + r'' • r') /ₒ (s'' * s) :=
  ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩
#align ore_localization.ore_div_add_char' OreLocalization.oreDivAddChar'

@[simp]
theorem add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s := by
  simp [oreDiv_add_char s s 1 1 (by simp)]
#align ore_localization.add_ore_div OreLocalization.add_oreDiv

protected theorem add_assoc (x y z : X[S⁻¹]) : x + y + z = x + (y + z) := by
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, mul_assoc, add_assoc]
  simp_rw [← add_oreDiv, ← OreLocalization.expand']
  congr 2
  · rw [OreLocalization.expand r₂ s₂ ra (ha.symm ▸ (sa * s₁).2)]; congr; ext; exact ha
  · rw [OreLocalization.expand r₃ s₃ rc (hc.symm ▸ (sc * (sa * s₁)).2)]; congr; ext; exact hc
#align ore_localization.add_assoc OreLocalization.add_assoc

private def zero : X[S⁻¹] := 0 /ₒ 1

instance : Zero X[S⁻¹] :=
  ⟨zero⟩

protected theorem zero_def : (0 : X[S⁻¹]) = 0 /ₒ 1 :=
  rfl
#align ore_localization.zero_def OreLocalization.zero_def

@[simp]
theorem zero_oreDiv (s : S) : (0 : X) /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩
#align ore_localization.zero_div_eq_zero OreLocalization.zero_oreDiv

protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
  induction x using OreLocalization.ind
  rw [← zero_oreDiv, add_oreDiv]; simp
#align ore_localization.zero_add OreLocalization.zero_add

protected theorem add_zero (x : X[S⁻¹]) : x + 0 = x := by
  induction x using OreLocalization.ind
  rw [← zero_oreDiv, add_oreDiv]; simp

instance : AddMonoid X[S⁻¹] where
    add_assoc := OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmulRec

protected theorem smul_zero (x : R[S⁻¹]) : x • (0 : X[S⁻¹]) = 0 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.zero_def, smul_div_one, smul_zero, zero_oreDiv, zero_oreDiv]

protected theorem smul_add (z : R[S⁻¹]) (x y : X[S⁻¹]) :
    z • (x + y) = z • x + z • y := by
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  rw [← Subtype.coe_eq_of_eq_mk ha]
  repeat rw [oreDiv_smul_oreDiv]
  simp only [smul_add, add_oreDiv]

instance : DistribMulAction R[S⁻¹] X[S⁻¹] where
  smul_zero := OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add

instance : DistribMulAction R X[S⁻¹] where
  smul_zero _ := by rw [← oreDiv_one_smul, smul_zero]
  smul_add _ _ _ := by simp only [← oreDiv_one_smul, smul_add]

end DistribMulAction

section AddCommMonoid

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [DistribMulAction R X]

protected theorem add_comm (x y : X[S⁻¹]) : x + y = y + x := by
  induction' x using OreLocalization.ind with r s
  induction' y using OreLocalization.ind with r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha', oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2), add_comm]
  congr; ext; exact ha
#align ore_localization.add_comm OreLocalization.add_comm

instance instAddCommMonoidOreLocalization : AddCommMonoid X[S⁻¹] where
  add_comm := OreLocalization.add_comm

end AddCommMonoid

section AddGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddGroup X] [DistribMulAction R X]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
protected def neg : X[S⁻¹] → X[S⁻¹] :=
  liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    -- Porting note(#12129): additional beta reduction needed
    beta_reduce
    rw [← smul_neg, ← OreLocalization.expand]
#align ore_localization.neg OreLocalization.neg

instance instNegOreLocalization : Neg X[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
protected theorem neg_def (r : X) (s : S) : -(r /ₒ s) = -r /ₒ s :=
  rfl
#align ore_localization.neg_def OreLocalization.neg_def

protected theorem add_left_neg (x : X[S⁻¹]) : -x + x = 0 := by
  induction' x using OreLocalization.ind with r s; simp
#align ore_localization.add_left_neg OreLocalization.add_left_neg

instance instAddGroupOreLocalization : AddGroup X[S⁻¹] where
  add_left_neg := OreLocalization.add_left_neg
  zsmul := zsmulRec

end AddGroup

section AddCommGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [DistribMulAction R X]

instance : AddCommGroup X[S⁻¹] where
  __ := inferInstanceAs (AddGroup X[S⁻¹])
  __ := inferInstanceAs (AddCommMonoid X[S⁻¹])

end AddCommGroup

end OreLocalization
