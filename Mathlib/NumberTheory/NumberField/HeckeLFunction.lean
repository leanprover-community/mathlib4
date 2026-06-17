/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Hecke L-Functions

In this file, we define the L-function of a Hecke character.

## Main definitions

* `HeckeCharacter R K`: Hecke characters on a number field `K` with ring of integers `R`.
* `HeckeCharacter.LFunction χ`: The L-function of a Hecke character `χ`.
-/

@[expose] public section

noncomputable section

namespace NumberField

open IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A Hecke character is a character on the idele class group. -/
abbrev HeckeCharacter := MulChar (IdeleClassGroup R K) ℂ

variable {R K} (χ : HeckeCharacter R K)

namespace HeckeCharacter

/- The restriction `χᵥ` of a character `χ` to the completion `Kᵥˣ` at a finite place `v`. -/
@[simps!]
def restrict (v : HeightOneSpectrum R) : MulChar (v.adicCompletion K) ℂ :=
  .ofUnitHom <| χ.toUnitHom.comp <| .toHomUnits <| IdeleClassGroup.ofCompletion R K v

/-- A Hecke character `χ` is said to be unramified at a finite place `v` when the restriction `χᵥ`
is trivial on the local unit group `𝓞ᵥˣ` -/
def IsUnramifiedAt (v : HeightOneSpectrum R) : Prop :=
  (χ.restrict v).toUnitHom.comp (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) = 1

variable {χ}

theorem isUnramifiedAt_iff {v : HeightOneSpectrum R} :
    χ.IsUnramifiedAt v ↔ ∀ x : (v.adicCompletionIntegers K)ˣ, χ.restrict v x = 1 := by
  simp [IsUnramifiedAt, MonoidHom.ext_iff, Units.ext_iff]

theorem IsUnramifiedAt.restrict_apply_eq_one
    {v : HeightOneSpectrum R} (h : χ.IsUnramifiedAt v) (x : (v.adicCompletionIntegers K)ˣ) :
    χ.restrict v x = 1 :=
  isUnramifiedAt_iff.mp h x

theorem IsUnramifiedAt.apply_eq_one {v : HeightOneSpectrum R} (h : χ.IsUnramifiedAt v)
    (x : v.adicCompletion K) (hx : Valued.v x = 1) : χ.restrict v x = 1 := by
  have hx : x ∈ v.adicCompletionIntegers K := (v.mem_adicCompletionIntegers R K).mp hx.le
  replace hx : IsUnit (⟨x, hx⟩ : v.adicCompletionIntegers K) := by
    rwa [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, Subtype.coe_mk]
  exact h.restrict_apply_eq_one hx.unit

theorem IsUnramifiedAt.apply_eq {v : HeightOneSpectrum R} (h : χ.IsUnramifiedAt v)
    (x y : v.adicCompletion K) (hxy : Valued.v x = Valued.v y) :
    χ.restrict v x = χ.restrict v y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [eq_comm, map_zero, map_eq_zero] at hxy
    rw [hxy]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero, map_eq_zero] at hxy
    rw [hxy]
  apply eq_of_div_eq_one
  simpa [hx, hy, IsUnit.unit_div] using h.apply_eq_one (x / y) (by simpa [hxy])

theorem IsUnramifiedAt.apply_eq_of_isUniformizer {v : HeightOneSpectrum R} (h : χ.IsUnramifiedAt v)
    {x y : v.adicCompletion K} (hx : Valued.v.IsUniformizer x) (hy : Valued.v.IsUniformizer y) :
    χ.restrict v x = χ.restrict v y :=
  h.apply_eq x y (hx.trans hy.symm)

variable (χ)

open Classical Polynomial in
/-- The value `χᵥ(ϖᵥ)` of a Hecke character `χ` at the uniformizer `ϖᵥ` of finite place `v`. -/
noncomputable def localValue (v : HeightOneSpectrum R) : ℂ :=
  letI val : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  χ.restrict v val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose

variable {χ} in
theorem IsUnramifiedAt.localValue_eq {v : HeightOneSpectrum R}
    (h : χ.IsUnramifiedAt v) (π : v.adicCompletion K) (hπ : Valued.v.IsUniformizer π) :
    χ.localValue v = χ.restrict v π :=
  h.apply_eq_of_isUniformizer Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec hπ

open Classical Polynomial in
/-- The local polynomial associated a Hecke character `χ` at a finite place `v` is `1 - χᵥ(ϖᵥ)X` if
`χ` is unramified at `v` and `1` otherwise. -/
noncomputable def localPolynomial (v : HeightOneSpectrum R) : ℂ[X] :=
  if χ.IsUnramifiedAt v then 1 - C (χ.localValue v) * X else 1

/-- The local power series associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localPowerSeries (v : HeightOneSpectrum R) : PowerSeries ℂ :=
  .invOfUnit (χ.localPolynomial v) 1

/-- The local Euler factor associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localEulerFactor (v : HeightOneSpectrum R) : ArithmeticFunction ℂ :=
  .ofPowerSeries (.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    (χ.localPowerSeries v)

/-- The L-function of a Hecke character `χ` is the product of `1 / (1 - χᵥ(ϖᵥ)‖v‖⁻ˢ)` as `v` ranges
over all finite places at which `χ` is unramified. -/
noncomputable def LFunction : ArithmeticFunction ℂ :=
  .eulerProduct fun v : HeightOneSpectrum R ↦ χ.localEulerFactor v

/-- The L-series of a Hecke character. -/
protected noncomputable def LSeries (s : ℂ) :=
  LSeries χ.LFunction s

end HeckeCharacter

end NumberField
