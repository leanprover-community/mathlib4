/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import HexPolyZ
public import Mathlib.Algebra.Polynomial.Hex.Int
public import Mathlib.Algebra.Polynomial.Hex.Squarefree
public import Mathlib.Analysis.Polynomial.Hex.Basic
public import Mathlib.Analysis.Polynomial.Hex.Sturm

/-!
# Real roots of the square-free core

The certified isolator only handles square-free input, so the `isolate_roots`
elaborator (and `rcf` step 3) run the executable square-free reduction
`Hex.ZPoly.squareFreeCore` first and transport the certified conclusions back
along `aevalIff_squareFreeCore`: a nonzero integer polynomial and its square-free
core have exactly the same real roots.

The proof factors through a **field-generic** lemma
(`isRoot_left_iff_of_mul_of_dvd_derivative`, Hex-free and upstreamable): over a
characteristic-zero field, if `q = c * r` and `r ∣ q'`, then `c` and `q` have
the same roots. It is instantiated at `q = primitivePart p` over `ℝ`, with `c`
the (signed) square-free core and `r` the repeated part, using that the repeated
part is a rational associate of `gcd(primitive, primitive')` — hence divides the
derivative (the executable bridge
`Hex.ZPoly.toRatPoly_repeatedPart_dvd_derivative`).
-/

public section

namespace HexRealRootsMathlib

open Polynomial HexPolyZMathlib

noncomputable section

/-! # The field-generic quotient-roots lemma -/

/-- **Field-generic square-free-core root transfer.** Over a characteristic-zero
field, if `q = c * r` (with `q ≠ 0`) and `r` divides the derivative `q'`, then a
point is a root of `c` iff it is a root of `q`. The root-multiplicity argument:
at a root `a` of multiplicity `m ≥ 1`, `q'` has multiplicity `m − 1`
(characteristic zero), so `r ∣ q'` forces the `r`-multiplicity of `a` below `m`,
leaving `c` with multiplicity at least one; conversely any root of `c` is a root
of the product `q`. Hex-free; a candidate Mathlib contribution. -/
theorem isRoot_left_iff_of_mul_of_dvd_derivative {K : Type*} [Field K] [CharZero K]
    {q c r : K[X]} (hq : q ≠ 0) (hqcr : q = c * r) (hrd : r ∣ derivative q) (a : K) :
    c.IsRoot a ↔ q.IsRoot a := by
  have hcr0 : c * r ≠ 0 := hqcr ▸ hq
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcr0
  have hmul : rootMultiplicity a q = rootMultiplicity a c + rootMultiplicity a r := by
    rw [hqcr]; exact rootMultiplicity_mul (hqcr ▸ hq)
  constructor
  · intro hca
    have hcpos : 0 < rootMultiplicity a c := (rootMultiplicity_pos hc0).mpr hca
    rw [← rootMultiplicity_pos hq, hmul]
    omega
  · intro hqa
    rw [← rootMultiplicity_pos hc0]
    have hqpos : 0 < rootMultiplicity a q := (rootMultiplicity_pos hq).mpr hqa
    have hderiv : rootMultiplicity a (derivative q) = rootMultiplicity a q - 1 :=
      derivative_rootMultiplicity_of_root hqa
    have hq'0 : derivative q ≠ 0 := by
      intro h
      have hqC : q = C (q.coeff 0) := eq_C_of_derivative_eq_zero h
      have hcoeff0 : q.coeff 0 = 0 := by
        have he : q.eval a = 0 := hqa
        rw [hqC, eval_C] at he
        exact he
      exact hq (by rw [hqC, hcoeff0, C_0])
    have hle : rootMultiplicity a r ≤ rootMultiplicity a (derivative q) :=
      rootMultiplicity_le_rootMultiplicity_of_dvd hq'0 hrd a
    rw [hderiv] at hle
    omega

/-! # Cast helpers -/

/-- `aeval` at a real point of an embedded integer polynomial is the evaluation
of its real cast. -/
theorem aeval_eq_eval_toPolyℝ (q : Hex.ZPoly) (x : ℝ) :
    aeval x (toPolynomial q) = (toPolyℝ q).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

/-- The real cast is the composition of the rational cast with `ℚ → ℝ`. -/
theorem toPolyℝ_eq_map_toPolyℚ (q : Hex.ZPoly) :
    toPolyℝ q = (toPolyℚ q).map (algebraMap ℚ ℝ) := by
  have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.ext_int _ _
  change (toPolynomial q).map (Int.castRingHom ℝ)
    = ((toPolynomial q).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)
  rw [Polynomial.map_map, hcomp]

/-- **Executable-to-real divisibility.** The real cast of the repeated part
divides the derivative of the real cast of the primitive part: the executable
rational divisibility, transported through `ℚ` and then `ℚ → ℝ`. -/
theorem toPolyℝ_repeatedPart_dvd_derivative (p : Hex.ZPoly) :
    toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart ∣
      derivative (toPolyℝ (Hex.ZPoly.primitivePart p)) := by
  have hexec := Hex.ZPoly.toRatPoly_repeatedPart_dvd_derivative p
  -- Transport to `Polynomial ℚ` by destructuring the executable divisibility.
  obtain ⟨s, hs⟩ := hexec
  have hq : toPolyℚ (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart ∣
      derivative (toPolyℚ (Hex.ZPoly.primitivePart p)) := by
    refine ⟨HexPolyMathlib.toPolynomial s, ?_⟩
    have hcong := congrArg HexPolyMathlib.toPolynomial hs
    rw [HexPolyMathlib.toPolynomial_derivative, HexPolyMathlib.toPolynomial_mul,
      toPolynomial_toRatPoly, toPolynomial_toRatPoly] at hcong
    exact hcong
  -- Map along `ℚ → ℝ`.
  obtain ⟨t, ht⟩ := hq
  refine ⟨t.map (algebraMap ℚ ℝ), ?_⟩
  have hcong := congrArg (Polynomial.map (algebraMap ℚ ℝ)) ht
  rw [← Polynomial.derivative_map, Polynomial.map_mul, ← toPolyℝ_eq_map_toPolyℚ,
    ← toPolyℝ_eq_map_toPolyℚ] at hcong
  exact hcong

/-! # The square-free-core root iff -/

/-- **Square-free core preserves real roots.** A nonzero integer polynomial and
its executable square-free core have exactly the same real roots, stated through
`aeval` at real points. Shared with the `rcf` decision procedure (step 3) and
consumed by the `isolate_roots` elaborator to reduce to square-free input. -/
theorem aevalIff_squareFreeCore {p : Hex.ZPoly} (hp0 : p ≠ 0) (x : ℝ) :
    aeval x (toPolynomial (Hex.ZPoly.squareFreeCore p)) = 0 ↔
      aeval x (toPolynomial p) = 0 := by
  rw [aeval_eq_eval_toPolyℝ, aeval_eq_eval_toPolyℝ, Hex.ZPoly.squareFreeCore_eq]
  -- Reduce to `IsRoot` of the square-free core vs `p`.
  rcases Hex.ZPoly.primitiveSquareFreeDecomposition_reassembly_signed p hp0 with ⟨ε, hε, hre⟩
  have hε0 : ((ε : Int) : ℝ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hprim_ne : toPolyℝ (Hex.ZPoly.primitivePart p) ≠ 0 := by
    rw [Ne, toPolyℝ_eq_zero_iff]; exact primitivePart_ne_zero hp0
  -- The signed reassembly over `ℝ`.
  have hreℝ : toPolyℝ (Hex.ZPoly.primitivePart p) =
      Polynomial.C ((ε : Int) : ℝ) *
        (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore *
          toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart) := by
    have hcong := congrArg toPolyℝ hre
    rw [toPolyℝ_scale, toPolyℝ_mul] at hcong
    exact hcong.symm
  -- Apply the field-generic lemma at `q = primitivePart`, `c = C ε * core`,
  -- `r = repeatedPart`.
  have hqcr : toPolyℝ (Hex.ZPoly.primitivePart p) =
      (Polynomial.C ((ε : Int) : ℝ) *
        toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore) *
        toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart := by
    rw [hreℝ, mul_assoc]
  have hrd : toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).repeatedPart ∣
      derivative (toPolyℝ (Hex.ZPoly.primitivePart p)) :=
    toPolyℝ_repeatedPart_dvd_derivative p
  have hgen := isRoot_left_iff_of_mul_of_dvd_derivative hprim_ne hqcr hrd x
  -- Strip the `C ε` factor.
  have hCe : (Polynomial.C ((ε : Int) : ℝ) *
      toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).IsRoot x ↔
      (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).IsRoot x := by
    constructor
    · intro h
      have hval : ((ε : Int) : ℝ) *
          (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).eval x = 0 := by
        simpa [IsRoot, eval_mul, eval_C] using h
      rcases mul_eq_zero.mp hval with h1 | h1
      · exact absurd h1 hε0
      · exact h1
    · intro h
      change (Polynomial.C ((ε : Int) : ℝ) *
        toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).eval x = 0
      rw [eval_mul, eval_C, show
        (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).eval x = 0 from h,
        mul_zero]
  -- Strip the content factor: `p` and its primitive part share roots.
  have hcontent : (toPolyℝ (Hex.ZPoly.primitivePart p)).IsRoot x ↔ (toPolyℝ p).IsRoot x := by
    have hpp : toPolyℝ p = Polynomial.C ((Hex.ZPoly.content p : Int) : ℝ) *
        toPolyℝ (Hex.ZPoly.primitivePart p) :=
      toPolyℝ_eq_C_content_mul_primitivePart p
    constructor
    · intro h
      change (toPolyℝ p).eval x = 0
      rw [hpp, eval_mul, eval_C, show (toPolyℝ (Hex.ZPoly.primitivePart p)).eval x = 0 from h,
        mul_zero]
    · intro h
      have hval : ((Hex.ZPoly.content p : Int) : ℝ) *
          (toPolyℝ (Hex.ZPoly.primitivePart p)).eval x = 0 := by
        have h2 : (toPolyℝ p).eval x = 0 := h
        rwa [hpp, eval_mul, eval_C] at h2
      rcases mul_eq_zero.mp hval with h1 | h1
      · exact absurd h1 (ne_of_gt (content_real_pos hp0))
      · exact h1
  -- Chain the three iffs.
  change (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).IsRoot x ↔
    (toPolyℝ p).IsRoot x
  calc (toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).IsRoot x
      ↔ (Polynomial.C ((ε : Int) : ℝ) *
          toPolyℝ (Hex.ZPoly.primitiveSquareFreeDecomposition p).squareFreeCore).IsRoot x :=
            hCe.symm
    _ ↔ (toPolyℝ (Hex.ZPoly.primitivePart p)).IsRoot x := hgen
    _ ↔ (toPolyℝ p).IsRoot x := hcontent

end

end HexRealRootsMathlib
