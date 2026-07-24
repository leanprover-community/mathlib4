/-
Copyright (c) 2026 Sanad Kadu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sanad Kadu
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.RCLike.Basic

/-!
# Donoho–Stark support uncertainty principle for finite abelian groups

This file proves the support uncertainty principle for the unitary Fourier transform
on a finite abelian group `G`, indexed by its Pontryagin dual `AddChar G ℂ`:

**Theorem** (`AddChar.donoho_stark`). For every nonzero `f : G → ℂ`,
$$
|\operatorname{supp}(f)| \cdot |\operatorname{supp}(\widehat{f})| \;\ge\; |G|
$$
where $\widehat{f}(\psi) = |G|^{-1/2} \cdot \sum_g \overline{\psi(g)} \cdot f(g)$
ranges over $\psi \in \operatorname{AddChar}(G, \mathbb{C})$.

This is the natural finite-abelian generalisation of the classical Donoho–Stark
inequality for $\mathbb{Z}/N\mathbb{Z}$ (Donoho–Stark 1989,
*Uncertainty principles and signal recovery*, SIAM J. Appl. Math. 49(3): 906–931),
which itself is the discrete analogue of the continuous Heisenberg uncertainty.
The proof uses only the elementary $(L^1, L^\infty)$ duality argument: the
transform of a function is bounded by its $L^1$ norm, the inverse transform of
the transform recovers the function, and chaining the two triangle inequalities
gives the support-product bound. No Parseval or Cauchy–Schwarz is needed.

## Main results

* `AddChar.fourierTransform` — the symmetric (unitary) Fourier transform on a
  finite abelian group, indexed by `AddChar G ℂ`.
* `AddChar.fourier_inversion` — inversion formula.
* `AddChar.donoho_stark` — the support uncertainty principle:
  `Fintype.card G ≤ (support f).ncard * (support (fourierTransform f)).ncard`.

## Reference

* Donoho, D. L. and Stark, P. B. (1989), *Uncertainty principles and signal
  recovery*, SIAM Journal on Applied Mathematics, **49**(3): 906–931.
  https://doi.org/10.1137/0149053

## Implementation notes

Support sizes are stated as `(Function.support f).ncard`. On a finite type,
`Function.support f` is automatically finite, and the `Set.ncard` reading
avoids needing decidable equality on `ℂ` while matching the standard
Donoho–Stark statement `|{g : f(g) ≠ 0}| · |{ψ : f̂(ψ) ≠ 0}| ≥ |G|`.

The original proof was generated with the assistance of the Aristotle proof
system (Harmonic AI), then audited against Donoho–Stark 1989 and adapted to
Mathlib conventions by the author.
-/

@[expose] public section

open Finset Function
open scoped ComplexConjugate

namespace AddChar

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The symmetric (unitary) Fourier transform on a finite abelian group `G`,
indexed by the Pontryagin dual `AddChar G ℂ`:
$\widehat{f}(\psi) = |G|^{-1/2} \cdot \sum_g \overline{\psi(g)} \cdot f(g)$. -/
noncomputable def fourierTransform (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ) * ∑ g, conj (ψ g) * f g

omit [AddCommGroup G] in
private lemma sqrt_card_inv_nonneg : (0 : ℝ) ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹ :=
  inv_nonneg.2 (Real.sqrt_nonneg _)

omit [AddCommGroup G] in
private lemma sqrt_card_inv_sq :
    (Real.sqrt (Fintype.card G : ℝ))⁻¹ * (Real.sqrt (Fintype.card G : ℝ))⁻¹
      = ((Fintype.card G : ℝ))⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by positivity)]

/-- **Fourier inversion** on a finite abelian group:
`f g = |G|^{-1/2} · ∑_ψ ψ(g) · f̂(ψ)`. -/
theorem fourier_inversion (f : G → ℂ) (g : G) :
    f g = ((Real.sqrt (Fintype.card G : ℝ))⁻¹ : ℂ)
          * ∑ ψ : AddChar G ℂ, ψ g * fourierTransform f ψ := by
  -- Expand `fourierTransform`, swap sums, use character orthogonality:
  -- `∑_ψ ψ(g - x) = |G|` if `g = x`, else `0`.
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsq : ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹
        * ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹
      = ((Fintype.card G : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
      Complex.ofReal_natCast]
  have hmain : ∑ ψ : AddChar G ℂ, ψ g * fourierTransform f ψ
      = ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ * ((Fintype.card G : ℂ) * f g) :=
    calc ∑ ψ : AddChar G ℂ, ψ g * fourierTransform f ψ
        = ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹
            * ∑ ψ : AddChar G ℂ, ψ g * ∑ x, conj (ψ x) * f x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ψ _ => by simp only [fourierTransform]; ring
      _ = ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹
            * ∑ ψ : AddChar G ℂ, ∑ x, ψ (g - x) * f x := by
          refine congrArg _ (Finset.sum_congr rfl fun ψ _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← mul_assoc, ← AddChar.inv_apply_eq_conj, ← ψ.map_neg_eq_inv,
            ← ψ.map_add_eq_mul, ← sub_eq_add_neg]
      _ = ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ * ((Fintype.card G : ℂ) * f g) := by
          refine congrArg _ ?_
          rw [Finset.sum_comm]
          calc ∑ x, ∑ ψ : AddChar G ℂ, ψ (g - x) * f x
              = ∑ x, (∑ ψ : AddChar G ℂ, ψ (g - x)) * f x :=
                Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
            _ = (Fintype.card G : ℂ) * f g := by
                rw [Finset.sum_eq_single g
                  (fun b _ hb => by
                    rw [AddChar.sum_apply_eq_ite, if_neg (sub_ne_zero.mpr (Ne.symm hb)),
                      zero_mul])
                  (fun h => absurd (Finset.mem_univ g) h),
                  sub_self, AddChar.sum_apply_eq_ite, if_pos rfl]
  rw [hmain, ← mul_assoc, hsq, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- $L^\infty \le |G|^{-1/2} \cdot L^1$ for the Fourier transform. -/
theorem norm_fourierTransform_le (f : G → ℂ) (ψ : AddChar G ℂ) :
    ‖fourierTransform f ψ‖
      ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹ * ∑ g, ‖f g‖ := by
  simp only [fourierTransform]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  refine norm_sum_le _ _ |>.trans ?_
  refine Finset.sum_le_sum fun g _ => ?_
  rw [norm_mul]
  refine le_of_eq ?_
  rw [show ‖conj (ψ g)‖ = ‖ψ g‖ from by simp, ψ.norm_apply, one_mul]

/-- $L^\infty \le |G|^{-1/2} \cdot L^1$ for the inverse Fourier transform
(consequence of inversion and the triangle inequality). -/
theorem norm_le_sum_norm_fourierTransform (f : G → ℂ) (g : G) :
    ‖f g‖ ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹
          * ∑ ψ : AddChar G ℂ, ‖fourierTransform f ψ‖ := by
  rw [fourier_inversion f g, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  refine norm_sum_le _ _ |>.trans ?_
  refine Finset.sum_le_sum fun ψ _ => ?_
  rw [norm_mul, ψ.norm_apply, one_mul]

/-- **Donoho–Stark support uncertainty principle for finite abelian groups.**

For every nonzero `f : G → ℂ`:
$$
|\operatorname{supp}(f)| \cdot |\operatorname{supp}(\widehat{f})| \;\ge\; |G|,
$$
where $\widehat{f}$ is the unitary Fourier transform indexed by the Pontryagin
dual `AddChar G ℂ` (which has the same cardinality as `G`).

The classical Donoho–Stark inequality for $\mathbb{Z}/N\mathbb{Z}$ is the
instance `G = ZMod N`; the Walsh–Hadamard / Boolean-cube version
(`|{x : f(x) ≠ 0}| · |{y : f̂(y) ≠ 0}| ≥ 2^n`) is the instance
`G = Fin n → ZMod 2`, indexed via the standard Pontryagin pairing
`(x, y) ↦ (-1)^{x · y}`.

The proof is the elementary $(L^1, L^\infty)$ duality argument: bound `‖f̂‖_∞`
by `|G|^{-1/2} ‖f‖₁`, bound `‖f‖_∞` similarly via inversion, chain, and cancel
`‖f‖_∞ > 0`.

**Reference.** Donoho–Stark 1989, SIAM J. Appl. Math. 49(3): 906–931. -/
theorem donoho_stark (f : G → ℂ) (hf : f ≠ 0) :
    Fintype.card G
      ≤ (Function.support f).ncard * (Function.support (fourierTransform f)).ncard := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite (Function.support f)),
      Set.ncard_eq_toFinset_card _ (Set.toFinite (Function.support (fourierTransform f)))]
  -- Let `Mf = max_g ‖f g‖` and `Mψ = max_ψ ‖f̂ ψ‖`. By the triangle bounds
  -- above, `Mψ ≤ |G|^{-1/2} · |supp f| · Mf` (each value `f̂(ψ)` is a sum
  -- of `|supp f|` terms each ≤ `Mf` after the `|G|^{-1/2}` scaling), and
  -- similarly `Mf ≤ |G|^{-1/2} · |supp f̂| · Mψ`. Multiplying,
  -- `Mf · Mψ ≤ |G|^{-1} · |supp f| · |supp f̂| · Mf · Mψ`. Since `f ≠ 0`,
  -- both maxima are positive, so we may cancel to obtain
  -- `|G| ≤ |supp f| · |supp f̂|`.
  set Mf := Finset.univ.sup' Finset.univ_nonempty (fun g => ‖f g‖)
  set Mψ := Finset.univ.sup' Finset.univ_nonempty (fun ψ => ‖fourierTransform f ψ‖)
  obtain ⟨g₀, hg₀⟩ : ∃ g, f g ≠ 0 := Function.ne_iff.mp hf
  have hMf_pos : 0 < Mf :=
    lt_of_lt_of_le (norm_pos_iff.mpr hg₀)
      (Finset.le_sup' (fun g => ‖f g‖) (Finset.mem_univ g₀))
  -- Bound 1: Mψ ≤ |G|^{-1/2} · |supp f| · Mf.
  have hMψ_le : Mψ ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹
                    * (Set.toFinite (Function.support f)).toFinset.card * Mf := by
    refine Finset.sup'_le _ _ fun ψ _ => ?_
    refine (norm_fourierTransform_le f ψ).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ sqrt_card_inv_nonneg
    calc ∑ g, ‖f g‖
        = ∑ g ∈ (Set.toFinite (Function.support f)).toFinset, ‖f g‖ := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro g _ hg
          simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hg
          simp [hg]
      _ ≤ (Set.toFinite (Function.support f)).toFinset.card * Mf := by
          rw [← nsmul_eq_mul]
          refine Finset.sum_le_card_nsmul _ _ Mf fun g _ => ?_
          exact Finset.le_sup' (fun g => ‖f g‖) (Finset.mem_univ g)
  -- Bound 2: Mf ≤ |G|^{-1/2} · |supp f̂| · Mψ.
  have hMf_le : Mf ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹
                  * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card * Mψ := by
    refine Finset.sup'_le _ _ fun g _ => ?_
    refine (norm_le_sum_norm_fourierTransform f g).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ sqrt_card_inv_nonneg
    calc ∑ ψ : AddChar G ℂ, ‖fourierTransform f ψ‖
        = ∑ ψ ∈ (Set.toFinite (Function.support (fourierTransform f))).toFinset,
            ‖fourierTransform f ψ‖ := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro ψ _ hψ
          simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hψ
          simp [hψ]
      _ ≤ (Set.toFinite (Function.support (fourierTransform f))).toFinset.card * Mψ := by
          rw [← nsmul_eq_mul]
          refine Finset.sum_le_card_nsmul _ _ Mψ fun ψ _ => ?_
          exact Finset.le_sup' (fun ψ => ‖fourierTransform f ψ‖) (Finset.mem_univ ψ)
  -- Chain and cancel `Mf > 0`.
  have hchain : Mf ≤ ((Fintype.card G : ℝ))⁻¹
                  * (Set.toFinite (Function.support f)).toFinset.card
                  * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card
                  * Mf := by
    calc Mf
        ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹
            * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card * Mψ := hMf_le
      _ ≤ (Real.sqrt (Fintype.card G : ℝ))⁻¹
            * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card
            * ((Real.sqrt (Fintype.card G : ℝ))⁻¹
                * (Set.toFinite (Function.support f)).toFinset.card * Mf) := by
            refine mul_le_mul_of_nonneg_left hMψ_le ?_
            positivity
      _ = ((Fintype.card G : ℝ))⁻¹
            * (Set.toFinite (Function.support f)).toFinset.card
            * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card
            * Mf := by
            rw [show ((Real.sqrt (Fintype.card G : ℝ))⁻¹
                  * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card)
                  * ((Real.sqrt (Fintype.card G : ℝ))⁻¹
                      * (Set.toFinite (Function.support f)).toFinset.card * Mf)
                = ((Real.sqrt (Fintype.card G : ℝ))⁻¹
                    * (Real.sqrt (Fintype.card G : ℝ))⁻¹)
                    * (Set.toFinite (Function.support f)).toFinset.card
                    * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card
                    * Mf from by ring,
                sqrt_card_inv_sq]
  -- Divide through by Mf > 0:
  have h1 : (1 : ℝ) ≤ ((Fintype.card G : ℝ))⁻¹
                    * (Set.toFinite (Function.support f)).toFinset.card
                    * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card := by
    have hdiv := (div_le_iff₀ hMf_pos).mpr hchain
    rwa [div_self hMf_pos.ne'] at hdiv
  -- Clear the |G|⁻¹ denominator:
  have hcard_pos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h2 : (Fintype.card G : ℝ)
          ≤ (Set.toFinite (Function.support f)).toFinset.card
            * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card := by
    have h3 : (Fintype.card G : ℝ) * 1
              ≤ (Fintype.card G : ℝ)
                  * (((Fintype.card G : ℝ))⁻¹
                      * (Set.toFinite (Function.support f)).toFinset.card
                      * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card) :=
      mul_le_mul_of_nonneg_left h1 hcard_pos.le
    rw [mul_one] at h3
    have h4 : (Fintype.card G : ℝ)
                  * (((Fintype.card G : ℝ))⁻¹
                      * (Set.toFinite (Function.support f)).toFinset.card
                      * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card)
              = (Set.toFinite (Function.support f)).toFinset.card
                * (Set.toFinite (Function.support (fourierTransform f))).toFinset.card := by
      field_simp
    rw [h4] at h3
    exact h3
  exact_mod_cast h2

end AddChar
