/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKZeroCharge
import Archive.GaussianMomentConjecture.HeightWitness
import Archive.GaussianMomentConjecture.LaurentShiftCheckA
import Archive.GaussianMomentConjecture.Thm2067HSonly
import Mathlib

set_option linter.minImports true

/-!
# The univariate reduction: `DvdK1BothSigns` from the single-polynomial crux

This is the **top-level integration** connecting the one-variable Duistermaat–van der Kallen input
`GMC2DvdKZeroCharge.DvdK1BothSigns` (a statement about the universal constant-term relations of an
arbitrary both-signs charge support) to the concrete Galois orbit-product route on a single polynomial
`Φ = Phi R M = Xᴹ − t·R`.

The bridge is Check A (`LaurentShiftCheckA`): shifting the finite charge support upward by
`M` produces an ordinary polynomial `R = shiftedPolynomial q c M` whose central power coefficients are
exactly the evaluated constant-term relations,
`(Rᵐ).coeff (M·m) = aeval c (constantTermRelation q m)` (`= D_m`).  A both-signs support determines a
canonical shift `M = −min_i q_i ≥ 1` for which `R.coeff 0 ≠ 0` (the unique minimal charge) and
`M < R.natDegree` (the unique maximal, strictly positive, charge).

So *assuming* the single-polynomial crux — for `Φ = Phi R M`, if every `D_m` (`m ≥ 1`) vanishes then
the small-root packet product is `c·t` (`hS`) — the sharpened orbit-product contradiction
`GMC2Thm2067HSonly.thm2067_reduced_to_hS` closes, giving `DvdK1BothSigns`.  Every step except that one
crux (the Weierstrass small-root identity, `= h(0,t) = 1`, the analytic lane) is
discharged here kernel-pure.
-/

open Polynomial GMC2LaurentShiftCheckA

namespace GMC2DvdKUnivariateReduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The single-polynomial crux (`= the small-root product identity = h(0,t) = 1`).**  For `Φ = Phi R M = Xᴹ − t·R` with
`1 ≤ M < deg R` and `R(0) ≠ 0`, if every central power coefficient `Dₘ = (Rᵐ).coeff (M·m)` (`m ≥ 1`)
vanishes, then the small-root packet product is `c·t` for some `c ≠ 0`.  This is the sole deep analytic
input — the Weierstrass small-root/log-derivative identity, the analytic lane. -/
def SinglePolyCrux : Prop :=
  ∀ (R : Polynomial ℂ) (M : ℕ), 1 ≤ M → M < R.natDegree → R.coeff 0 ≠ 0 →
      (∀ m : ℕ, 1 ≤ m → (R ^ m).coeff (M * m) = 0) →
      ∃ (S : Finset ((GMC2PhiVieta.Phi R M).rootSet (GMC2PhiVieta.Phi R M).SplittingField))
        (_x0 : (GMC2PhiVieta.Phi R M).rootSet (GMC2PhiVieta.Phi R M).SplittingField)
        (cc : ℂ), cc ≠ 0 ∧
        (∏ β ∈ S, (β : (GMC2PhiVieta.Phi R M).SplittingField))
          = algebraMap (RatFunc ℂ) (GMC2PhiVieta.Phi R M).SplittingField
              (RatFunc.C cc * RatFunc.X)

omit [DecidableEq ι] in
/-- **Coefficient of the shifted polynomial at an achieved shifted exponent.**  If `q` is injective
and every charge satisfies `-(M:ℤ) ≤ q i`, then the coefficient of `shiftedPolynomial q c M` at the
exponent `(q iv + M).toNat` is exactly `c iv`: every *other* charge produces a different shifted
exponent, because the shift is nonnegative on the whole support and `q` is injective. -/
theorem coeff_shiftedPolynomial_achiever
    (q : ι → ℤ) (c : ι → ℂ) (M : ℕ) (hq : Function.Injective q)
    (hMlb : ∀ i, -(M : ℤ) ≤ q i) (iv : ι) :
    (shiftedPolynomial q c M).coeff (q iv + (M : ℤ)).toNat = c iv := by
  classical
  unfold shiftedPolynomial
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single iv]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro i _ hiv
    have hne : ¬ ((q i + (M : ℤ)).toNat = (q iv + (M : ℤ)).toNat) := by
      intro hcontra
      apply hiv
      apply hq
      have hi_nn : 0 ≤ q i + (M : ℤ) := by have := hMlb i; omega
      have hiv_nn : 0 ≤ q iv + (M : ℤ) := by have := hMlb iv; omega
      have e1 := Int.toNat_of_nonneg hi_nn
      have e2 := Int.toNat_of_nonneg hiv_nn
      have hcast : ((q i + (M : ℤ)).toNat : ℤ) = ((q iv + (M : ℤ)).toNat : ℤ) := by
        exact_mod_cast hcontra
      omega
    rw [Polynomial.coeff_monomial, if_neg hne]
  · intro h; exact absurd (Finset.mem_univ iv) h

/-- **The univariate reduction.**  Given the single-polynomial crux (for `Φ = Phi R M`, the vanishing
of every central power coefficient `Dₘ = (Rᵐ).coeff (M·m)`, `m ≥ 1`, produces a small-root packet whose
product is `c·t`), the one-variable Duistermaat–van der Kallen input holds on every both-signs support.

The proof: negate the conclusion (so *all* `aeval c (constantTermRelation q m) = 0`, `m ≥ 1`), build
`R = shiftedPolynomial q c M` with `M = −min_i q_i`, verify `1 ≤ M`, `M < R.natDegree`, `R.coeff 0 ≠ 0`
(from the unique minimal/maximal charges and injectivity), pass the vanishing through Check A to feed
the crux, and close with `thm2067_reduced_to_hS`. -/
theorem dvdK1_bothSigns_of_crux (crux : SinglePolyCrux) :
    GMC2DvdKZeroCharge.DvdK1BothSigns := by
  classical
  intro ι _ _ q c hq hc hneg hpos
  by_contra hcon
  -- the negation says every positive-power constant term vanishes
  have hcon' : ∀ m : ℕ, 1 ≤ m →
      MvPolynomial.aeval c (GMC2ConstantTermRelations.constantTermRelation q m) = 0 := by
    intro m hm
    by_contra hmne
    exact hcon ⟨m, hm, hmne⟩
  obtain ⟨inl, hinl⟩ := hneg
  obtain ⟨jpo, hjpo⟩ := hpos
  have huniv : (Finset.univ : Finset ι).Nonempty := ⟨inl, Finset.mem_univ inl⟩
  -- the (unique) minimal and maximal charges
  obtain ⟨i0, -, hi0min⟩ := Finset.exists_min_image Finset.univ q huniv
  obtain ⟨jm, -, hjmax⟩ := Finset.exists_max_image Finset.univ q huniv
  have hi0neg : q i0 < 0 := lt_of_le_of_lt (hi0min inl (Finset.mem_univ inl)) hinl
  have hjmpos : 0 < q jm := lt_of_lt_of_le hjpo (hjmax jpo (Finset.mem_univ jpo))
  -- the canonical upward shift `M = −min q`
  set M : ℕ := (-q i0).toNat with hMdef
  have hMI : (M : ℤ) = -q i0 := Int.toNat_of_nonneg (by omega)
  have hM1 : 1 ≤ M := by omega
  have hMlb : ∀ i, -(M : ℤ) ≤ q i := by
    intro i; have := hi0min i (Finset.mem_univ i); omega
  -- `R.coeff 0 = c i0 ≠ 0`
  have hexp0 : (q i0 + (M : ℤ)).toNat = 0 := by rw [hMI]; simp
  have hR0 : (shiftedPolynomial q c M).coeff 0 ≠ 0 := by
    have h := coeff_shiftedPolynomial_achiever q c M hq hMlb i0
    rw [hexp0] at h
    rw [h]; exact hc i0
  -- `M < R.natDegree` via the maximal charge's coefficient
  have hcjm := coeff_shiftedPolynomial_achiever q c M hq hMlb jm
  have hle : (q jm + (M : ℤ)).toNat ≤ (shiftedPolynomial q c M).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcjm]; exact hc jm)
  have hMlt : M < (q jm + (M : ℤ)).toNat := by
    have hnn : 0 ≤ q jm + (M : ℤ) := by omega
    have := Int.toNat_of_nonneg hnn
    omega
  have hMd : M < (shiftedPolynomial q c M).natDegree := lt_of_lt_of_le hMlt hle
  -- Check A: the vanishing constant terms are the central power coefficients of `R`
  have hDvanish : ∀ m : ℕ, 1 ≤ m → ((shiftedPolynomial q c M) ^ m).coeff (M * m) = 0 := by
    intro m hm
    rw [coeff_shiftedPolynomial_pow_eq_aeval_constantTermRelation q c M m hMlb]
    exact hcon' m hm
  -- feed the crux, then close with the sharpened orbit-product contradiction
  obtain ⟨S, x0, cc, hcc, hS⟩ := crux (shiftedPolynomial q c M) M hM1 hMd hR0 hDvanish
  exact GMC2Thm2067HSonly.thm2067_reduced_to_hS (shiftedPolynomial q c M) M hM1 hMd hR0 S x0 cc hcc hS

/-- **`DvdK1` from the single-polynomial crux.**  Assembling the univariate reduction with the
zero-charge disjunct (`GMC2DvdKZeroCharge.dvdK1_of_bothSigns`): the full published one-variable
Duistermaat–van der Kallen input holds. -/
theorem dvdK1_of_crux (crux : SinglePolyCrux) : GMC2DvdKInterface.DvdK1 :=
  GMC2DvdKZeroCharge.dvdK1_of_bothSigns (dvdK1_bothSigns_of_crux crux)

/-- **NC2 from the single-polynomial crux.**  Composing with `GMC2NC2.nc2_of_dvdK1` (the height
witness is already discharged unconditionally): the two-variable nullcone non-transitivity theorem
holds modulo exactly the one small-root identity. -/
theorem nc2_of_crux (crux : SinglePolyCrux) : GMC2.NC2 :=
  GMC2NC2.nc2_of_dvdK1 (dvdK1_of_crux crux)

/-- **GMC(2) from the single-polynomial crux — the capstone.**  Composing with `GMC2NC2.gmc2_of_dvdK1`:
the full GMC(2) two-variable nullcone conclusion — for `P, Q` over `ℂ[x,y]` with `E(Pᵐ) = 0` for all
`m ≥ 1`, eventually `E(Q·Pᵐ) = 0` — holds modulo **exactly** the single deep analytic input
`SinglePolyCrux` (`= h(0,t) = 1`).  Every other step is kernel-pure. -/
theorem gmc2_of_crux (crux : SinglePolyCrux)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, GMC2.E (Q * P ^ m) = 0 :=
  GMC2NC2.gmc2_of_dvdK1 (dvdK1_of_crux crux) P Q hnull

end GMC2DvdKUnivariateReduction

