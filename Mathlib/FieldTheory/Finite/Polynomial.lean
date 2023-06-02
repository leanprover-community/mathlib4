/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module field_theory.finite.polynomial
! leanprover-community/mathlib commit 5aa3c1de9f3c642eac76e11071c852766f220fd0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Basic
import Mathbin.RingTheory.MvPolynomial.Basic
import Mathbin.Data.MvPolynomial.Expand
import Mathbin.FieldTheory.Finite.Basic

/-!
## Polynomials over finite fields
-/


namespace MvPolynomial

variable {σ : Type _}

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `zmod n`. -/
theorem c_dvd_iff_zMod (n : ℕ) (φ : MvPolynomial σ ℤ) :
    C (n : ℤ) ∣ φ ↔ map (Int.castRingHom (ZMod n)) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (CharP.int_cast_eq_zero_iff (ZMod n) n) _
#align mv_polynomial.C_dvd_iff_zmod MvPolynomial.c_dvd_iff_zMod

section frobenius

variable {p : ℕ} [Fact p.Prime]

theorem frobenius_zMod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p f :=
  by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [AlgHom.map_add, RingHom.map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, RingHom.map_mul, AlgHom.map_mul]
    intro _ _ hf; rw [hf, frobenius_def]
#align mv_polynomial.frobenius_zmod MvPolynomial.frobenius_zMod

theorem expand_zMod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p :=
  (frobenius_zMod _).symm
#align mv_polynomial.expand_zmod MvPolynomial.expand_zMod

end frobenius

end MvPolynomial

namespace MvPolynomial

noncomputable section

open scoped BigOperators Classical

open Set LinearMap Submodule

variable {K : Type _} {σ : Type _}

section Indicator

variable [Fintype K] [Fintype σ]

/-- Over a field, this is the indicator function as an `mv_polynomial`. -/
def indicator [CommRing K] (a : σ → K) : MvPolynomial σ K :=
  ∏ n, 1 - (X n - C (a n)) ^ (Fintype.card K - 1)
#align mv_polynomial.indicator MvPolynomial.indicator

section CommRing

variable [CommRing K]

theorem eval_indicator_apply_eq_one (a : σ → K) : eval a (indicator a) = 1 :=
  by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this, sub_zero, Finset.prod_const_one]
#align mv_polynomial.eval_indicator_apply_eq_one MvPolynomial.eval_indicator_apply_eq_one

theorem degrees_indicator (c : σ → K) :
    degrees (indicator c) ≤ ∑ s : σ, (Fintype.card K - 1) • {s} :=
  by
  rw [indicator]
  refine' le_trans (degrees_prod _ _) (Finset.sum_le_sum fun s hs => _)
  refine' le_trans (degrees_sub _ _) _
  rw [degrees_one, ← bot_eq_zero, bot_sup_eq]
  refine' le_trans (degrees_pow _ _) (nsmul_le_nsmul_of_le_right _ _)
  refine' le_trans (degrees_sub _ _) _
  rw [degrees_C, ← bot_eq_zero, sup_bot_eq]
  exact degrees_X' _
#align mv_polynomial.degrees_indicator MvPolynomial.degrees_indicator

theorem indicator_mem_restrictDegree (c : σ → K) :
    indicator c ∈ restrictDegree σ K (Fintype.card K - 1) :=
  by
  rw [mem_restrict_degree_iff_sup, indicator]
  intro n
  refine' le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq _)
  simp_rw [← Multiset.coe_countAddMonoidHom, (Multiset.countAddMonoidHom n).map_sum,
    AddMonoidHom.map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  refine' Finset.sum_eq_single n _ _
  · intro b hb ne; rw [Multiset.count_singleton, if_neg Ne.symm, MulZeroClass.mul_zero]
  · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]
#align mv_polynomial.indicator_mem_restrict_degree MvPolynomial.indicator_mem_restrictDegree

end CommRing

variable [Field K]

theorem eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) : eval a (indicator b) = 0 :=
  by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by rwa [(· ≠ ·), Function.funext_iff, not_forall] at h 
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    Finset.prod_eq_zero_iff]
  refine' ⟨i, Finset.mem_univ _, _⟩
  rw [FiniteField.pow_card_sub_one_eq_one, sub_self]
  rwa [(· ≠ ·), sub_eq_zero]
#align mv_polynomial.eval_indicator_apply_eq_zero MvPolynomial.eval_indicator_apply_eq_zero

end Indicator

section

variable (K σ)

/-- `mv_polynomial.eval` as a `K`-linear map. -/
@[simps]
def evalₗ [CommSemiring K] : MvPolynomial σ K →ₗ[K] (σ → K) → K
    where
  toFun p e := eval e p
  map_add' p q := by ext x; rw [RingHom.map_add]; rfl
  map_smul' a p := by ext e; rw [smul_eq_C_mul, RingHom.map_mul, eval_C]; rfl
#align mv_polynomial.evalₗ MvPolynomial.evalₗ

end

variable [Field K] [Fintype K] [Finite σ]

theorem map_restrict_dom_evalₗ : (restrictDegree σ K (Fintype.card K - 1)).map (evalₗ K σ) = ⊤ :=
  by
  cases nonempty_fintype σ
  refine' top_unique (SetLike.le_def.2 fun e _ => mem_map.2 _)
  refine' ⟨∑ n : σ → K, e n • indicator n, _, _⟩
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrict_degree _)
  · ext n
    simp only [LinearMap.map_sum, @Finset.sum_apply (σ → K) (fun _ => K) _ _ _ _ _, Pi.smul_apply,
      LinearMap.map_smul]
    simp only [evalₗ_apply]
    trans
    refine' Finset.sum_eq_single n (fun b _ h => _) _
    · rw [eval_indicator_apply_eq_zero _ _ h.symm, smul_zero]
    · exact fun h => (h <| Finset.mem_univ n).elim
    · rw [eval_indicator_apply_eq_one, smul_eq_mul, mul_one]
#align mv_polynomial.map_restrict_dom_evalₗ MvPolynomial.map_restrict_dom_evalₗ

end MvPolynomial

namespace MvPolynomial

open scoped Classical Cardinal

open LinearMap Submodule

universe u

variable (σ : Type u) (K : Type u) [Fintype K]

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] K -/
/-- The submodule of multivariate polynomials whose degree of each variable is strictly less
than the cardinality of K. -/
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)
deriving AddCommGroup,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] K»,
  Inhabited
#align mv_polynomial.R MvPolynomial.R

/-- Evaluation in the `mv_polynomial.R` subtype. -/
def evalᵢ [CommRing K] : R σ K →ₗ[K] (σ → K) → K :=
  (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).Subtype
#align mv_polynomial.evalᵢ MvPolynomial.evalᵢ

section CommRing

variable [CommRing K]

noncomputable instance decidableRestrictDegree (m : ℕ) :
    DecidablePred (· ∈ { n : σ →₀ ℕ | ∀ i, n i ≤ m }) := by
  simp only [Set.mem_setOf_eq] <;> infer_instance
#align mv_polynomial.decidable_restrict_degree MvPolynomial.decidableRestrictDegree

end CommRing

variable [Field K]

theorem rank_r [Fintype σ] : Module.rank K (R σ K) = Fintype.card (σ → K) :=
  calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 } →₀ K) :=
      LinearEquiv.rank_eq
        (Finsupp.supportedEquivFinsupp { s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 })
    _ = (#{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 }) := by rw [rank_finsupp_self']
    _ = (#{ s : σ → ℕ | ∀ n : σ, s n < Fintype.card K }) :=
      by
      refine' Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => _⟩
      refine' forall_congr' fun n => le_tsub_iff_right _
      exact Fintype.card_pos_iff.2 ⟨0⟩
    _ = (#σ → { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => ℕ) fun s n => n < Fintype.card K).cardinal_eq
    _ = (#σ → Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = (#σ → K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ → K) := Cardinal.mk_fintype _
    
#align mv_polynomial.rank_R MvPolynomial.rank_r

instance [Finite σ] : FiniteDimensional K (R σ K) :=
  by
  cases nonempty_fintype σ
  exact
    IsNoetherian.iff_fg.1
      (is_noetherian.iff_rank_lt_aleph_0.mpr <| by
        simpa only [rank_R] using Cardinal.nat_lt_aleph0 (Fintype.card (σ → K)))

theorem finrank_r [Fintype σ] : FiniteDimensional.finrank K (R σ K) = Fintype.card (σ → K) :=
  FiniteDimensional.finrank_eq_of_rank_eq (rank_r σ K)
#align mv_polynomial.finrank_R MvPolynomial.finrank_r

theorem range_evalᵢ [Finite σ] : (evalᵢ σ K).range = ⊤ :=
  by
  rw [evalᵢ, LinearMap.range_comp, range_subtype]
  exact map_restrict_dom_evalₗ
#align mv_polynomial.range_evalᵢ MvPolynomial.range_evalᵢ

theorem ker_evalₗ [Finite σ] : (evalᵢ σ K).ker = ⊥ :=
  by
  cases nonempty_fintype σ
  refine' (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank _).mpr (range_evalᵢ _ _)
  rw [FiniteDimensional.finrank_fintype_fun_eq_card, finrank_R]
#align mv_polynomial.ker_evalₗ MvPolynomial.ker_evalₗ

theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : ∀ v : σ → K, eval v p = 0)
    (hp : p ∈ restrictDegree σ K (Fintype.card K - 1)) : p = 0 :=
  let p' : R σ K := ⟨p, hp⟩
  have : p' ∈ (evalᵢ σ K).ker := funext h
  show p'.1 = (0 : R σ K).1 from congr_arg _ <| by rwa [ker_evalₗ, mem_bot] at this 
#align mv_polynomial.eq_zero_of_eval_eq_zero MvPolynomial.eq_zero_of_eval_eq_zero

end MvPolynomial

