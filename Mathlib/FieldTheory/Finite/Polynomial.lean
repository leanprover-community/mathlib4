/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.Expand
import Mathlib.FieldTheory.Finite.Basic

#align_import field_theory.finite.polynomial from "leanprover-community/mathlib"@"5aa3c1de9f3c642eac76e11071c852766f220fd0"

/-!
## Polynomials over finite fields
-/


namespace MvPolynomial

variable {σ : Type*}

/-- A polynomial over the integers is divisible by `n : ℕ`
if and only if it is zero over `ZMod n`. -/
theorem C_dvd_iff_zmod (n : ℕ) (φ : MvPolynomial σ ℤ) :
    C (n : ℤ) ∣ φ ↔ map (Int.castRingHom (ZMod n)) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (CharP.int_cast_eq_zero_iff (ZMod n) n) _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.C_dvd_iff_zmod MvPolynomial.C_dvd_iff_zmod

section frobenius

variable {p : ℕ} [Fact p.Prime]

theorem frobenius_zmod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p f := by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
    -- ⊢ ↑(frobenius (MvPolynomial σ (ZMod p)) p) (↑C a) = ↑(expand p) (↑C a)
             -- 🎉 no goals
  · simp only [AlgHom.map_add, RingHom.map_add]; intro _ _ hf hg; rw [hf, hg]
    -- ⊢ ∀ (p_1 q : MvPolynomial σ (ZMod p)), ↑(frobenius (MvPolynomial σ (ZMod p)) p …
                                                 -- ⊢ ↑(frobenius (MvPolynomial σ (ZMod p)) p) p✝ + ↑(frobenius (MvPolynomial σ (Z …
                                                                  -- 🎉 no goals
  · simp only [expand_X, RingHom.map_mul, AlgHom.map_mul]
    -- ⊢ ∀ (p_1 : MvPolynomial σ (ZMod p)) (n : σ), ↑(frobenius (MvPolynomial σ (ZMod …
    intro _ _ hf; rw [hf, frobenius_def]
    -- ⊢ ↑(frobenius (MvPolynomial σ (ZMod p)) p) p✝ * ↑(frobenius (MvPolynomial σ (Z …
                  -- 🎉 no goals
#align mv_polynomial.frobenius_zmod MvPolynomial.frobenius_zmod

theorem expand_zmod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p :=
  (frobenius_zmod _).symm
#align mv_polynomial.expand_zmod MvPolynomial.expand_zmod

end frobenius

end MvPolynomial

namespace MvPolynomial

noncomputable section

open scoped BigOperators Classical

open Set LinearMap Submodule

variable {K : Type*} {σ : Type*}

section Indicator

variable [Fintype K] [Fintype σ]

/-- Over a field, this is the indicator function as an `MvPolynomial`. -/
def indicator [CommRing K] (a : σ → K) : MvPolynomial σ K :=
  ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))
#align mv_polynomial.indicator MvPolynomial.indicator

section CommRing

variable [CommRing K]

theorem eval_indicator_apply_eq_one (a : σ → K) : eval a (indicator a) = 1 := by
  nontriviality
  -- ⊢ ↑(eval a) (indicator a) = 1
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  -- ⊢ ↑(eval a) (indicator a) = 1
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this, sub_zero, Finset.prod_const_one]
#align mv_polynomial.eval_indicator_apply_eq_one MvPolynomial.eval_indicator_apply_eq_one

theorem degrees_indicator (c : σ → K) :
    degrees (indicator c) ≤ ∑ s : σ, (Fintype.card K - 1) • {s} := by
  rw [indicator]
  -- ⊢ degrees (∏ n : σ, (1 - (X n - ↑C (c n)) ^ (Fintype.card K - 1))) ≤ ∑ s : σ,  …
  refine' le_trans (degrees_prod _ _) (Finset.sum_le_sum fun s _ => _)
  -- ⊢ degrees (1 - (X s - ↑C (c s)) ^ (Fintype.card K - 1)) ≤ (Fintype.card K - 1) …
  refine' le_trans (degrees_sub _ _) _
  -- ⊢ degrees 1 ⊔ degrees ((X s - ↑C (c s)) ^ (Fintype.card K - 1)) ≤ (Fintype.car …
  rw [degrees_one, ← bot_eq_zero, bot_sup_eq]
  -- ⊢ degrees ((X s - ↑C (c s)) ^ (Fintype.card K - 1)) ≤ (Fintype.card K - 1) • {s}
  refine' le_trans (degrees_pow _ _) (nsmul_le_nsmul_of_le_right _ _)
  -- ⊢ degrees (X s - ↑C (c s)) ≤ {s}
  refine' le_trans (degrees_sub _ _) _
  -- ⊢ degrees (X s) ⊔ degrees (↑C (c s)) ≤ {s}
  rw [degrees_C, ← bot_eq_zero, sup_bot_eq]
  -- ⊢ degrees (X s) ≤ {s}
  exact degrees_X' _
  -- 🎉 no goals
#align mv_polynomial.degrees_indicator MvPolynomial.degrees_indicator

theorem indicator_mem_restrictDegree (c : σ → K) :
    indicator c ∈ restrictDegree σ K (Fintype.card K - 1) := by
  rw [mem_restrictDegree_iff_sup, indicator]
  -- ⊢ ∀ (i : σ), Multiset.count i (degrees (∏ n : σ, (1 - (X n - ↑C (c n)) ^ (Fint …
  intro n
  -- ⊢ Multiset.count n (degrees (∏ n : σ, (1 - (X n - ↑C (c n)) ^ (Fintype.card K  …
  refine' le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq _)
  -- ⊢ Multiset.count n (∑ s : σ, (Fintype.card K - 1) • {s}) = Fintype.card K - 1
  simp_rw [← Multiset.coe_countAddMonoidHom, (Multiset.countAddMonoidHom n).map_sum,
    AddMonoidHom.map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  refine' Finset.sum_eq_single n _ _
  · intro b _ ne
    -- ⊢ (Fintype.card K - 1) * Multiset.count n {b} = 0
    simp [Multiset.count_singleton, ne, if_neg (Ne.symm _)]
    -- 🎉 no goals
  · intro h; exact (h <| Finset.mem_univ _).elim
    -- ⊢ (Fintype.card K - 1) * Multiset.count n {n} = 0
             -- 🎉 no goals
  · rw [Multiset.count_singleton_self, mul_one]
    -- 🎉 no goals
#align mv_polynomial.indicator_mem_restrict_degree MvPolynomial.indicator_mem_restrictDegree

end CommRing

variable [Field K]

theorem eval_indicator_apply_eq_zero (a b : σ → K) (h : a ≠ b) : eval a (indicator b) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by rwa [Ne, Function.funext_iff, not_forall] at h
  -- ⊢ ↑(eval a) (indicator b) = 0
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    Finset.prod_eq_zero_iff]
  refine' ⟨i, Finset.mem_univ _, _⟩
  -- ⊢ 1 - (a i - b i) ^ (Fintype.card K - 1) = 0
  rw [FiniteField.pow_card_sub_one_eq_one, sub_self]
  -- ⊢ a i - b i ≠ 0
  rwa [Ne, sub_eq_zero]
  -- 🎉 no goals
#align mv_polynomial.eval_indicator_apply_eq_zero MvPolynomial.eval_indicator_apply_eq_zero

end Indicator

section

variable (K σ)

/-- `MvPolynomial.eval` as a `K`-linear map. -/
@[simps]
def evalₗ [CommSemiring K] : MvPolynomial σ K →ₗ[K] (σ → K) → K where
  toFun p e := eval e p
  map_add' p q := by ext x; simp
                     -- ⊢ (fun p e => ↑(eval e) p) (p + q) x = ((fun p e => ↑(eval e) p) p + (fun p e  …
                            -- 🎉 no goals
  map_smul' a p := by ext e; simp
                      -- ⊢ AddHom.toFun { toFun := fun p e => ↑(eval e) p, map_add' := (_ : ∀ (p q : Mv …
                             -- 🎉 no goals
#align mv_polynomial.evalₗ MvPolynomial.evalₗ

variable [Field K] [Fintype K] [Finite σ]

-- Porting note: `K` and `σ` were implicit in mathlib3, even if they were declared via
-- `variables (K σ)` (I don't understand why). They are now explicit, as expected.
theorem map_restrict_dom_evalₗ : (restrictDegree σ K (Fintype.card K - 1)).map (evalₗ K σ) = ⊤ := by
  cases nonempty_fintype σ
  -- ⊢ Submodule.map (evalₗ K σ) (restrictDegree σ K (Fintype.card K - 1)) = ⊤
  refine' top_unique (SetLike.le_def.2 fun e _ => mem_map.2 _)
  -- ⊢ ∃ y, y ∈ restrictDegree σ K (Fintype.card K - 1) ∧ ↑(evalₗ K σ) y = e
  refine' ⟨∑ n : σ → K, e n • indicator n, _, _⟩
  -- ⊢ ∑ n : σ → K, e n • indicator n ∈ restrictDegree σ K (Fintype.card K - 1)
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrictDegree _)
    -- 🎉 no goals
  · ext n
    -- ⊢ ↑(evalₗ K σ) (∑ n : σ → K, e n • indicator n) n = e n
    simp only [LinearMap.map_sum, @Finset.sum_apply (σ → K) (fun _ => K) _ _ _ _ _, Pi.smul_apply,
      LinearMap.map_smul]
    simp only [evalₗ_apply]
    -- ⊢ ∑ x : σ → K, e x • ↑(eval n) (indicator x) = e n
    trans
    refine' Finset.sum_eq_single n (fun b _ h => _) _
    · rw [eval_indicator_apply_eq_zero _ _ h.symm, smul_zero]
      -- 🎉 no goals
    · exact fun h => (h <| Finset.mem_univ n).elim
      -- 🎉 no goals
    · rw [eval_indicator_apply_eq_one, smul_eq_mul, mul_one]
      -- 🎉 no goals
#align mv_polynomial.map_restrict_dom_evalₗ MvPolynomial.map_restrict_dom_evalₗ

end

end

end MvPolynomial

namespace MvPolynomial

open scoped Classical Cardinal

open LinearMap Submodule

universe u

variable (σ : Type u) (K : Type u) [Fintype K]

--Porting note: `@[derive [add_comm_group, module K, inhabited]]` done by hand.
/-- The submodule of multivariate polynomials whose degree of each variable is strictly less
than the cardinality of K. -/
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.R MvPolynomial.R

noncomputable instance [CommRing K] : AddCommGroup (R σ K) :=
  inferInstanceAs (AddCommGroup (restrictDegree σ K (Fintype.card K - 1)))

noncomputable instance [CommRing K] : Module K (R σ K) :=
  inferInstanceAs (Module K (restrictDegree σ K (Fintype.card K - 1)))

noncomputable instance [CommRing K] : Inhabited (R σ K) :=
  inferInstanceAs (Inhabited (restrictDegree σ K (Fintype.card K - 1)))

/-- Evaluation in the `mv_polynomial.R` subtype. -/
def evalᵢ [CommRing K] : R σ K →ₗ[K] (σ → K) → K :=
  (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype
#align mv_polynomial.evalᵢ MvPolynomial.evalᵢ

section CommRing

variable [CommRing K]

noncomputable instance decidableRestrictDegree (m : ℕ) :
    DecidablePred (· ∈ { n : σ →₀ ℕ | ∀ i, n i ≤ m }) := by
  simp only [Set.mem_setOf_eq]; infer_instance
  -- ⊢ DecidablePred fun n => ∀ (i : σ), ↑n i ≤ m
                                -- 🎉 no goals
#align mv_polynomial.decidable_restrict_degree MvPolynomial.decidableRestrictDegree

end CommRing

variable [Field K]

theorem rank_R [Fintype σ] : Module.rank K (R σ K) = Fintype.card (σ → K) :=
  calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 } →₀ K) :=
      LinearEquiv.rank_eq
        (Finsupp.supportedEquivFinsupp { s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 })
    _ = #{ s : σ →₀ ℕ | ∀ n : σ, s n ≤ Fintype.card K - 1 } := by rw [rank_finsupp_self']
                                                                  -- 🎉 no goals
    _ = #{ s : σ → ℕ | ∀ n : σ, s n < Fintype.card K } := by
      refine' Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => _⟩
      -- ⊢ f ∈ {s | ∀ (n : σ), ↑s n ≤ Fintype.card K - 1} ↔ ↑Finsupp.equivFunOnFinite f …
      refine' forall_congr' fun n => le_tsub_iff_right _
      -- ⊢ 1 ≤ Fintype.card K
      exact Fintype.card_pos_iff.2 ⟨0⟩
      -- 🎉 no goals
    _ = #(σ → { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => ℕ) fun s n => n < Fintype.card K).cardinal_eq
    _ = #(σ → Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = #(σ → K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ → K) := Cardinal.mk_fintype _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.rank_R MvPolynomial.rank_R

instance [Finite σ] : FiniteDimensional K (R σ K) := by
  cases nonempty_fintype σ
  -- ⊢ FiniteDimensional K (R σ K)
  exact
    IsNoetherian.iff_fg.1
      (IsNoetherian.iff_rank_lt_aleph0.mpr <| by
        simpa only [rank_R] using Cardinal.nat_lt_aleph0 (Fintype.card (σ → K)))

theorem finrank_R [Fintype σ] : FiniteDimensional.finrank K (R σ K) = Fintype.card (σ → K) :=
  FiniteDimensional.finrank_eq_of_rank_eq (rank_R σ K)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.finrank_R MvPolynomial.finrank_R

-- Porting note: was `(evalᵢ σ K).range`.
theorem range_evalᵢ [Finite σ] : range (evalᵢ σ K) = ⊤ := by
  rw [evalᵢ, LinearMap.range_comp, range_subtype]
  -- ⊢ Submodule.map (evalₗ K σ) (restrictDegree σ K (Fintype.card K - 1)) = ⊤
  exact map_restrict_dom_evalₗ K σ
  -- 🎉 no goals
#align mv_polynomial.range_evalᵢ MvPolynomial.range_evalᵢ

--Porting note: was `(evalᵢ σ K).ker`.
theorem ker_evalₗ [Finite σ] : ker (evalᵢ σ K) = ⊥ := by
  cases nonempty_fintype σ
  -- ⊢ ker (evalᵢ σ K) = ⊥
  refine' (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank _).mpr (range_evalᵢ σ K)
  -- ⊢ FiniteDimensional.finrank K (R σ K) = FiniteDimensional.finrank K ((σ → K) → …
  rw [FiniteDimensional.finrank_fintype_fun_eq_card, finrank_R]
  -- 🎉 no goals
#align mv_polynomial.ker_evalₗ MvPolynomial.ker_evalₗ

theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : ∀ v : σ → K, eval v p = 0)
    (hp : p ∈ restrictDegree σ K (Fintype.card K - 1)) : p = 0 :=
  let p' : R σ K := ⟨p, hp⟩
  have : p' ∈ ker (evalᵢ σ K) := funext h
  show p'.1 = (0 : R σ K).1 from congr_arg _ <| by rwa [ker_evalₗ, mem_bot] at this
                                                   -- 🎉 no goals
#align mv_polynomial.eq_zero_of_eval_eq_zero MvPolynomial.eq_zero_of_eval_eq_zero

end MvPolynomial
