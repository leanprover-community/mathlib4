/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.polynomial.basic from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Ring-theoretic supplement of Data.Polynomial.

## Main results
* `MvPolynomial.isDomain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `Polynomial.isNoetherianRing`:
  Hilbert basis theorem, that if a ring is noetherian then so is its polynomial ring.
* `Polynomial.wfDvdMonoid`:
  If an integral domain is a `WFDvdMonoid`, then so is its polynomial ring.
* `Polynomial.uniqueFactorizationMonoid`, `MvPolynomial.uniqueFactorizationMonoid`:
  If an integral domain is a `UniqueFactorizationMonoid`, then so is its polynomial ring (of any
  number of variables).
-/

noncomputable section

open Classical BigOperators Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

instance (p : ℕ) [h : CharP R p] : CharP R[X] p :=
  let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩
               -- 🎉 no goals

variable (R)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)
#align polynomial.degree_le Polynomial.degreeLE

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degreeLT (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R k)
#align polynomial.degree_lt Polynomial.degreeLT

variable {R}

theorem mem_degreeLE {n : WithBot ℕ} {f : R[X]} : f ∈ degreeLE R n ↔ degree f ≤ n := by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl
  -- ⊢ (∀ (i : ℕ), ↑i > n → ↑(lcoeff R i) f = 0) ↔ ∀ (m : ℕ), n < ↑m → coeff f m = 0
                                                                                         -- 🎉 no goals
#align polynomial.mem_degree_le Polynomial.mem_degreeLE

@[mono]
theorem degreeLE_mono {m n : WithBot ℕ} (H : m ≤ n) : degreeLE R m ≤ degreeLE R n := fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)
#align polynomial.degree_le_mono Polynomial.degreeLE_mono

theorem degreeLE_eq_span_X_pow {n : ℕ} :
    degreeLE R n = Submodule.span R ↑((Finset.range (n + 1)).image fun n => (X : R[X]) ^ n) := by
  apply le_antisymm
  -- ⊢ degreeLE R ↑n ≤ Submodule.span R ↑(image (fun n => X ^ n) (range (n + 1)))
  · intro p hp
    -- ⊢ p ∈ Submodule.span R ↑(image (fun n => X ^ n) (range (n + 1)))
    replace hp := mem_degreeLE.1 hp
    -- ⊢ p ∈ Submodule.span R ↑(image (fun n => X ^ n) (range (n + 1)))
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    -- ⊢ ∑ n in support p, ↑(monomial n) (coeff p n) ∈ Submodule.span R ↑(image (fun  …
    refine' Submodule.sum_mem _ fun k hk => _
    -- ⊢ ↑(monomial k) (coeff p k) ∈ Submodule.span R ↑(image (fun n => X ^ n) (range …
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    -- ⊢ ↑(monomial k) (coeff p k) ∈ Submodule.span R ↑(image (fun n => X ^ n) (range …
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    -- ⊢ coeff p k • X ^ k ∈ Submodule.span R ↑(image (fun n => X ^ n) (range (n + 1)))
    refine'
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <|
            Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le this), rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  -- ⊢ ↑(range (n + 1)) ⊆ (fun n => X ^ n) ⁻¹' ↑(degreeLE R ↑n)
  intro k hk
  -- ⊢ k ∈ (fun n => X ^ n) ⁻¹' ↑(degreeLE R ↑n)
  apply mem_degreeLE.2
  -- ⊢ degree ((fun n => X ^ n) k) ≤ ↑n
  exact
    (degree_X_pow_le _).trans (WithBot.coe_le_coe.2 <| Nat.le_of_lt_succ <| Finset.mem_range.1 hk)
set_option linter.uppercaseLean3 false in
#align polynomial.degree_le_eq_span_X_pow Polynomial.degreeLE_eq_span_X_pow

theorem mem_degreeLT {n : ℕ} {f : R[X]} : f ∈ degreeLT R n ↔ degree f < n := by
  rw [degreeLT, Submodule.mem_iInf]
  -- ⊢ (∀ (i : ℕ), f ∈ ⨅ (_ : i ≥ n), LinearMap.ker (lcoeff R i)) ↔ degree f < ↑n
  conv_lhs => intro i; rw [Submodule.mem_iInf]
  -- ⊢ (∀ (i : ℕ), i ≥ n → f ∈ LinearMap.ker (lcoeff R i)) ↔ degree f < ↑n
  rw [degree, Finset.max_eq_sup_coe]
  -- ⊢ (∀ (i : ℕ), i ≥ n → f ∈ LinearMap.ker (lcoeff R i)) ↔ sup (support f) WithBo …
  rw [Finset.sup_lt_iff ?_]
  -- ⊢ (∀ (i : ℕ), i ≥ n → f ∈ LinearMap.ker (lcoeff R i)) ↔ ∀ (b : ℕ), b ∈ support …
  rotate_left
  -- ⊢ ⊥ < ↑n
  apply WithBot.bot_lt_coe
  -- ⊢ (∀ (i : ℕ), i ≥ n → f ∈ LinearMap.ker (lcoeff R i)) ↔ ∀ (b : ℕ), b ∈ support …
  conv_rhs =>
    simp only [mem_support_iff]
    intro b
    rw [Nat.cast_withBot, WithBot.coe_lt_coe, lt_iff_not_le, Ne, not_imp_not]
#align polynomial.mem_degree_lt Polynomial.mem_degreeLT

@[mono]
theorem degreeLT_mono {m n : ℕ} (H : m ≤ n) : degreeLT R m ≤ degreeLT R n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)
#align polynomial.degree_lt_mono Polynomial.degreeLT_mono

theorem degreeLT_eq_span_X_pow {n : ℕ} :
    degreeLT R n = Submodule.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X]) := by
  apply le_antisymm
  -- ⊢ degreeLT R n ≤ Submodule.span R ↑(image (fun n => X ^ n) (range n))
  · intro p hp
    -- ⊢ p ∈ Submodule.span R ↑(image (fun n => X ^ n) (range n))
    replace hp := mem_degreeLT.1 hp
    -- ⊢ p ∈ Submodule.span R ↑(image (fun n => X ^ n) (range n))
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    -- ⊢ ∑ n in support p, ↑(monomial n) (coeff p n) ∈ Submodule.span R ↑(image (fun  …
    refine' Submodule.sum_mem _ fun k hk => _
    -- ⊢ ↑(monomial k) (coeff p k) ∈ Submodule.span R ↑(image (fun n => X ^ n) (range …
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    -- ⊢ ↑(monomial k) (coeff p k) ∈ Submodule.span R ↑(image (fun n => X ^ n) (range …
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    -- ⊢ coeff p k • X ^ k ∈ Submodule.span R ↑(image (fun n => X ^ n) (range n))
    refine'
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <| Finset.mem_image.2 ⟨_, Finset.mem_range.2 this, rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  -- ⊢ ↑(range n) ⊆ (fun n => X ^ n) ⁻¹' ↑(degreeLT R n)
  intro k hk
  -- ⊢ k ∈ (fun n => X ^ n) ⁻¹' ↑(degreeLT R n)
  apply mem_degreeLT.2
  -- ⊢ degree ((fun n => X ^ n) k) < ↑n
  exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.2 <| Finset.mem_range.1 hk)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.degree_lt_eq_span_X_pow Polynomial.degreeLT_eq_span_X_pow

/-- The first `n` coefficients on `degreeLT n` form a linear equivalence with `Fin n → R`. -/
def degreeLTEquiv (R) [Semiring R] (n : ℕ) : degreeLT R n ≃ₗ[R] Fin n → R where
  toFun p n := (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
      (degreeLT R n).sum_mem fun i _ =>
        mem_degreeLT.mpr
          (lt_of_le_of_lt (degree_monomial_le i (f i)) (WithBot.coe_lt_coe.mpr i.is_lt))⟩
  map_add' p q := by
    ext
    -- ⊢ (fun p n_1 => coeff ↑p ↑n_1) (p + q) x✝ = ((fun p n_1 => coeff ↑p ↑n_1) p +  …
    dsimp
    -- ⊢ coeff (↑p + ↑q) ↑x✝ = coeff ↑p ↑x✝ + coeff ↑q ↑x✝
    rw [coeff_add]
    -- 🎉 no goals
  map_smul' x p := by
    ext
    -- ⊢ AddHom.toFun { toFun := fun p n_1 => coeff ↑p ↑n_1, map_add' := (_ : ∀ (p q  …
    dsimp
    -- ⊢ coeff (x • ↑p) ↑x✝ = x * coeff ↑p ↑x✝
    rw [coeff_smul]
    -- ⊢ x • coeff ↑p ↑x✝ = x * coeff ↑p ↑x✝
    rfl
    -- 🎉 no goals
  left_inv := by
    rintro ⟨p, hp⟩
    -- ⊢ (fun f => { val := ∑ i : Fin n, ↑(monomial ↑i) (f i), property := (_ : ∑ i : …
    ext1
    -- ⊢ ↑((fun f => { val := ∑ i : Fin n, ↑(monomial ↑i) (f i), property := (_ : ∑ i …
    simp only [Submodule.coe_mk]
    -- ⊢ ∑ x : Fin n, ↑(monomial ↑x) (coeff p ↑x) = p
    by_cases hp0 : p = 0
    -- ⊢ ∑ x : Fin n, ↑(monomial ↑x) (coeff p ↑x) = p
    · subst hp0
      -- ⊢ ∑ x : Fin n, ↑(monomial ↑x) (coeff 0 ↑x) = 0
      simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
      -- 🎉 no goals
    rw [mem_degreeLT, degree_eq_natDegree hp0,
      Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe] at hp
    conv_rhs => rw [p.as_sum_range' n hp, ← Fin.sum_univ_eq_sum_range]
    -- 🎉 no goals
  right_inv f := by
    ext i
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun p n_1 => coeff ↑p ↑n_1, map_add' : …
    simp only [finset_sum_coeff, Submodule.coe_mk]
    -- ⊢ ∑ b : Fin n, coeff (↑(monomial ↑b) (f b)) ↑i = f i
    rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
    -- ⊢ ∀ (b : Fin n), b ∈ univ → b ≠ i → coeff (↑(monomial ↑b) (f b)) ↑i = 0
    · rintro j - hji
      -- ⊢ coeff (↑(monomial ↑j) (f j)) ↑i = 0
      rw [coeff_monomial, if_neg]
      -- ⊢ ¬↑j = ↑i
      rwa [← Fin.ext_iff]
      -- 🎉 no goals
    · intro h
      -- ⊢ coeff (↑(monomial ↑i) (f i)) ↑i = 0
      exact (h (Finset.mem_univ _)).elim
      -- 🎉 no goals
#align polynomial.degree_lt_equiv Polynomial.degreeLTEquiv

-- Porting note: removed @[simp] as simp can prove this
theorem degreeLTEquiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) :
    degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mk_eq_zero]
  -- 🎉 no goals
#align polynomial.degree_lt_equiv_eq_zero_iff_eq_zero Polynomial.degreeLTEquiv_eq_zero_iff_eq_zero

theorem eval_eq_sum_degreeLTEquiv {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) (x : R) :
    p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : ℕ) := by
  simp_rw [eval_eq_sum]
  -- ⊢ (sum p fun e a => a * x ^ e) = ∑ x_1 : Fin n, ↑(degreeLTEquiv R n) { val :=  …
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm
  -- 🎉 no goals
#align polynomial.eval_eq_sum_degree_lt_equiv Polynomial.eval_eq_sum_degreeLTEquiv

/-- The finset of nonzero coefficients of a polynomial. -/
def frange (p : R[X]) : Finset R :=
  Finset.image (fun n => p.coeff n) p.support
#align polynomial.frange Polynomial.frange

theorem frange_zero : frange (0 : R[X]) = ∅ :=
  rfl
#align polynomial.frange_zero Polynomial.frange_zero

theorem mem_frange_iff {p : R[X]} {c : R} : c ∈ p.frange ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [frange, eq_comm]
  -- 🎉 no goals
#align polynomial.mem_frange_iff Polynomial.mem_frange_iff

theorem frange_one : frange (1 : R[X]) ⊆ {1} := by
  simp only [frange]
  -- ⊢ image (fun n => coeff 1 n) (support 1) ⊆ {1}
  rw [Finset.image_subset_iff]
  -- ⊢ ∀ (x : ℕ), x ∈ support 1 → coeff 1 x ∈ {1}
  simp only [mem_support_iff, ne_eq, mem_singleton, ← C_1, coeff_C]
  -- ⊢ ∀ (x : ℕ), ¬(if x = 0 then 1 else 0) = 0 → (if x = 0 then 1 else 0) = 1
  intro n hn
  -- ⊢ (if n = 0 then 1 else 0) = 1
  simp only [exists_prop, ite_eq_right_iff, not_forall] at hn
  -- ⊢ (if n = 0 then 1 else 0) = 1
  simp [hn]
  -- 🎉 no goals
#align polynomial.frange_one Polynomial.frange_one

theorem coeff_mem_frange (p : R[X]) (n : ℕ) (h : p.coeff n ≠ 0) : p.coeff n ∈ p.frange := by
  simp only [frange, exists_prop, mem_support_iff, Finset.mem_image, Ne.def]
  -- ⊢ ∃ a, ¬coeff p a = 0 ∧ coeff p a = coeff p n
  exact ⟨n, h, rfl⟩
  -- 🎉 no goals
#align polynomial.coeff_mem_frange Polynomial.coeff_mem_frange

theorem geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
    (∑ i in range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : ℕ => (n.choose (i + 1) : R[X]) * X ^ i := by
  ext i
  -- ⊢ coeff (comp (∑ i in range n, X ^ i) (X + 1)) i = coeff (∑ i in range n, ↑(Na …
  trans (n.choose (i + 1) : R); swap
  -- ⊢ coeff (comp (∑ i in range n, X ^ i) (X + 1)) i = ↑(Nat.choose n (i + 1))
                                -- ⊢ ↑(Nat.choose n (i + 1)) = coeff (∑ i in range n, ↑(Nat.choose n (i + 1)) * X …
  · simp only [finset_sum_coeff, ← C_eq_nat_cast, coeff_C_mul_X_pow]
    -- ⊢ ↑(Nat.choose n (i + 1)) = ∑ x in range n, if i = x then ↑(Nat.choose n (x +  …
    rw [Finset.sum_eq_single i, if_pos rfl]
    -- ⊢ ∀ (b : ℕ), b ∈ range n → b ≠ i → (if i = b then ↑(Nat.choose n (b + 1)) else …
    · simp (config := { contextual := true }) only [@eq_comm _ i, if_false, eq_self_iff_true,
        imp_true_iff]
    · simp (config := { contextual := true }) only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, eq_self_iff_true, if_true, imp_true_iff]
  induction' n with n ih generalizing i
  -- ⊢ coeff (comp (∑ i in range Nat.zero, X ^ i) (X + 1)) i = ↑(Nat.choose Nat.zer …
  · dsimp; simp only [zero_comp, coeff_zero, Nat.cast_zero]
    -- ⊢ coeff (comp 0 (X + 1)) i = ↑0
           -- 🎉 no goals
  · simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
    Nat.cast_add, coeff_X_add_one_pow]
set_option linter.uppercaseLean3 false in
#align polynomial.geom_sum_X_comp_X_add_one_eq_sum Polynomial.geom_sum_X_comp_X_add_one_eq_sum

theorem Monic.geom_sum {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i in range n, P ^ i).Monic := by
  nontriviality R
  -- ⊢ Monic (∑ i in range n, P ^ i)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- ⊢ Monic (∑ i in range (Nat.succ n), P ^ i)
  rw [geom_sum_succ']
  -- ⊢ Monic (P ^ n + ∑ i in range n, P ^ i)
  refine' (hP.pow _).add_of_left _
  -- ⊢ degree (∑ i in range n, P ^ i) < degree (P ^ n)
  refine' lt_of_le_of_lt (degree_sum_le _ _) _
  -- ⊢ (sup (range n) fun b => degree (P ^ b)) < degree (P ^ n)
  rw [Finset.sup_lt_iff]
  -- ⊢ ∀ (b : ℕ), b ∈ range n → degree (P ^ b) < degree (P ^ n)
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    -- ⊢ ∀ (b : ℕ), b < n → ↑(natDegree (P ^ b)) < ↑(natDegree (P ^ n))
    simp only [Nat.cast_withBot, WithBot.coe_lt_coe, hP.natDegree_pow]
    -- ⊢ ∀ (b : ℕ), b < n → b * natDegree P < n * natDegree P
    intro k
    -- ⊢ k < n → k * natDegree P < n * natDegree P
    exact nsmul_lt_nsmul hdeg
    -- 🎉 no goals
  · rw [bot_lt_iff_ne_bot, Ne.def, degree_eq_bot]
    -- ⊢ ¬P ^ n = 0
    exact (hP.pow _).ne_zero
    -- 🎉 no goals
#align polynomial.monic.geom_sum Polynomial.Monic.geom_sum

theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i in range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn
#align polynomial.monic.geom_sum' Polynomial.Monic.geom_sum'

theorem monic_geom_sum_X {n : ℕ} (hn : n ≠ 0) : (∑ i in range n, (X : R[X]) ^ i).Monic := by
  nontriviality R
  -- ⊢ Monic (∑ i in range n, X ^ i)
  apply monic_X.geom_sum _ hn
  -- ⊢ 0 < natDegree X
  simp only [natDegree_X, zero_lt_one]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.monic_geom_sum_X Polynomial.monic_geom_sum_X

end Semiring

section Ring

variable [Ring R]

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.frange : Set R)) :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_frange _ H)⟩ :
        Subring.closure (↑p.frange : Set R))
#align polynomial.restriction Polynomial.restriction

@[simp]
theorem coeff_restriction {p : R[X]} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := by
  simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne.def, ite_not]
  split_ifs with h
  -- ⊢ ↑0 = coeff p n
  · rw [h]
    -- ⊢ ↑0 = 0
    rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align polynomial.coeff_restriction Polynomial.coeff_restriction

-- Porting note: removed @[simp] as simp can prove this
theorem coeff_restriction' {p : R[X]} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n :=
  coeff_restriction
#align polynomial.coeff_restriction' Polynomial.coeff_restriction'

@[simp]
theorem support_restriction (p : R[X]) : support (restriction p) = support p := by
  ext i
  -- ⊢ i ∈ support (restriction p) ↔ i ∈ support p
  simp only [mem_support_iff, not_iff_not, Ne.def]
  -- ⊢ coeff (restriction p) i = 0 ↔ coeff p i = 0
  conv_rhs => rw [← coeff_restriction]
  -- ⊢ coeff (restriction p) i = 0 ↔ ↑(coeff (restriction p) i) = 0
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩
  -- 🎉 no goals
#align polynomial.support_restriction Polynomial.support_restriction

@[simp]
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubring_apply, coeff_restriction]
                  -- 🎉 no goals
#align polynomial.map_restriction Polynomial.map_restriction

@[simp]
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]
                                                                                -- 🎉 no goals
#align polynomial.degree_restriction Polynomial.degree_restriction

@[simp]
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [natDegree]
  -- 🎉 no goals
#align polynomial.nat_degree_restriction Polynomial.natDegree_restriction

@[simp]
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  -- ⊢ coeff (restriction p) (natDegree p) = 1 ↔ coeff p (natDegree p) = 1
  rw [← @coeff_restriction _ _ p]
  -- ⊢ coeff (restriction p) (natDegree p) = 1 ↔ ↑(coeff (restriction p) (natDegree …
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩
  -- 🎉 no goals
#align polynomial.monic_restriction Polynomial.monic_restriction

@[simp]
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]
  -- 🎉 no goals
#align polynomial.restriction_zero Polynomial.restriction_zero

@[simp]
theorem restriction_one : restriction (1 : R[X]) = 1 :=
  ext fun i => Subtype.eq <| by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl
                                -- ⊢ (if 0 = i then 1 else 0) = ↑(if 0 = i then 1 else 0)
                                                                               -- ⊢ 1 = ↑1
                                                                                             -- 🎉 no goals
                                                                                             -- 🎉 no goals
#align polynomial.restriction_one Polynomial.restriction_one

variable [Semiring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.frange : Set R)))) x p.restriction := by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coeSubtype]
#align polynomial.eval₂_restriction Polynomial.eval₂_restriction

section ToSubring

variable (p : R[X]) (T : Subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def toSubring (hp : (↑p.frange : Set R) ⊆ T) : T[X] :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i, if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_frange _ H)⟩ :
        T)
#align polynomial.to_subring Polynomial.toSubring

variable (hp : (↑p.frange : Set R) ⊆ T)

@[simp]
theorem coeff_toSubring {n : ℕ} : ↑(coeff (toSubring p T hp) n) = coeff p n := by
  simp only [toSubring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne.def, ite_not]
  split_ifs with h
  -- ⊢ ↑0 = coeff p n
  · rw [h]
    -- ⊢ ↑0 = 0
    rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align polynomial.coeff_to_subring Polynomial.coeff_toSubring

-- Porting note: removed @[simp] as simp can prove this
theorem coeff_toSubring' {n : ℕ} : (coeff (toSubring p T hp) n).1 = coeff p n :=
  coeff_toSubring _ _ hp
#align polynomial.coeff_to_subring' Polynomial.coeff_toSubring'

@[simp]
theorem support_toSubring : support (toSubring p T hp) = support p := by
  ext i
  -- ⊢ i ∈ support (toSubring p T hp) ↔ i ∈ support p
  simp only [mem_support_iff, not_iff_not, Ne.def]
  -- ⊢ coeff (toSubring p T hp) i = 0 ↔ coeff p i = 0
  conv_rhs => rw [← coeff_toSubring p T hp]
  -- ⊢ coeff (toSubring p T hp) i = 0 ↔ ↑(coeff (toSubring p T hp) i) = 0
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩
  -- 🎉 no goals
#align polynomial.support_to_subring Polynomial.support_toSubring

@[simp]
theorem degree_toSubring : (toSubring p T hp).degree = p.degree := by simp [degree]
                                                                      -- 🎉 no goals
#align polynomial.degree_to_subring Polynomial.degree_toSubring

@[simp]
theorem natDegree_toSubring : (toSubring p T hp).natDegree = p.natDegree := by simp [natDegree]
                                                                               -- 🎉 no goals
#align polynomial.nat_degree_to_subring Polynomial.natDegree_toSubring

@[simp]
theorem monic_toSubring : Monic (toSubring p T hp) ↔ Monic p := by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  -- ⊢ coeff (toSubring p T hp) (natDegree p) = 1 ↔ ↑(coeff (toSubring p T hp) (nat …
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩
  -- 🎉 no goals
#align polynomial.monic_to_subring Polynomial.monic_toSubring

@[simp]
theorem toSubring_zero : toSubring (0 : R[X]) T (by simp [frange_zero]) = 0 := by
                                                    -- 🎉 no goals
  ext i
  -- ⊢ ↑(coeff (toSubring 0 T (_ : ↑∅ ⊆ ↑T)) i) = ↑(coeff 0 i)
  simp
  -- 🎉 no goals
#align polynomial.to_subring_zero Polynomial.toSubring_zero

@[simp]
theorem toSubring_one :
    toSubring (1 : R[X]) T
        (Set.Subset.trans frange_one <| Finset.singleton_subset_set_iff.2 T.one_mem) =
      1 :=
  ext fun i => Subtype.eq <| by
    rw [coeff_toSubring', coeff_one, coeff_one, apply_ite Subtype.val, ZeroMemClass.coe_zero,
      OneMemClass.coe_one]
#align polynomial.to_subring_one Polynomial.toSubring_one

@[simp]
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p := by
  ext n
  -- ⊢ coeff (map (Subring.subtype T) (toSubring p T hp)) n = coeff p n
  simp [coeff_map]
  -- 🎉 no goals
#align polynomial.map_to_subring Polynomial.map_toSubring

end ToSubring

variable (T : Subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def ofSubring (p : T[X]) : R[X] :=
  ∑ i in p.support, monomial i (p.coeff i : R)
#align polynomial.of_subring Polynomial.ofSubring

theorem coeff_ofSubring (p : T[X]) (n : ℕ) : coeff (ofSubring T p) n = (coeff p n : T) := by
  simp only [ofSubring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    ite_eq_right_iff, Ne.def, ite_not, Classical.not_not, ite_eq_left_iff]
  intro h
  -- ⊢ 0 = ↑(coeff p n)
  rw [h, ZeroMemClass.coe_zero]
  -- 🎉 no goals
#align polynomial.coeff_of_subring Polynomial.coeff_ofSubring

@[simp]
theorem frange_ofSubring {p : T[X]} : (↑(p.ofSubring T).frange : Set R) ⊆ T := by
  intro i hi
  -- ⊢ i ∈ ↑T
  simp only [frange, Set.mem_image, mem_support_iff, Ne.def, Finset.mem_coe, Finset.coe_image] at hi
  -- ⊢ i ∈ ↑T
  rcases hi with ⟨n, _, h'n⟩
  -- ⊢ i ∈ ↑T
  rw [← h'n, coeff_ofSubring]
  -- ⊢ ↑(coeff p n) ∈ ↑T
  exact Subtype.mem (coeff p n : T)
  -- 🎉 no goals
#align polynomial.frange_of_subring Polynomial.frange_ofSubring

end Ring

section CommRing

variable [CommRing R]

section ModByMonic

variable {q : R[X]}

theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (dvd_iff_modByMonic_eq_zero hq)
#align polynomial.mem_ker_mod_by_monic Polynomial.mem_ker_modByMonic

@[simp]
theorem ker_modByMonicHom (hq : q.Monic) :
    LinearMap.ker (Polynomial.modByMonicHom q) = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm
#align polynomial.ker_mod_by_monic_hom Polynomial.ker_modByMonicHom

end ModByMonic

end CommRing

end Polynomial

namespace Ideal

open Polynomial

section Semiring

variable [Semiring R]

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
def ofPolynomial (I : Ideal R[X]) : Submodule R R[X] where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    -- ⊢ ↑C c * x ∈ { toAddSubsemigroup := { carrier := I.carrier, add_mem' := (_ : ∀ …
    exact I.mul_mem_left _ H
    -- 🎉 no goals
#align ideal.of_polynomial Ideal.ofPolynomial

variable {I : Ideal R[X]}

theorem mem_ofPolynomial (x) : x ∈ I.ofPolynomial ↔ x ∈ I :=
  Iff.rfl
#align ideal.mem_of_polynomial Ideal.mem_ofPolynomial

variable (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  Polynomial.degreeLE R n ⊓ I.ofPolynomial
#align ideal.degree_le Ideal.degreeLE

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leadingCoeffNth (n : ℕ) : Ideal R :=
  (I.degreeLE n).map <| lcoeff R n
#align ideal.leading_coeff_nth Ideal.leadingCoeffNth

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n
#align ideal.leading_coeff Ideal.leadingCoeff

end Semiring

section CommSemiring

variable [CommSemiring R] [Semiring S]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X])
    (hp : ∀ n : ℕ, p.coeff n ∈ I.comap (C : R →+* R[X])) : p ∈ I :=
  sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)
#align ideal.polynomial_mem_ideal_of_coeff_mem_ideal Ideal.polynomial_mem_ideal_of_coeff_mem_ideal

/-- The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : R[X]} :
    f ∈ (Ideal.map (C : R →+* R[X]) I : Ideal R[X]) ↔ ∀ n : ℕ, f.coeff n ∈ I := by
  constructor
  -- ⊢ f ∈ map C I → ∀ (n : ℕ), coeff f n ∈ I
  · intro hf
    -- ⊢ ∀ (n : ℕ), coeff f n ∈ I
    apply @Submodule.span_induction _ _ _ _ _ f _ _ hf
    · intro f hf n
      -- ⊢ coeff f n ∈ I
      cases' (Set.mem_image _ _ _).mp hf with x hx
      -- ⊢ coeff f n ∈ I
      rw [← hx.right, coeff_C]
      -- ⊢ (if n = 0 then x else 0) ∈ I
      by_cases h : n = 0
      -- ⊢ (if n = 0 then x else 0) ∈ I
      · simpa [h] using hx.left
        -- 🎉 no goals
      · simp [h]
        -- 🎉 no goals
    · simp
      -- 🎉 no goals
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
      -- 🎉 no goals
    · refine' fun f g hg n => _
      -- ⊢ coeff (f • g) n ∈ I
      rw [smul_eq_mul, coeff_mul]
      -- ⊢ ∑ x in Nat.antidiagonal n, coeff f x.fst * coeff g x.snd ∈ I
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
      -- 🎉 no goals
  · intro hf
    -- ⊢ f ∈ map C I
    rw [← sum_monomial_eq f]
    -- ⊢ (sum f fun n a => ↑(monomial n) a) ∈ map C I
    refine' (I.map C : Ideal R[X]).sum_mem fun n _ => _
    -- ⊢ (fun n a => ↑(monomial n) a) n (coeff f n) ∈ map C I
    simp [← C_mul_X_pow_eq_monomial]
    -- ⊢ ↑C (coeff f n) * X ^ n ∈ map C I
    rw [mul_comm]
    -- ⊢ X ^ n * ↑C (coeff f n) ∈ map C I
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align ideal.mem_map_C_iff Ideal.mem_map_C_iff

theorem _root_.Polynomial.ker_mapRingHom (f : R →+* S) :
    LinearMap.ker (Polynomial.mapRingHom f).toSemilinearMap = f.ker.map (C : R →+* R[X]) := by
  ext
  -- ⊢ x✝ ∈ LinearMap.ker (RingHom.toSemilinearMap (mapRingHom f)) ↔ x✝ ∈ map C (Ri …
  simp only [LinearMap.mem_ker, RingHom.toSemilinearMap_apply, coe_mapRingHom]
  -- ⊢ Polynomial.map f x✝ = 0 ↔ x✝ ∈ map C (RingHom.ker f)
  rw [mem_map_C_iff, Polynomial.ext_iff]
  -- ⊢ (∀ (n : ℕ), coeff (Polynomial.map f x✝) n = coeff 0 n) ↔ ∀ (n : ℕ), coeff x✝ …
  simp_rw [RingHom.mem_ker f, coeff_map, coeff_zero]
  -- 🎉 no goals
#align polynomial.ker_map_ring_hom Polynomial.ker_mapRingHom

variable (I : Ideal R[X])

theorem mem_leadingCoeffNth (n : ℕ) (x) :
    x ∈ I.leadingCoeffNth n ↔ ∃ p ∈ I, degree p ≤ n ∧ p.leadingCoeff = x := by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  -- ⊢ (∃ y, (degree y ≤ ↑n ∧ y ∈ ofPolynomial I) ∧ coeff y n = x) → ∃ p, p ∈ I ∧ d …
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    -- ⊢ ∃ p_1, p_1 ∈ I ∧ degree p_1 ≤ ↑n ∧ Polynomial.leadingCoeff p_1 = coeff p n
    cases' lt_or_eq_of_le hpdeg with hpdeg hpdeg
    -- ⊢ ∃ p_1, p_1 ∈ I ∧ degree p_1 ≤ ↑n ∧ Polynomial.leadingCoeff p_1 = coeff p n
    · refine' ⟨0, I.zero_mem, bot_le, _⟩
      -- ⊢ Polynomial.leadingCoeff 0 = coeff p n
      rw [leadingCoeff_zero, eq_comm]
      -- ⊢ coeff p n = 0
      exact coeff_eq_zero_of_degree_lt hpdeg
      -- 🎉 no goals
    · refine' ⟨p, hpI, le_of_eq hpdeg, _⟩
      -- ⊢ Polynomial.leadingCoeff p = coeff p n
      rw [Polynomial.leadingCoeff, natDegree, hpdeg, Nat.cast_withBot, WithBot.unbot'_coe]
      -- 🎉 no goals
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    -- ⊢ ∃ y, (degree y ≤ ↑n ∧ y ∈ ofPolynomial I) ∧ coeff y n = Polynomial.leadingCo …
    have : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine' ⟨p * X ^ (n - natDegree p), ⟨_, I.mul_mem_right _ hpI⟩, _⟩
    -- ⊢ degree (p * X ^ (n - natDegree p)) ≤ ↑n
    · apply le_trans (degree_mul_le _ _) _
      -- ⊢ degree p + degree (X ^ (n - natDegree p)) ≤ ↑n
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      -- ⊢ ↑(natDegree p) + ↑(n - natDegree p) ≤ ↑n
      rw [Nat.cast_withBot, Nat.cast_withBot, ← WithBot.coe_add, this, Nat.cast_withBot]
      -- 🎉 no goals
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), this]
      -- 🎉 no goals
#align ideal.mem_leading_coeff_nth Ideal.mem_leadingCoeffNth

theorem mem_leadingCoeffNth_zero (x) : x ∈ I.leadingCoeffNth 0 ↔ C x ∈ I :=
  (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩
#align ideal.mem_leading_coeff_nth_zero Ideal.mem_leadingCoeffNth_zero

theorem leadingCoeffNth_mono {m n : ℕ} (H : m ≤ n) : I.leadingCoeffNth m ≤ I.leadingCoeffNth n := by
  intro r hr
  -- ⊢ r ∈ leadingCoeffNth I n
  simp only [SetLike.mem_coe, mem_leadingCoeffNth] at hr ⊢
  -- ⊢ ∃ p, p ∈ I ∧ degree p ≤ ↑n ∧ Polynomial.leadingCoeff p = r
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  -- ⊢ ∃ p_1, p_1 ∈ I ∧ degree p_1 ≤ ↑n ∧ Polynomial.leadingCoeff p_1 = Polynomial. …
  refine' ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, _, leadingCoeff_mul_X_pow⟩
  -- ⊢ degree (p * X ^ (n - m)) ≤ ↑n
  refine' le_trans (degree_mul_le _ _) _
  -- ⊢ degree p + degree (X ^ (n - m)) ≤ ↑n
  refine' le_trans (add_le_add hpdeg (degree_X_pow_le _)) _
  -- ⊢ ↑m + ↑(n - m) ≤ ↑n
  rw [Nat.cast_withBot, Nat.cast_withBot, ← WithBot.coe_add, add_tsub_cancel_of_le H,
    Nat.cast_withBot]
#align ideal.leading_coeff_nth_mono Ideal.leadingCoeffNth_mono

theorem mem_leadingCoeff (x) : x ∈ I.leadingCoeff ↔ ∃ p ∈ I, Polynomial.leadingCoeff p = x := by
  rw [leadingCoeff, Submodule.mem_iSup_of_directed]
  -- ⊢ (∃ i, x ∈ leadingCoeffNth I i) ↔ ∃ p, p ∈ I ∧ Polynomial.leadingCoeff p = x
  simp only [mem_leadingCoeffNth]
  -- ⊢ (∃ i p, p ∈ I ∧ degree p ≤ ↑i ∧ Polynomial.leadingCoeff p = x) ↔ ∃ p, p ∈ I  …
  · constructor
    -- ⊢ (∃ i p, p ∈ I ∧ degree p ≤ ↑i ∧ Polynomial.leadingCoeff p = x) → ∃ p, p ∈ I  …
    · rintro ⟨i, p, hpI, _, rfl⟩
      -- ⊢ ∃ p_1, p_1 ∈ I ∧ Polynomial.leadingCoeff p_1 = Polynomial.leadingCoeff p
      exact ⟨p, hpI, rfl⟩
      -- 🎉 no goals
    rintro ⟨p, hpI, rfl⟩
    -- ⊢ ∃ i p_1, p_1 ∈ I ∧ degree p_1 ≤ ↑i ∧ Polynomial.leadingCoeff p_1 = Polynomia …
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
    -- 🎉 no goals
  intro i j
  -- ⊢ ∃ z, (fun x x_1 => x ≤ x_1) ((fun n => leadingCoeffNth I n) i) ((fun n => le …
  exact
    ⟨i + j, I.leadingCoeffNth_mono (Nat.le_add_right _ _),
      I.leadingCoeffNth_mono (Nat.le_add_left _ _)⟩
#align ideal.mem_leading_coeff Ideal.mem_leadingCoeff

/-- If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ⁻ᵏ` with `n = ∑ nᵢ`.
-/
theorem _root_.Polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (I : Ideal R) (n : ι → ℕ) (h : ∀ i ∈ s, ∀ (k), (f i).coeff k ∈ I ^ (n i - k)) (k : ℕ) :
    (s.prod f).coeff k ∈ I ^ (s.sum n - k) := by
  classical
    induction' s using Finset.induction with a s ha hs generalizing k
    · rw [sum_empty, prod_empty, coeff_one, zero_tsub, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [sum_insert ha, prod_insert ha, coeff_mul]
      apply sum_mem
      rintro ⟨i, j⟩ e
      obtain rfl : i + j = k := Nat.mem_antidiagonal.mp e
      apply Ideal.pow_le_pow add_tsub_add_le_tsub_add_tsub
      rw [pow_add]
      exact
        Ideal.mul_mem_mul (h _ (Finset.mem_insert.mpr <| Or.inl rfl) _)
          (hs (fun i hi k => h _ (Finset.mem_insert.mpr <| Or.inr hi) _) j)
#align polynomial.coeff_prod_mem_ideal_pow_tsub Polynomial.coeff_prod_mem_ideal_pow_tsub

end CommSemiring

section Ring

variable [Ring R]

/-- `R[X]` is never a field for any ring `R`. -/
theorem polynomial_not_isField : ¬IsField R[X] := by
  nontriviality R
  -- ⊢ ¬IsField R[X]
  intro hR
  -- ⊢ False
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  -- ⊢ False
  have hp0 : p ≠ 0 := right_ne_zero_of_mul_eq_one hp
  -- ⊢ False
  have := degree_lt_degree_mul_X hp0
  -- ⊢ False
  rw [← X_mul, congr_arg degree hp, degree_one, Nat.WithBot.lt_zero_iff, degree_eq_bot] at this
  -- ⊢ False
  exact hp0 this
  -- 🎉 no goals
#align ideal.polynomial_not_is_field Ideal.polynomial_not_isField

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : C x ∈ I) : x = 0 := by
  refine' Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 _)
  -- ⊢ 1 ∈ I
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  -- ⊢ 1 ∈ I
  convert I.mul_mem_left (C y) hx
  -- ⊢ 1 = ↑C y * ↑C x
  rw [← C.map_mul, hR.mul_comm y x, hy, RingHom.map_one]
  -- 🎉 no goals
#align ideal.eq_zero_of_constant_mem_of_maximal Ideal.eq_zero_of_constant_mem_of_maximal

end Ring

section CommRing

variable [CommRing R]

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem isPrime_map_C_iff_isPrime (P : Ideal R) :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) ↔ IsPrime P := by
  -- Porting note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  -- ⊢ IsPrime (map C P) → IsPrime P
  · intro H
    -- ⊢ IsPrime P
    have := @comap_isPrime R R[X] (R →+* R[X]) _ _ _ C (map C P) H
    -- ⊢ IsPrime P
    convert this using 1
    -- ⊢ P = comap C (map C P)
    ext x
    -- ⊢ x ∈ P ↔ x ∈ comap C (map C P)
    simp only [mem_comap, mem_map_C_iff]
    -- ⊢ x ∈ P ↔ ∀ (n : ℕ), coeff (↑C x) n ∈ P
    constructor
    -- ⊢ x ∈ P → ∀ (n : ℕ), coeff (↑C x) n ∈ P
    · rintro h (- | n)
      -- ⊢ coeff (↑C x) Nat.zero ∈ P
      · rwa [coeff_C_zero]
        -- 🎉 no goals
      · simp only [coeff_C_ne_zero (Nat.succ_ne_zero _), Submodule.zero_mem]
        -- 🎉 no goals
    · intro h
      -- ⊢ x ∈ P
      simpa only [coeff_C_zero] using h 0
      -- 🎉 no goals
  · intro h
    -- ⊢ IsPrime (map C P)
    constructor
    -- ⊢ map C P ≠ ⊤
    · rw [Ne.def, eq_top_iff_one, mem_map_C_iff, not_forall]
      -- ⊢ ∃ x, ¬coeff 1 x ∈ P
      use 0
      -- ⊢ ¬coeff 1 0 ∈ P
      rw [coeff_one_zero, ← eq_top_iff_one]
      -- ⊢ ¬P = ⊤
      exact h.1
      -- 🎉 no goals
    · intro f g
      -- ⊢ f * g ∈ map C P → f ∈ map C P ∨ g ∈ map C P
      simp only [mem_map_C_iff]
      -- ⊢ (∀ (n : ℕ), coeff (f * g) n ∈ P) → (∀ (n : ℕ), coeff f n ∈ P) ∨ ∀ (n : ℕ), c …
      contrapose!
      -- ⊢ ((∃ n, ¬coeff f n ∈ P) ∧ ∃ n, ¬coeff g n ∈ P) → ∃ n, ¬coeff (f * g) n ∈ P
      rintro ⟨hf, hg⟩
      -- ⊢ ∃ n, ¬coeff (f * g) n ∈ P
      classical
        let m := Nat.find hf
        let n := Nat.find hg
        refine' ⟨m + n, _⟩
        rw [coeff_mul, ← Finset.insert_erase ((@Finset.Nat.mem_antidiagonal _ (m, n)).mpr rfl),
          Finset.sum_insert (Finset.not_mem_erase _ _), (P.add_mem_iff_left _).not]
        · apply mt h.2
          rw [not_or]
          exact ⟨Nat.find_spec hf, Nat.find_spec hg⟩
        apply P.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_erase, Finset.Nat.mem_antidiagonal] at hij
        simp only [Ne.def, Prod.mk.inj_iff, not_and_or] at hij
        obtain hi | hj : i < m ∨ j < n := by
          rw [or_iff_not_imp_left, not_lt, le_iff_lt_or_eq]
          rintro (hmi | rfl)
          · rw [← not_le]
            intro hnj
            exact (add_lt_add_of_lt_of_le hmi hnj).ne hij.2.symm
          · simp only [eq_self_iff_true, not_true, false_or_iff, add_right_inj,
              not_and_self_iff] at hij
        · rw [mul_comm]
          apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hf hi)
        · apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hg hj)
set_option linter.uppercaseLean3 false in
#align ideal.is_prime_map_C_iff_is_prime Ideal.isPrime_map_C_iff_isPrime

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem isPrime_map_C_of_isPrime {P : Ideal R} (H : IsPrime P) :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) :=
  (isPrime_map_C_iff_isPrime P).mpr H
set_option linter.uppercaseLean3 false in
#align ideal.is_prime_map_C_of_is_prime Ideal.isPrime_map_C_of_isPrime

theorem is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X]) (n : ℕ) :
    Submodule.FG (I.degreeLE n) :=
  isNoetherian_submodule_left.1
    -- porting note: times out without explicit `R`.
    (isNoetherian_of_fg_of_noetherian _ ⟨_, (degreeLE_eq_span_X_pow (R := R)).symm⟩) _
#align ideal.is_fg_degree_le Ideal.is_fg_degreeLE

end CommRing

end Ideal

variable {σ : Type v} {M : Type w}

variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

-- Porting note: this ordering of the argument dramatically speeds up lean
theorem prime_C_iff : Prime (C r) ↔ Prime r :=
  ⟨comap_prime C (evalRingHom (0 : R)) fun r => eval_C, by
    intro hr
    -- ⊢ Prime (↑C r)
    have := hr.1
    -- ⊢ Prime (↑C r)
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      -- ⊢ Ideal.IsPrime (Ideal.map C (Ideal.span {r}))
      apply Ideal.isPrime_map_C_of_isPrime hr
      -- 🎉 no goals
    · intro h; apply (this (C_eq_zero.mp h))
      -- ⊢ False
               -- 🎉 no goals
    · assumption⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.prime_C_iff Polynomial.prime_C_iff

end Polynomial

namespace MvPolynomial

/- Porting note: had to move the heavy inference outside the convert call to stop timeouts.
Also, many @'s. etaExperiment caused more time outs-/
private theorem prime_C_iff_of_fintype {R : Type u} (σ : Type v) {r : R} [CommRing R] [Fintype σ] :
    Prime (C r : MvPolynomial σ R) ↔ Prime r := by
  let f (d : ℕ) := (finSuccEquiv R d).symm.toMulEquiv
  -- ⊢ Prime (↑C r) ↔ Prime r
  let _coe' (d : ℕ) : CoeFun ((MvPolynomial (Fin d) R)[X] ≃* MvPolynomial (Fin (d + 1)) R)
    (fun _ => (MvPolynomial (Fin d) R)[X] → MvPolynomial (Fin (d + 1)) R) := inferInstance
  have that (d : ℕ) : @C R (Fin (d+1)) _ r = (f d) (Polynomial.C (@C R (Fin d) _ r)) := by
    rw [← finSuccEquiv_comp_C_eq_C]; rfl
  rw [(renameEquiv R (Fintype.equivFin σ)).toMulEquiv.prime_iff]
  -- ⊢ Prime (↑(AlgEquiv.toMulEquiv (renameEquiv R (Fintype.equivFin σ))) (↑C r)) ↔ …
  convert_to Prime (C r) ↔ _
  · congr!
    -- ⊢ ↑(AlgEquiv.toMulEquiv (renameEquiv R (Fintype.equivFin σ))) (↑C r) = ↑C r
    apply rename_C
    -- 🎉 no goals
  · symm
    -- ⊢ Prime r ↔ Prime (↑C r)
    induction' Fintype.card σ with d hd
    -- ⊢ Prime r ↔ Prime (↑C r)
    · exact (isEmptyAlgEquiv R (Fin 0)).toMulEquiv.symm.prime_iff
      -- 🎉 no goals
    · rw [hd, ← Polynomial.prime_C_iff]
      -- ⊢ Prime (↑Polynomial.C (↑C r)) ↔ Prime (↑C r)
      rw [that d]
      -- ⊢ Prime (↑Polynomial.C (↑C r)) ↔ Prime (↑(f d) (↑Polynomial.C (↑C r)))
      -- Porting note: change ?_ to _ and watch it time out
      refine @MulEquiv.prime_iff (MvPolynomial (Fin d) R)[X] (MvPolynomial (Fin (d + 1)) R)
        ?_ ?_ (Polynomial.C (C r)) ?_

-- Porting note: @'s help with multiple timeouts. It seems like there are too many things to unify
theorem prime_C_iff : Prime (C r : MvPolynomial σ R) ↔ Prime r :=
  ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
    ⟨fun h =>
      hr.1 <| by
        rw [← C_inj, h]
        -- ⊢ 0 = ↑C 0
        simp,
        -- 🎉 no goals
      fun h =>
      hr.2.1 <| by
        rw [← constantCoeff_C _ r]
        -- ⊢ IsUnit (↑constantCoeff (↑C r))
        exact h.map _,
        -- 🎉 no goals
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      -- ⊢ ↑C r ∣ ↑(rename Subtype.val) a' ∨ ↑C r ∣ ↑(rename Subtype.val) b'
      rw [← algebraMap_eq] at hd
      -- ⊢ ↑C r ∣ ↑(rename Subtype.val) a' ∨ ↑C r ∣ ↑(rename Subtype.val) b'
      have := (@killCompl s σ R _ ((↑) : s → σ) Subtype.coe_injective).toRingHom.map_dvd hd
      -- ⊢ ↑C r ∣ ↑(rename Subtype.val) a' ∨ ↑C r ∣ ↑(rename Subtype.val) b'
      have : algebraMap R _ r ∣ a' * b' := by convert this <;> simp
      -- ⊢ ↑C r ∣ ↑(rename Subtype.val) a' ∨ ↑C r ∣ ↑(rename Subtype.val) b'
      rw [← rename_C ((↑) : s → σ)]
      -- ⊢ ↑(rename Subtype.val) (↑C r) ∣ ↑(rename Subtype.val) a' ∨ ↑(rename Subtype.v …
      let f := @AlgHom.toRingHom R (MvPolynomial s R)
        (MvPolynomial σ R) _ _ _ _ _ (@rename _ _ R _ ((↑) : s → σ))
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp f.map_dvd f.map_dvd⟩⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.prime_C_iff MvPolynomial.prime_C_iff

variable {σ}

theorem prime_rename_iff (s : Set σ) {p : MvPolynomial s R} :
    Prime (rename ((↑) : s → σ) p) ↔ Prime (p : MvPolynomial s R) := by
  classical
    symm
    let eqv :=
      (sumAlgEquiv R (↥sᶜ) s).symm.trans
        (renameEquiv R <| (Equiv.sumComm (↥sᶜ) s).trans <| Equiv.Set.sumCompl s)
    have : (rename (↑)).toRingHom = eqv.toAlgHom.toRingHom.comp C := by
      apply ringHom_ext
      · intro
        dsimp
        erw [iterToSum_C_C, rename_C, rename_C]
      · intro
        dsimp
        erw [iterToSum_C_X, rename_X, rename_X]
        rfl
    rw [← @prime_C_iff (MvPolynomial s R) (↥sᶜ) instCommRingMvPolynomial p]
    rw [@MulEquiv.prime_iff (MvPolynomial ↑sᶜ (MvPolynomial ↑s R)) (MvPolynomial σ R) (_) (_)]
    rotate_left
    exact eqv.toMulEquiv
    convert Iff.rfl
    apply RingHom.congr_fun this p
#align mv_polynomial.prime_rename_iff MvPolynomial.prime_rename_iff

end MvPolynomial

end Prime

namespace Polynomial

instance (priority := 100) {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] : WfDvdMonoid R[X]
    where
  wellFounded_dvdNotUnit := by
    classical
      refine'
        RelHomClass.wellFounded
          (⟨fun p : R[X] =>
              ((if p = 0 then ⊤ else ↑p.degree : WithTop (WithBot ℕ)), p.leadingCoeff), _⟩ :
            DvdNotUnit →r Prod.Lex (· < ·) DvdNotUnit)
          (WellFounded.prod_lex (WithTop.wellFounded_lt <| WithBot.wellFounded_lt Nat.lt_wfRel.wf)
            ‹WfDvdMonoid R›.wellFounded_dvdNotUnit)
      rintro a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩
      dsimp
      rw [Polynomial.degree_mul, if_neg ane0]
      split_ifs with hac
      · rw [hac, Polynomial.leadingCoeff_zero]
        apply Prod.Lex.left
        exact lt_of_le_of_ne le_top WithTop.coe_ne_top
      have cne0 : c ≠ 0 := right_ne_zero_of_mul hac
      simp only [cne0, ane0, Polynomial.leadingCoeff_mul]
      by_cases hdeg : c.degree = 0
      · simp only [hdeg, add_zero]
        refine' Prod.Lex.right _ ⟨_, ⟨c.leadingCoeff, fun unit_c => not_unit_c _, rfl⟩⟩
        · rwa [Ne, Polynomial.leadingCoeff_eq_zero]
        rw [Polynomial.isUnit_iff, Polynomial.eq_C_of_degree_eq_zero hdeg]
        use c.leadingCoeff, unit_c
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]; rfl
      · apply Prod.Lex.left
        rw [Polynomial.degree_eq_natDegree cne0] at *
        rw [WithTop.coe_lt_coe, Polynomial.degree_eq_natDegree ane0,
          Nat.cast_withBot, Nat.cast_withBot,← WithBot.coe_add, WithBot.coe_lt_coe]
        exact lt_add_of_pos_right _ (Nat.pos_of_ne_zero fun h => hdeg (h.symm ▸ WithBot.coe_zero))

end Polynomial

/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected theorem Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M :=
        WellFounded.min (isNoetherian_iff_wellFounded.1 (by infer_instance))
                                                            -- 🎉 no goals
          (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M ∈ Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := fun k =>
        Or.casesOn (le_or_lt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h x hx =>
          Classical.by_contradiction fun hxm =>
            haveI : IsNoetherian R R := inst
            have : ¬M < I.leadingCoeffNth k := by
              refine' WellFounded.not_lt_min (wellFounded_submodule_gt R R) _ _ _; exact ⟨k, rfl⟩
              -- ⊢ Ideal.leadingCoeffNth I k ∈ Set.range (Ideal.leadingCoeffNth I)
                                                                                   -- 🎉 no goals
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : ∀ {x}, x ∈ I.degreeLE N → x ∈ Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun hx =>
          Submodule.span_induction hx (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ => Ideal.add_mem _) fun c f hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s, le_antisymm (Ideal.span_le.2 fun x hx =>
          have : x ∈ I.degreeLE N := hs ▸ Submodule.subset_span hx
          this.2) <| by
        have : Submodule.span R[X] ↑s = Ideal.span ↑s := by rfl
        -- ⊢ I ≤ Submodule.span R[X] ↑s
        rw [this]
        -- ⊢ I ≤ Ideal.span ↑s
        intro p hp
        -- ⊢ p ∈ Ideal.span ↑s
        generalize hn : p.natDegree = k
        -- ⊢ p ∈ Ideal.span ↑s
        induction' k using Nat.strong_induction_on with k ih generalizing p
        -- ⊢ p ∈ Ideal.span ↑s
        cases' le_or_lt k N with h h
        -- ⊢ p ∈ Ideal.span ↑s
        · subst k
          -- ⊢ p ∈ Ideal.span ↑s
          refine' hs2 ⟨Polynomial.mem_degreeLE.2
            (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h), hp⟩
        · have hp0 : p ≠ 0 := by
            rintro rfl
            cases hn
            exact Nat.not_lt_zero _ h
          have : (0 : R) ≠ 1 := by
            intro h
            apply hp0
            ext i
            refine' (mul_one _).symm.trans _
            rw [← h, mul_zero]
            rfl
          haveI : Nontrivial R := ⟨⟨0, 1, this⟩⟩
          -- ⊢ p ∈ Ideal.span ↑s
          have : p.leadingCoeff ∈ I.leadingCoeffNth N := by
            rw [HN]
            exact hm2 k ((I.mem_leadingCoeffNth _ _).2
              ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
          rw [I.mem_leadingCoeffNth] at this
          -- ⊢ p ∈ Ideal.span ↑s
          rcases this with ⟨q, hq, hdq, hlqp⟩
          -- ⊢ p ∈ Ideal.span ↑s
          have hq0 : q ≠ 0 := by
            intro H
            rw [← Polynomial.leadingCoeff_eq_zero] at H
            rw [hlqp, Polynomial.leadingCoeff_eq_zero] at H
            exact hp0 H
          have h1 : p.degree = (q * Polynomial.X ^ (k - q.natDegree)).degree := by
            rw [Polynomial.degree_mul', Polynomial.degree_X_pow]
            rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
            rw [Nat.cast_withBot, Nat.cast_withBot, Nat.cast_withBot, ← WithBot.coe_add,
              add_tsub_cancel_of_le, hn]
            · refine' le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
            rw [Polynomial.leadingCoeff_X_pow, mul_one]
            exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
          have h2 : p.leadingCoeff = (q * Polynomial.X ^ (k - q.natDegree)).leadingCoeff := by
            rw [← hlqp, Polynomial.leadingCoeff_mul_X_pow]
          have := Polynomial.degree_sub_lt h1 hp0 h2
          -- ⊢ p ∈ Ideal.span ↑s
          rw [Polynomial.degree_eq_natDegree hp0] at this
          -- ⊢ p ∈ Ideal.span ↑s
          rw [← sub_add_cancel p (q * Polynomial.X ^ (k - q.natDegree))]
          -- ⊢ p - q * X ^ (k - natDegree q) + q * X ^ (k - natDegree q) ∈ Ideal.span ↑s
          refine' (Ideal.span ↑s).add_mem _ ((Ideal.span ↑s).mul_mem_right _ _)
          -- ⊢ p - q * X ^ (k - natDegree q) ∈ Ideal.span ↑s
          · by_cases hpq : p - q * Polynomial.X ^ (k - q.natDegree) = 0
            -- ⊢ p - q * X ^ (k - natDegree q) ∈ Ideal.span ↑s
            · rw [hpq]
              -- ⊢ 0 ∈ Ideal.span ↑s
              exact Ideal.zero_mem _
              -- 🎉 no goals
            refine' ih _ _ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
            -- ⊢ natDegree (p - q * X ^ (k - natDegree q)) < k
            rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_withBot, Nat.cast_withBot,
              WithBot.coe_lt_coe, hn] at this
          exact hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩⟩⟩
          -- 🎉 no goals
#align polynomial.is_noetherian_ring Polynomial.isNoetherianRing

attribute [instance] Polynomial.isNoetherianRing

namespace Polynomial

theorem exists_irreducible_of_degree_pos {R : Type u} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    {f : R[X]} (hf : 0 < f.degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
    fun hf0 => not_lt_of_lt hf <| hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _
#align polynomial.exists_irreducible_of_degree_pos Polynomial.exists_irreducible_of_degree_pos

theorem exists_irreducible_of_natDegree_pos {R : Type u} [CommRing R] [IsDomain R] [WfDvdMonoid R]
    {f : R[X]} (hf : 0 < f.natDegree) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_degree_pos <| by
    contrapose! hf
    -- ⊢ natDegree f ≤ 0
    exact natDegree_le_of_degree_le hf
    -- 🎉 no goals
#align polynomial.exists_irreducible_of_nat_degree_pos Polynomial.exists_irreducible_of_natDegree_pos

theorem exists_irreducible_of_natDegree_ne_zero {R : Type u} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] {f : R[X]} (hf : f.natDegree ≠ 0) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_natDegree_pos <| Nat.pos_of_ne_zero hf
#align polynomial.exists_irreducible_of_nat_degree_ne_zero Polynomial.exists_irreducible_of_natDegree_ne_zero

theorem linearIndependent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : ℕ => (f ^ n) v) ↔ ∀ p : R[X], aeval f p v = 0 → p = 0 := by
  rw [linearIndependent_iff]
  -- ⊢ (∀ (l : ℕ →₀ R), ↑(Finsupp.total ℕ ((fun x => M) v) R fun n => ↑(f ^ n) v) l …
  simp only [Finsupp.total_apply, aeval_endomorphism, forall_iff_forall_finsupp, Sum, support,
    coeff, ofFinsupp_eq_zero]
  exact Iff.rfl
  -- 🎉 no goals
#align polynomial.linear_independent_powers_iff_aeval Polynomial.linearIndependent_powers_iff_aeval

attribute [-instance] Ring.toNonAssocRing

theorem disjoint_ker_aeval_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q)) := by
  rw [disjoint_iff_inf_le]
  -- ⊢ LinearMap.ker (↑(aeval f) p) ⊓ LinearMap.ker (↑(aeval f) q) ≤ ⊥
  intro v hv
  -- ⊢ v ∈ ⊥
  rcases hpq with ⟨p', q', hpq'⟩
  -- ⊢ v ∈ ⊥
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm
#align polynomial.disjoint_ker_aeval_of_coprime Polynomial.disjoint_ker_aeval_of_coprime

theorem sup_aeval_range_eq_top_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤ := by
  rw [eq_top_iff]
  -- ⊢ ⊤ ≤ LinearMap.range (↑(aeval f) p) ⊔ LinearMap.range (↑(aeval f) q)
  intro v _
  -- ⊢ v ∈ LinearMap.range (↑(aeval f) p) ⊔ LinearMap.range (↑(aeval f) q)
  rw [Submodule.mem_sup]
  -- ⊢ ∃ y, y ∈ LinearMap.range (↑(aeval f) p) ∧ ∃ z, z ∈ LinearMap.range (↑(aeval  …
  rcases hpq with ⟨p', q', hpq'⟩
  -- ⊢ ∃ y, y ∈ LinearMap.range (↑(aeval f) p) ∧ ∃ z, z ∈ LinearMap.range (↑(aeval  …
  use aeval f (p * p') v
  -- ⊢ ↑(↑(aeval f) (p * p')) v ∈ LinearMap.range (↑(aeval f) p) ∧ ∃ z, z ∈ LinearM …
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  -- ⊢ ∃ z, z ∈ LinearMap.range (↑(aeval f) q) ∧ ↑(↑(aeval f) (p * p')) v + z = v
  use aeval f (q * q') v
  -- ⊢ ↑(↑(aeval f) (q * q')) v ∈ LinearMap.range (↑(aeval f) q) ∧ ↑(↑(aeval f) (p  …
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  -- ⊢ ↑(↑(aeval f) (p * p')) v + ↑(↑(aeval f) (q * q')) v = v
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'
#align polynomial.sup_aeval_range_eq_top_of_coprime Polynomial.sup_aeval_range_eq_top_of_coprime

theorem sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) ≤ LinearMap.ker (aeval f (p * q)) := by
  intro v hv
  -- ⊢ v ∈ LinearMap.ker (↑(aeval f) (p * q))
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  -- ⊢ v ∈ LinearMap.ker (↑(aeval f) (p * q))
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm, aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hx, LinearMap.map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hy, LinearMap.map_zero]
  rw [LinearMap.mem_ker, ← hxy, LinearMap.map_add, h_eval_x, h_eval_y, add_zero]
  -- 🎉 no goals
#align polynomial.sup_ker_aeval_le_ker_aeval_mul Polynomial.sup_ker_aeval_le_ker_aeval_mul

theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M →ₗ[R] M) {p q : R[X]}
    (hpq : IsCoprime p q) :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) = LinearMap.ker (aeval f (p * q)) := by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  -- ⊢ LinearMap.ker (↑(aeval f) (p * q)) ≤ LinearMap.ker (↑(aeval f) p) ⊔ LinearMa …
  intro v hv
  -- ⊢ v ∈ LinearMap.ker (↑(aeval f) p) ⊔ LinearMap.ker (↑(aeval f) q)
  rw [Submodule.mem_sup]
  -- ⊢ ∃ y, y ∈ LinearMap.ker (↑(aeval f) p) ∧ ∃ z, z ∈ LinearMap.ker (↑(aeval f) q …
  rcases hpq with ⟨p', q', hpq'⟩
  -- ⊢ ∃ y, y ∈ LinearMap.ker (↑(aeval f) p) ∧ ∃ z, z ∈ LinearMap.ker (↑(aeval f) q …
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm q p]
      _ = 0 := by rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]

  have h_eval₂_pqq' :=
    calc
      aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v := by rw [← mul_assoc, mul_comm]
      _ = 0 := by rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]

  rw [aeval_mul] at h_eval₂_qpp' h_eval₂_pqq'
  -- ⊢ ∃ y, y ∈ LinearMap.ker (↑(aeval f) p) ∧ ∃ z, z ∈ LinearMap.ker (↑(aeval f) q …
  refine'
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', _⟩
  rw [add_comm, mul_comm p p', mul_comm q q']
  -- ⊢ ↑(↑(aeval f) (p' * p)) v + ↑(↑(aeval f) (q' * q)) v = v
  simpa only [map_add, map_mul, aeval_one] using congr_arg (fun p : R[X] => aeval f p v) hpq'
  -- 🎉 no goals
#align polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime

end Polynomial

namespace MvPolynomial

theorem isNoetherianRing_fin_0 [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial (Fin 0) R) := by
  apply isNoetherianRing_of_ringEquiv R
  -- ⊢ R ≃+* MvPolynomial (Fin 0) R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)
  -- ⊢ MvPolynomial (Fin 0) R ≃+* R
        -- 🎉 no goals
#align mv_polynomial.is_noetherian_ring_fin_0 MvPolynomial.isNoetherianRing_fin_0

theorem isNoetherianRing_fin [IsNoetherianRing R] :
    ∀ {n : ℕ}, IsNoetherianRing (MvPolynomial (Fin n) R)
  | 0 => isNoetherianRing_fin_0
  | n + 1 =>
    @isNoetherianRing_of_ringEquiv (Polynomial (MvPolynomial (Fin n) R)) _ _ _
      (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
      (@Polynomial.isNoetherianRing (MvPolynomial (Fin n) R) _ isNoetherianRing_fin)
#align mv_polynomial.is_noetherian_ring_fin MvPolynomial.isNoetherianRing_fin

/-- The multivariate polynomial ring in finitely many variables over a noetherian ring
is itself a noetherian ring. -/
instance isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  -- ⊢ IsNoetherianRing (MvPolynomial σ R)
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin
#align mv_polynomial.is_noetherian_ring MvPolynomial.isNoetherianRing

/-- Auxiliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `Fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `MvPolynomial.noZeroDivisors` for the general case. -/
theorem noZeroDivisors_fin (R : Type u) [CommSemiring R] [NoZeroDivisors R] :
    ∀ n : ℕ, NoZeroDivisors (MvPolynomial (Fin n) R)
  | 0 => (MvPolynomial.isEmptyAlgEquiv R _).injective.noZeroDivisors _ (map_zero _) (map_mul _)
  | n + 1 =>
    haveI := noZeroDivisors_fin R n
    (MvPolynomial.finSuccEquiv R n).injective.noZeroDivisors _ (map_zero _) (map_mul _)
#align mv_polynomial.no_zero_divisors_fin MvPolynomial.noZeroDivisors_fin

/-- Auxiliary definition:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `MvPolynomial.noZeroDivisors_fin`,
and then used to prove the general case without finiteness hypotheses.
See `MvPolynomial.noZeroDivisors` for the general case. -/
theorem noZeroDivisors_of_finite (R : Type u) (σ : Type v) [CommSemiring R] [Finite σ]
    [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  -- ⊢ NoZeroDivisors (MvPolynomial σ R)
  haveI := noZeroDivisors_fin R (Fintype.card σ)
  -- ⊢ NoZeroDivisors (MvPolynomial σ R)
  exact (renameEquiv R (Fintype.equivFin σ)).injective.noZeroDivisors _ (map_zero _) (map_mul _)
  -- 🎉 no goals
#align mv_polynomial.no_zero_divisors_of_finite MvPolynomial.noZeroDivisors_of_finite

instance {R : Type u} [CommSemiring R] [NoZeroDivisors R] {σ : Type v} :
    NoZeroDivisors (MvPolynomial σ R) :=
  ⟨fun {p} {q} h => by
    obtain ⟨s, p, rfl⟩ := exists_finset_rename p
    -- ⊢ ↑(rename Subtype.val) p = 0 ∨ q = 0
    obtain ⟨t, q, rfl⟩ := exists_finset_rename q
    -- ⊢ ↑(rename Subtype.val) p = 0 ∨ ↑(rename Subtype.val) q = 0
    have :
        rename (Subtype.map id (Finset.subset_union_left s t) :
          { x // x ∈ s } → { x // x ∈ s ∪ t }) p *
        rename (Subtype.map id (Finset.subset_union_right s t) :
          { x // x ∈ t } → { x // x ∈ s ∪ t }) q =
        0 := by
      apply rename_injective _ Subtype.val_injective
      simpa using h
    letI that := MvPolynomial.noZeroDivisors_of_finite R { x // x ∈ s ∪ t }
    -- ⊢ ↑(rename Subtype.val) p = 0 ∨ ↑(rename Subtype.val) q = 0
    rw [mul_eq_zero] at this
    -- ⊢ ↑(rename Subtype.val) p = 0 ∨ ↑(rename Subtype.val) q = 0
    apply this.imp <;> intro that <;> simpa using congr_arg (rename Subtype.val) that⟩
    -- ⊢ ↑(rename (Subtype.map id (_ : s ⊆ s ∪ t))) p = 0 → ↑(rename Subtype.val) p = 0
                       -- ⊢ ↑(rename Subtype.val) p = 0
                       -- ⊢ ↑(rename Subtype.val) q = 0
                                      -- 🎉 no goals
                                      -- 🎉 no goals

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] :
    IsDomain (MvPolynomial σ R) := by
  apply @NoZeroDivisors.to_isDomain (MvPolynomial σ R) _ ?_ _
  -- ⊢ Nontrivial (MvPolynomial σ R)
  apply AddMonoidAlgebra.nontrivial
  -- 🎉 no goals

-- instance {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] :
--     IsDomain (MvPolynomial σ R)[X] := inferInstance

theorem map_mvPolynomial_eq_eval₂ {S : Type*} [CommRing S] [Finite σ] (ϕ : MvPolynomial σ R →+* S)
    (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.C) (fun s => ϕ (MvPolynomial.X s)) p := by
  cases nonempty_fintype σ
  -- ⊢ ↑ϕ p = eval₂ (RingHom.comp ϕ C) (fun s => ↑ϕ (X s)) p
  refine' Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) _
  -- ⊢ ↑ϕ (∑ v in support p, ↑(monomial v) (coeff v p)) = eval₂ (RingHom.comp ϕ C)  …
  rw [MvPolynomial.eval₂_eq', ϕ.map_sum]
  -- ⊢ ∑ x in support p, ↑ϕ (↑(monomial x) (coeff x p)) = ∑ d in support p, ↑(RingH …
  congr
  -- ⊢ (fun x => ↑ϕ (↑(monomial x) (coeff x p))) = fun d => ↑(RingHom.comp ϕ C) (co …
  ext
  -- ⊢ ↑ϕ (↑(monomial x✝) (coeff x✝ p)) = ↑(RingHom.comp ϕ C) (coeff x✝ p) * ∏ i :  …
  simp only [monomial_eq, ϕ.map_pow, ϕ.map_prod, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]
  -- 🎉 no goals
#align mv_polynomial.map_mv_polynomial_eq_eval₂ MvPolynomial.map_mvPolynomial_eq_eval₂

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
    (hcoe : ∀ m : σ →₀ ℕ, p.coeff m ∈ I.comap (C : R →+* MvPolynomial σ R)) : p ∈ I := by
  rw [as_sum p]
  -- ⊢ ∑ v in support p, ↑(monomial v) (coeff v p) ∈ I
  suffices ∀ m ∈ p.support, monomial m (MvPolynomial.coeff m p) ∈ I by
    exact Submodule.sum_mem I this
  intro m _
  -- ⊢ ↑(monomial m) (coeff m p) ∈ I
  rw [← mul_one (coeff m p), ← C_mul_monomial]
  -- ⊢ ↑C (coeff m p) * ↑(monomial m) 1 ∈ I
  suffices C (coeff m p) ∈ I by exact I.mul_mem_right (monomial m 1) this
  -- ⊢ ↑C (coeff m p) ∈ I
  simpa [Ideal.mem_comap] using hcoe m
  -- 🎉 no goals
#align mv_polynomial.mem_ideal_of_coeff_mem_ideal MvPolynomial.mem_ideal_of_coeff_mem_ideal

/-- The push-forward of an ideal `I` of `R` to `MvPolynomial σ R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      ∀ m : σ →₀ ℕ, f.coeff m ∈ I := by
  constructor
  -- ⊢ f ∈ Ideal.map C I → ∀ (m : σ →₀ ℕ), coeff m f ∈ I
  · intro hf
    -- ⊢ ∀ (m : σ →₀ ℕ), coeff m f ∈ I
    apply @Submodule.span_induction _ _ _ _ Semiring.toModule f _ _ hf
    · intro f hf n
      -- ⊢ coeff n f ∈ I
      cases' (Set.mem_image _ _ _).mp hf with x hx
      -- ⊢ coeff n f ∈ I
      rw [← hx.right, coeff_C]
      -- ⊢ (if 0 = n then x else 0) ∈ I
      by_cases h : n = 0
      -- ⊢ (if 0 = n then x else 0) ∈ I
      · simpa [h] using hx.left
        -- 🎉 no goals
      · simp [Ne.symm h]
        -- 🎉 no goals
    · simp
      -- 🎉 no goals
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
      -- 🎉 no goals
    · refine' fun f g hg n => _
      -- ⊢ coeff n (f • g) ∈ I
      rw [smul_eq_mul, coeff_mul]
      -- ⊢ ∑ x in Finsupp.antidiagonal n, coeff x.fst f * coeff x.snd g ∈ I
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
      -- 🎉 no goals
  · intro hf
    -- ⊢ f ∈ Ideal.map C I
    rw [as_sum f]
    -- ⊢ ∑ v in support f, ↑(monomial v) (coeff v f) ∈ Ideal.map C I
    suffices ∀ m ∈ f.support, monomial m (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Submodule.sum_mem _ this
    intro m _
    -- ⊢ ↑(monomial m) (coeff m f) ∈ Ideal.map C I
    rw [← mul_one (coeff m f), ← C_mul_monomial]
    -- ⊢ ↑C (coeff m f) * ↑(monomial m) 1 ∈ Ideal.map C I
    suffices C (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Ideal.mul_mem_right _ _ this
    apply Ideal.mem_map_of_mem _
    -- ⊢ coeff m f ∈ I
    exact hf m
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.mem_map_C_iff MvPolynomial.mem_map_C_iff

attribute [-instance] Ring.toNonAssocRing in
theorem ker_map (f : R →+* S) :
    RingHom.ker (map f : MvPolynomial σ R →+* MvPolynomial σ S) =
    Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  ext
  -- ⊢ x✝ ∈ RingHom.ker (map f) ↔ x✝ ∈ Ideal.map C (RingHom.ker f)
  rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  -- ⊢ (∀ (m : σ →₀ ℕ), coeff m (↑(map f) x✝) = coeff m 0) ↔ ∀ (m : σ →₀ ℕ), coeff  …
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]
  -- 🎉 no goals
#align mv_polynomial.ker_map MvPolynomial.ker_map

end MvPolynomial

section UniqueFactorizationDomain

variable {D : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] (σ)

open UniqueFactorizationMonoid

namespace Polynomial

attribute [-instance] Ring.toSemiring in
instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] := by
  haveI : NormalizationMonoid D := Inhabited.default
  -- ⊢ UniqueFactorizationMonoid D[X]
  haveI := toNormalizedGCDMonoid D
  -- ⊢ UniqueFactorizationMonoid D[X]
  exact ufm_of_gcd_of_wfDvdMonoid
  -- 🎉 no goals
#align polynomial.unique_factorization_monoid Polynomial.uniqueFactorizationMonoid

end Polynomial

namespace MvPolynomial
variable (d : ℕ)

/- Porting note: lean can come up with this instance in infinite time by resolving
the diamond with CommSemiring.toSemiring. I don't know how to inline this
attribute for a haveI in the proof of the uniqueFactorizationMonoid_of_fintype.
The proof times out if we remove these from instance graph for all of
uniqueFactorizationMonoid_of_fintype. -/
attribute [-instance] Polynomial.semiring Polynomial.commSemiring in
private instance : CancelCommMonoidWithZero (MvPolynomial (Fin d) D)[X] := by
  apply IsDomain.toCancelCommMonoidWithZero
  -- 🎉 no goals

/- Porting note: this can probably be cleaned up a little -/
private theorem uniqueFactorizationMonoid_of_fintype [Fintype σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  (renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid <| by
    induction' Fintype.card σ with d hd
    -- ⊢ UniqueFactorizationMonoid (MvPolynomial (Fin Nat.zero) D)
    · apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      -- ⊢ UniqueFactorizationMonoid D
      infer_instance
      -- 🎉 no goals
    · rw [Nat.succ_eq_add_one d]
      -- ⊢ UniqueFactorizationMonoid (MvPolynomial (Fin (d + 1)) D)
      apply @MulEquiv.uniqueFactorizationMonoid _ _ (_) (_)
      · exact (finSuccEquiv D d).toMulEquiv.symm
        -- 🎉 no goals
      · apply @Polynomial.uniqueFactorizationMonoid (MvPolynomial (Fin d) D) _ _ ?_
        -- ⊢ UniqueFactorizationMonoid (MvPolynomial (Fin d) D)
        assumption
        -- 🎉 no goals

instance (priority := 100) : UniqueFactorizationMonoid (MvPolynomial σ D) := by
  rw [iff_exists_prime_factors]
  -- ⊢ ∀ (a : MvPolynomial σ D), a ≠ 0 → ∃ f, (∀ (b : MvPolynomial σ D), b ∈ f → Pr …
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
  -- ⊢ ∃ f, (∀ (b : MvPolynomial σ D), b ∈ f → Prime b) ∧ Associated (Multiset.prod …
              -- ⊢ ∃ f, (∀ (b : MvPolynomial σ D), b ∈ f → Prime b) ∧ Associated (Multiset.prod …
  obtain ⟨w, h, u, hw⟩ :=
    iff_exists_prime_factors.1 (uniqueFactorizationMonoid_of_fintype s) a' fun h =>
      ha <| by simp [h]
  exact
    ⟨w.map (rename (↑)), fun b hb =>
      let ⟨b', hb', he⟩ := Multiset.mem_map.1 hb
      he ▸ (prime_rename_iff ↑s).2 (h b' hb'),
      Units.map (@rename s σ D _ (↑)).toRingHom.toMonoidHom u, by
      erw [Multiset.prod_hom, ← map_mul, hw]⟩

end MvPolynomial

end UniqueFactorizationDomain
