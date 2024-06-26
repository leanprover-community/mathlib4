/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.ExpChar
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain

#align_import ring_theory.polynomial.basic from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Ring-theoretic supplement of Algebra.Polynomial.

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

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

instance instCharP (p : ℕ) [h : CharP R p] : CharP R[X] p :=
  let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩

instance instExpChar (p : ℕ) [h : ExpChar R p] : ExpChar R[X] p := by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

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
#align polynomial.mem_degree_le Polynomial.mem_degreeLE

@[mono]
theorem degreeLE_mono {m n : WithBot ℕ} (H : m ≤ n) : degreeLE R m ≤ degreeLE R n := fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)
#align polynomial.degree_le_mono Polynomial.degreeLE_mono

theorem degreeLE_eq_span_X_pow [DecidableEq R] {n : ℕ} :
    degreeLE R n = Submodule.span R ↑((Finset.range (n + 1)).image fun n => (X : R[X]) ^ n) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLE.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <|
            Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le this), rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk
  apply mem_degreeLE.2
  exact
    (degree_X_pow_le _).trans (WithBot.coe_le_coe.2 <| Nat.le_of_lt_succ <| Finset.mem_range.1 hk)
set_option linter.uppercaseLean3 false in
#align polynomial.degree_le_eq_span_X_pow Polynomial.degreeLE_eq_span_X_pow

theorem mem_degreeLT {n : ℕ} {f : R[X]} : f ∈ degreeLT R n ↔ degree f < n := by
  rw [degreeLT, Submodule.mem_iInf]
  conv_lhs => intro i; rw [Submodule.mem_iInf]
  rw [degree, Finset.max_eq_sup_coe]
  rw [Finset.sup_lt_iff ?_]
  rotate_left
  · apply WithBot.bot_lt_coe
  conv_rhs =>
    simp only [mem_support_iff]
    intro b
    rw [Nat.cast_withBot, WithBot.coe_lt_coe, lt_iff_not_le, Ne, not_imp_not]
  rfl
#align polynomial.mem_degree_lt Polynomial.mem_degreeLT

@[mono]
theorem degreeLT_mono {m n : ℕ} (H : m ≤ n) : degreeLT R m ≤ degreeLT R n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)
#align polynomial.degree_lt_mono Polynomial.degreeLT_mono

theorem degreeLT_eq_span_X_pow [DecidableEq R] {n : ℕ} :
    degreeLT R n = Submodule.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X]) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <| Finset.mem_image.2 ⟨_, Finset.mem_range.2 this, rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk
  apply mem_degreeLT.2
  exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.2 <| Finset.mem_range.1 hk)
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
    dsimp
    rw [coeff_add]
  map_smul' x p := by
    ext
    dsimp
    rw [coeff_smul]
    rfl
  left_inv := by
    rintro ⟨p, hp⟩
    ext1
    simp only [Submodule.coe_mk]
    by_cases hp0 : p = 0
    · subst hp0
      simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
    rw [mem_degreeLT, degree_eq_natDegree hp0, Nat.cast_lt] at hp
    conv_rhs => rw [p.as_sum_range' n hp, ← Fin.sum_univ_eq_sum_range]
  right_inv f := by
    ext i
    simp only [finset_sum_coeff, Submodule.coe_mk]
    rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
    · rintro j - hji
      rw [coeff_monomial, if_neg]
      rwa [← Fin.ext_iff]
    · intro h
      exact (h (Finset.mem_univ _)).elim
#align polynomial.degree_lt_equiv Polynomial.degreeLTEquiv

-- Porting note: removed @[simp] as simp can prove this
theorem degreeLTEquiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) :
    degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mk_eq_zero]
#align polynomial.degree_lt_equiv_eq_zero_iff_eq_zero Polynomial.degreeLTEquiv_eq_zero_iff_eq_zero

theorem eval_eq_sum_degreeLTEquiv {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) (x : R) :
    p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : ℕ) := by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm
#align polynomial.eval_eq_sum_degree_lt_equiv Polynomial.eval_eq_sum_degreeLTEquiv

theorem degreeLT_succ_eq_degreeLE {n : ℕ} : degreeLT R (n + 1) = degreeLE R n := by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ]

/-- For every polynomial `p` in the span of a set `s : Set R[X]`, there exists a polynomial of
  `p' ∈ s` with higher degree. See also `Polynomial.exists_degree_le_of_mem_span_of_finite`. -/
theorem exists_degree_le_of_mem_span {s : Set R[X]} {p : R[X]}
    (hs : s.Nonempty) (hp : p ∈ Submodule.span R s) :
    ∃ p' ∈ s, degree p ≤ degree p' := by
  by_contra! h
  by_cases hp_zero : p = 0
  · rw [hp_zero, degree_zero] at h
    rcases hs with ⟨x, hx⟩
    exact not_lt_bot (h x hx)
  · have : p ∈ degreeLT R (natDegree p) := by
      refine (Submodule.span_le.mpr fun p' p'_mem => ?_) hp
      rw [SetLike.mem_coe, mem_degreeLT, Nat.cast_withBot]
      exact lt_of_lt_of_le (h p' p'_mem) degree_le_natDegree
    rwa [mem_degreeLT, Nat.cast_withBot, degree_eq_natDegree hp_zero,
      Nat.cast_withBot, lt_self_iff_false] at this

/-- A stronger version of `Polynomial.exists_degree_le_of_mem_span` under the assumption that the
  set `s : R[X]` is finite. There exists a polynomial `p' ∈ s` whose degree dominates the degree of
  every element of `p ∈ span R s`-/
theorem exists_degree_le_of_mem_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty) :
    ∃ p' ∈ s, ∀ (p : R[X]), p ∈ Submodule.span R s → degree p ≤ degree p' := by
  rcases Set.Finite.exists_maximal_wrt degree s s_fin hs with ⟨a, has, hmax⟩
  refine ⟨a, has, fun p hp => ?_⟩
  rcases exists_degree_le_of_mem_span hs hp with ⟨p', hp'⟩
  by_cases h : degree a ≤ degree p'
  · rw [← hmax p' hp'.left h] at hp'; exact hp'.right
  · exact le_trans hp'.right (not_le.mp h).le

/-- The span of every finite set of polynomials is contained in a `degreeLE n` for some `n`. -/
theorem span_le_degreeLE_of_finite {s : Set R[X]} (s_fin : s.Finite) :
    ∃ n : ℕ, Submodule.span R s ≤ degreeLE R n := by
  by_cases s_emp : s.Nonempty
  · rcases exists_degree_le_of_mem_span_of_finite s_fin s_emp with ⟨p', _, hp'max⟩
    exact ⟨natDegree p', fun p hp => mem_degreeLE.mpr ((hp'max _ hp).trans degree_le_natDegree)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at s_emp
    rw [s_emp, Submodule.span_empty]
    exact ⟨0, bot_le⟩

/-- The span of every finite set of polynomials is contained in a `degreeLT n` for some `n`. -/
theorem span_of_finite_le_degreeLT {s : Set R[X]} (s_fin : s.Finite) :
    ∃ n : ℕ, Submodule.span R s ≤ degreeLT R n := by
  rcases span_le_degreeLE_of_finite s_fin with ⟨n, _⟩
  exact ⟨n + 1, by rwa [degreeLT_succ_eq_degreeLE]⟩

/-- If `R` is a nontrivial ring, the polynomials `R[X]` are not finite as an `R`-module. When `R` is
a field, this is equivalent to `R[X]` being an infinite-dimensional vector space over `R`.  -/
theorem not_finite [Nontrivial R] : ¬ Module.Finite R R[X] := by
  rw [Module.finite_def, Submodule.fg_def]
  push_neg
  intro s hs contra
  rcases span_le_degreeLE_of_finite hs with ⟨n,hn⟩
  have : ((X : R[X]) ^ (n + 1)) ∈ Polynomial.degreeLE R ↑n := by
    rw [contra] at hn
    exact hn Submodule.mem_top
  rw [mem_degreeLE, degree_X_pow, Nat.cast_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  exact one_ne_zero this

/-- The finset of nonzero coefficients of a polynomial. -/
def coeffs (p : R[X]) : Finset R :=
  letI := Classical.decEq R
  Finset.image (fun n => p.coeff n) p.support
#align polynomial.frange Polynomial.coeffs

@[deprecated (since := "2024-05-17")] noncomputable alias frange := coeffs

theorem coeffs_zero : coeffs (0 : R[X]) = ∅ :=
  rfl
#align polynomial.frange_zero Polynomial.coeffs_zero

@[deprecated (since := "2024-05-17")] alias frange_zero := coeffs_zero

theorem mem_coeffs_iff {p : R[X]} {c : R} : c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [coeffs, eq_comm, (Finset.mem_image)]
#align polynomial.mem_frange_iff Polynomial.mem_coeffs_iff

@[deprecated (since := "2024-05-17")] alias mem_frange_iff := mem_coeffs_iff

theorem coeffs_one : coeffs (1 : R[X]) ⊆ {1} := by
  classical
    simp_rw [coeffs, Finset.image_subset_iff]
    simp_all [coeff_one]
#align polynomial.frange_one Polynomial.coeffs_one

@[deprecated (since := "2024-05-17")] alias frange_one := coeffs_one

theorem coeff_mem_coeffs (p : R[X]) (n : ℕ) (h : p.coeff n ≠ 0) : p.coeff n ∈ p.coeffs := by
  classical
  simp only [coeffs, exists_prop, mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩
#align polynomial.coeff_mem_frange Polynomial.coeff_mem_coeffs

@[deprecated (since := "2024-05-17")] alias coeff_mem_frange := coeff_mem_coeffs

theorem geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
    (∑ i ∈ range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : ℕ => (n.choose (i + 1) : R[X]) * X ^ i := by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finset_sum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i, if_pos rfl]
    · simp (config := { contextual := true }) only [@eq_comm _ i, if_false, eq_self_iff_true,
        imp_true_iff]
    · simp (config := { contextual := true }) only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, eq_self_iff_true, if_true, imp_true_iff]
  induction' n with n ih generalizing i
  · dsimp; simp only [zero_comp, coeff_zero, Nat.cast_zero]
  · simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
    Nat.cast_add, coeff_X_add_one_pow]
set_option linter.uppercaseLean3 false in
#align polynomial.geom_sum_X_comp_X_add_one_eq_sum Polynomial.geom_sum_X_comp_X_add_one_eq_sum

theorem Monic.geom_sum {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, P ^ i).Monic := by
  nontriviality R
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [geom_sum_succ']
  refine (hP.pow _).add_of_left ?_
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    simp only [Nat.cast_lt, hP.natDegree_pow]
    intro k
    exact nsmul_lt_nsmul_left hdeg
  · rw [bot_lt_iff_ne_bot, Ne, degree_eq_bot]
    exact (hP.pow _).ne_zero
#align polynomial.monic.geom_sum Polynomial.Monic.geom_sum

theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn
#align polynomial.monic.geom_sum' Polynomial.Monic.geom_sum'

theorem monic_geom_sum_X {n : ℕ} (hn : n ≠ 0) : (∑ i ∈ range n, (X : R[X]) ^ i).Monic := by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]
set_option linter.uppercaseLean3 false in
#align polynomial.monic_geom_sum_X Polynomial.monic_geom_sum_X

end Semiring

section Ring

variable [Ring R]

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.coeffs : Set R)) :=
  ∑ i ∈ p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_coeffs _ H)⟩ :
        Subring.closure (↑p.coeffs : Set R))
#align polynomial.restriction Polynomial.restriction

@[simp]
theorem coeff_restriction {p : R[X]} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := by
  classical
  simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl
#align polynomial.coeff_restriction Polynomial.coeff_restriction

-- Porting note: removed @[simp] as simp can prove this
theorem coeff_restriction' {p : R[X]} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n :=
  coeff_restriction
#align polynomial.coeff_restriction' Polynomial.coeff_restriction'

@[simp]
theorem support_restriction (p : R[X]) : support (restriction p) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩
#align polynomial.support_restriction Polynomial.support_restriction

@[simp]
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubring_apply, coeff_restriction]
#align polynomial.map_restriction Polynomial.map_restriction

@[simp]
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]
#align polynomial.degree_restriction Polynomial.degree_restriction

@[simp]
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [natDegree]
#align polynomial.nat_degree_restriction Polynomial.natDegree_restriction

@[simp]
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩
#align polynomial.monic_restriction Polynomial.monic_restriction

@[simp]
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]
#align polynomial.restriction_zero Polynomial.restriction_zero

@[simp]
theorem restriction_one : restriction (1 : R[X]) = 1 :=
  ext fun i => Subtype.eq <| by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl
#align polynomial.restriction_one Polynomial.restriction_one

variable [Semiring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.coeffs : Set R)))) x p.restriction := by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coeSubtype]
#align polynomial.eval₂_restriction Polynomial.eval₂_restriction

section ToSubring

variable (p : R[X]) (T : Subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def toSubring (hp : (↑p.coeffs : Set R) ⊆ T) : T[X] :=
  ∑ i ∈ p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs _ H)⟩ : T)
#align polynomial.to_subring Polynomial.toSubring

variable (hp : (↑p.coeffs : Set R) ⊆ T)

@[simp]
theorem coeff_toSubring {n : ℕ} : ↑(coeff (toSubring p T hp) n) = coeff p n := by
  classical
  simp only [toSubring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl
#align polynomial.coeff_to_subring Polynomial.coeff_toSubring

-- Porting note: removed @[simp] as simp can prove this
theorem coeff_toSubring' {n : ℕ} : (coeff (toSubring p T hp) n).1 = coeff p n :=
  coeff_toSubring _ _ hp
#align polynomial.coeff_to_subring' Polynomial.coeff_toSubring'

@[simp]
theorem support_toSubring : support (toSubring p T hp) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩
#align polynomial.support_to_subring Polynomial.support_toSubring

@[simp]
theorem degree_toSubring : (toSubring p T hp).degree = p.degree := by simp [degree]
#align polynomial.degree_to_subring Polynomial.degree_toSubring

@[simp]
theorem natDegree_toSubring : (toSubring p T hp).natDegree = p.natDegree := by simp [natDegree]
#align polynomial.nat_degree_to_subring Polynomial.natDegree_toSubring

@[simp]
theorem monic_toSubring : Monic (toSubring p T hp) ↔ Monic p := by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩
#align polynomial.monic_to_subring Polynomial.monic_toSubring

@[simp]
theorem toSubring_zero : toSubring (0 : R[X]) T (by simp [coeffs]) = 0 := by
  ext i
  simp
#align polynomial.to_subring_zero Polynomial.toSubring_zero

@[simp]
theorem toSubring_one :
    toSubring (1 : R[X]) T
        (Set.Subset.trans coeffs_one <| Finset.singleton_subset_set_iff.2 T.one_mem) =
      1 :=
  ext fun i => Subtype.eq <| by
    rw [coeff_toSubring', coeff_one, coeff_one, apply_ite Subtype.val, ZeroMemClass.coe_zero,
      OneMemClass.coe_one]
#align polynomial.to_subring_one Polynomial.toSubring_one

@[simp]
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p := by
  ext n
  simp [coeff_map]
#align polynomial.map_to_subring Polynomial.map_toSubring

end ToSubring

variable (T : Subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def ofSubring (p : T[X]) : R[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i : R)
#align polynomial.of_subring Polynomial.ofSubring

theorem coeff_ofSubring (p : T[X]) (n : ℕ) : coeff (ofSubring T p) n = (coeff p n : T) := by
  simp only [ofSubring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    ite_eq_right_iff, Ne, ite_not, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h, ZeroMemClass.coe_zero]
#align polynomial.coeff_of_subring Polynomial.coeff_ofSubring

@[simp]
theorem coeffs_ofSubring {p : T[X]} : (↑(p.ofSubring T).coeffs : Set R) ⊆ T := by
  classical
  intro i hi
  simp only [coeffs, Set.mem_image, mem_support_iff, Ne, Finset.mem_coe,
    (Finset.coe_image)] at hi
  rcases hi with ⟨n, _, h'n⟩
  rw [← h'n, coeff_ofSubring]
  exact Subtype.mem (coeff p n : T)
#align polynomial.frange_of_subring Polynomial.coeffs_ofSubring

@[deprecated (since := "2024-05-17")] alias frange_ofSubring := coeffs_ofSubring

end Ring

section CommRing

variable [CommRing R]

section ModByMonic

variable {q : R[X]}

theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)
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
    exact I.mul_mem_left _ H
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
  · intro hf
    apply @Submodule.span_induction _ _ _ _ _ f _ _ hf
    · intro f hf n
      cases' (Set.mem_image _ _ _).mp hf with x hx
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine fun f g hg n => ?_
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [← sum_monomial_eq f]
    refine (I.map C : Ideal R[X]).sum_mem fun n _ => ?_
    simp only [← C_mul_X_pow_eq_monomial, ne_eq]
    rw [mul_comm]
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))
set_option linter.uppercaseLean3 false in
#align ideal.mem_map_C_iff Ideal.mem_map_C_iff

theorem _root_.Polynomial.ker_mapRingHom (f : R →+* S) :
    LinearMap.ker (Polynomial.mapRingHom f).toSemilinearMap = f.ker.map (C : R →+* R[X]) := by
  ext
  simp only [LinearMap.mem_ker, RingHom.toSemilinearMap_apply, coe_mapRingHom]
  rw [mem_map_C_iff, Polynomial.ext_iff]
  simp_rw [RingHom.mem_ker f]
  simp
#align polynomial.ker_map_ring_hom Polynomial.ker_mapRingHom

variable (I : Ideal R[X])

theorem mem_leadingCoeffNth (n : ℕ) (x) :
    x ∈ I.leadingCoeffNth n ↔ ∃ p ∈ I, degree p ≤ n ∧ p.leadingCoeff = x := by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero, eq_comm]
      exact coeff_eq_zero_of_degree_lt hpdeg
    · refine ⟨p, hpI, le_of_eq hpdeg, ?_⟩
      rw [Polynomial.leadingCoeff, natDegree, hpdeg, Nat.cast_withBot, WithBot.unbot'_coe]
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine ⟨p * X ^ (n - natDegree p), ⟨?_, I.mul_mem_right _ hpI⟩, ?_⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      rw [← Nat.cast_add, this]
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), this]
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
  simp only [SetLike.mem_coe, mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  refine le_trans (add_le_add hpdeg (degree_X_pow_le _)) ?_
  rw [← Nat.cast_add, add_tsub_cancel_of_le H]
#align ideal.leading_coeff_nth_mono Ideal.leadingCoeffNth_mono

theorem mem_leadingCoeff (x) : x ∈ I.leadingCoeff ↔ ∃ p ∈ I, Polynomial.leadingCoeff p = x := by
  rw [leadingCoeff, Submodule.mem_iSup_of_directed]
  · simp only [mem_leadingCoeffNth]
    constructor
    · rintro ⟨i, p, hpI, _, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
  intro i j
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
      obtain rfl : i + j = k := mem_antidiagonal.mp e
      apply Ideal.pow_le_pow_right add_tsub_add_le_tsub_add_tsub
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
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p ≠ 0 := right_ne_zero_of_mul_eq_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul, congr_arg degree hp, degree_one, Nat.WithBot.lt_zero_iff, degree_eq_bot] at this
  exact hp0 this
#align ideal.polynomial_not_is_field Ideal.polynomial_not_isField

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : C x ∈ I) : x = 0 := by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert I.mul_mem_left (C y) hx
  rw [← C.map_mul, hR.mul_comm y x, hy, RingHom.map_one]
#align ideal.eq_zero_of_constant_mem_of_maximal Ideal.eq_zero_of_constant_mem_of_maximal

end Ring

section CommRing

variable [CommRing R]

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem isPrime_map_C_iff_isPrime (P : Ideal R) :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) ↔ IsPrime P := by
  -- Note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  · intro H
    have := comap_isPrime C (map C P)
    convert this using 1
    ext x
    simp only [mem_comap, mem_map_C_iff]
    constructor
    · rintro h (- | n)
      · rwa [coeff_C_zero]
      · simp only [coeff_C_ne_zero (Nat.succ_ne_zero _), Submodule.zero_mem]
    · intro h
      simpa only [coeff_C_zero] using h 0
  · intro h
    constructor
    · rw [Ne, eq_top_iff_one, mem_map_C_iff, not_forall]
      use 0
      rw [coeff_one_zero, ← eq_top_iff_one]
      exact h.1
    · intro f g
      simp only [mem_map_C_iff]
      contrapose!
      rintro ⟨hf, hg⟩
      classical
        let m := Nat.find hf
        let n := Nat.find hg
        refine ⟨m + n, ?_⟩
        rw [coeff_mul, ← Finset.insert_erase ((Finset.mem_antidiagonal (a := (m,n))).mpr rfl),
          Finset.sum_insert (Finset.not_mem_erase _ _), (P.add_mem_iff_left _).not]
        · apply mt h.2
          rw [not_or]
          exact ⟨Nat.find_spec hf, Nat.find_spec hg⟩
        apply P.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_erase, Finset.mem_antidiagonal] at hij
        simp only [Ne, Prod.mk.inj_iff, not_and_or] at hij
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
  letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _
#align ideal.is_fg_degree_le Ideal.is_fg_degreeLE

end CommRing

end Ideal

variable {σ : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

theorem prime_C_iff : Prime (C r) ↔ Prime r :=
  ⟨comap_prime C (evalRingHom (0 : R)) fun r => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      apply Ideal.isPrime_map_C_of_isPrime hr
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩
set_option linter.uppercaseLean3 false in
#align polynomial.prime_C_iff Polynomial.prime_C_iff

end Polynomial

namespace MvPolynomial

private theorem prime_C_iff_of_fintype {R : Type u} (σ : Type v) {r : R} [CommRing R] [Fintype σ] :
    Prime (C r : MvPolynomial σ R) ↔ Prime r := by
  rw [(renameEquiv R (Fintype.equivFin σ)).toMulEquiv.prime_iff]
  convert_to Prime (C r) ↔ _
  · congr!
    apply rename_C
  · symm
    induction' Fintype.card σ with d hd
    · exact (isEmptyAlgEquiv R (Fin 0)).toMulEquiv.symm.prime_iff
    · rw [hd, ← Polynomial.prime_C_iff]
      convert (finSuccEquiv R d).toMulEquiv.symm.prime_iff (p := Polynomial.C (C r))
      rw [← finSuccEquiv_comp_C_eq_C]; rfl

theorem prime_C_iff : Prime (C r : MvPolynomial σ R) ↔ Prime r :=
  ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
    ⟨fun h => hr.1 <| by
        rw [← C_inj, h]
        simp,
      fun h =>
      hr.2.1 <| by
        rw [← constantCoeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw [← algebraMap_eq] at hd
      have : algebraMap R _ r ∣ a' * b' := by
        convert killCompl Subtype.coe_injective |>.toRingHom.map_dvd hd <;> simp
      rw [← rename_C ((↑) : s → σ)]
      let f := (rename (R := R) ((↑) : s → σ)).toRingHom
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp f.map_dvd f.map_dvd⟩⟩
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
        simp only [eqv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C,
          AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
          AlgEquiv.coe_trans, Function.comp_apply, MvPolynomial.sumAlgEquiv_symm_apply,
          iterToSum_C_C, renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply]
      · intro
        simp only [eqv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
          AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp,
          AlgEquiv.coe_trans, Function.comp_apply, MvPolynomial.sumAlgEquiv_symm_apply,
          iterToSum_C_X, renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply, Sum.swap_inr,
          Equiv.Set.sumCompl_apply_inl]
    apply_fun (· p) at this
    simp_rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [← prime_C_iff, eqv.toMulEquiv.prime_iff, this]
    simp only [MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AlgEquiv.trans_apply,
      MvPolynomial.sumAlgEquiv_symm_apply, renameEquiv_apply, Equiv.coe_trans, Equiv.sumComm_apply,
      AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_trans, Function.comp_apply]
#align mv_polynomial.prime_rename_iff MvPolynomial.prime_rename_iff

end MvPolynomial

end Prime

namespace Polynomial

instance (priority := 100) wfDvdMonoid {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] :
    WfDvdMonoid R[X] where
  wellFounded_dvdNotUnit := by
    classical
      refine
        RelHomClass.wellFounded
          (⟨fun p : R[X] =>
              ((if p = 0 then ⊤ else ↑p.degree : WithTop (WithBot ℕ)), p.leadingCoeff), ?_⟩ :
            DvdNotUnit →r Prod.Lex (· < ·) DvdNotUnit)
          (wellFounded_lt.prod_lex ‹WfDvdMonoid R›.wellFounded_dvdNotUnit)
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
        refine Prod.Lex.right _ ⟨?_, ⟨c.leadingCoeff, fun unit_c => not_unit_c ?_, rfl⟩⟩
        · rwa [Ne, Polynomial.leadingCoeff_eq_zero]
        rw [Polynomial.isUnit_iff, Polynomial.eq_C_of_degree_eq_zero hdeg]
        use c.leadingCoeff, unit_c
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]; rfl
      · apply Prod.Lex.left
        rw [Polynomial.degree_eq_natDegree cne0] at *
        rw [WithTop.coe_lt_coe, Polynomial.degree_eq_natDegree ane0, ← Nat.cast_add, Nat.cast_lt]
        exact lt_add_of_pos_right _ (Nat.pos_of_ne_zero fun h => hdeg (h.symm ▸ WithBot.coe_zero))

end Polynomial

/-- Hilbert basis theorem: a polynomial ring over a noetherian ring is a noetherian ring. -/
protected theorem Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M :=
        WellFounded.min (isNoetherian_iff_wellFounded.1 (by infer_instance))
          (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M ∈ Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := fun k =>
        Or.casesOn (le_or_lt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h x hx =>
          Classical.by_contradiction fun hxm =>
            haveI : IsNoetherian R R := inst
            have : ¬M < I.leadingCoeffNth k := by
              refine WellFounded.not_lt_min (wellFounded_submodule_gt R R) _ _ ?_; exact ⟨k, rfl⟩
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : ∀ {x}, x ∈ I.degreeLE N → x ∈ Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun hx =>
          Submodule.span_induction hx (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ => Ideal.add_mem _) fun c f hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s, le_antisymm (Ideal.span_le.2 fun x hx =>
          have : x ∈ I.degreeLE N := hs ▸ Submodule.subset_span hx
          this.2) <| by
        have : Submodule.span R[X] ↑s = Ideal.span ↑s := rfl
        rw [this]
        intro p hp
        generalize hn : p.natDegree = k
        induction' k using Nat.strong_induction_on with k ih generalizing p
        rcases le_or_lt k N with h | h
        · subst k
          refine hs2 ⟨Polynomial.mem_degreeLE.2
            (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h), hp⟩
        · have hp0 : p ≠ 0 := by
            rintro rfl
            cases hn
            exact Nat.not_lt_zero _ h
          have : (0 : R) ≠ 1 := by
            intro h
            apply hp0
            ext i
            refine (mul_one _).symm.trans ?_
            rw [← h, mul_zero]
            rfl
          haveI : Nontrivial R := ⟨⟨0, 1, this⟩⟩
          have : p.leadingCoeff ∈ I.leadingCoeffNth N := by
            rw [HN]
            exact hm2 k ((I.mem_leadingCoeffNth _ _).2
              ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
          rw [I.mem_leadingCoeffNth] at this
          rcases this with ⟨q, hq, hdq, hlqp⟩
          have hq0 : q ≠ 0 := by
            intro H
            rw [← Polynomial.leadingCoeff_eq_zero] at H
            rw [hlqp, Polynomial.leadingCoeff_eq_zero] at H
            exact hp0 H
          have h1 : p.degree = (q * Polynomial.X ^ (k - q.natDegree)).degree := by
            rw [Polynomial.degree_mul', Polynomial.degree_X_pow]
            · rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
              rw [← Nat.cast_add, add_tsub_cancel_of_le, hn]
              · refine le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
            rw [Polynomial.leadingCoeff_X_pow, mul_one]
            exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
          have h2 : p.leadingCoeff = (q * Polynomial.X ^ (k - q.natDegree)).leadingCoeff := by
            rw [← hlqp, Polynomial.leadingCoeff_mul_X_pow]
          have := Polynomial.degree_sub_lt h1 hp0 h2
          rw [Polynomial.degree_eq_natDegree hp0] at this
          rw [← sub_add_cancel p (q * Polynomial.X ^ (k - q.natDegree))]
          convert (Ideal.span ↑s).add_mem _ ((Ideal.span (s : Set R[X])).mul_mem_right _ _)
          · by_cases hpq : p - q * Polynomial.X ^ (k - q.natDegree) = 0
            · rw [hpq]
              exact Ideal.zero_mem _
            refine ih _ ?_ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
            rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_lt, hn] at this
          exact hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩⟩⟩
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
    exact natDegree_le_of_degree_le hf
#align polynomial.exists_irreducible_of_nat_degree_pos Polynomial.exists_irreducible_of_natDegree_pos

theorem exists_irreducible_of_natDegree_ne_zero {R : Type u} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] {f : R[X]} (hf : f.natDegree ≠ 0) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_natDegree_pos <| Nat.pos_of_ne_zero hf
#align polynomial.exists_irreducible_of_nat_degree_ne_zero Polynomial.exists_irreducible_of_natDegree_ne_zero

theorem linearIndependent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : ℕ => (f ^ n) v) ↔ ∀ p : R[X], aeval f p v = 0 → p = 0 := by
  rw [linearIndependent_iff]
  simp only [Finsupp.total_apply, aeval_endomorphism, forall_iff_forall_finsupp, Sum, support,
    coeff, ofFinsupp_eq_zero]
  exact Iff.rfl
#align polynomial.linear_independent_powers_iff_aeval Polynomial.linearIndependent_powers_iff_aeval

attribute [-instance] Ring.toNonAssocRing

theorem disjoint_ker_aeval_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm
#align polynomial.disjoint_ker_aeval_of_coprime Polynomial.disjoint_ker_aeval_of_coprime

theorem sup_aeval_range_eq_top_of_coprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [LinearMap.mul_apply, aeval_mul]⟩
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'
#align polynomial.sup_aeval_range_eq_top_of_coprime Polynomial.sup_aeval_range_eq_top_of_coprime

theorem sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) ≤ LinearMap.ker (aeval f (p * q)) := by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm, aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hx, LinearMap.map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul, LinearMap.mul_apply, LinearMap.mem_ker.1 hy, LinearMap.map_zero]
  rw [LinearMap.mem_ker, ← hxy, LinearMap.map_add, h_eval_x, h_eval_y, add_zero]
#align polynomial.sup_ker_aeval_le_ker_aeval_mul Polynomial.sup_ker_aeval_le_ker_aeval_mul

theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M →ₗ[R] M) {p q : R[X]}
    (hpq : IsCoprime p q) :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) = LinearMap.ker (aeval f (p * q)) := by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
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
  refine
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', ?_⟩
  rw [add_comm, mul_comm p p', mul_comm q q']
  simpa only [map_add, map_mul, aeval_one] using congr_arg (fun p : R[X] => aeval f p v) hpq'
#align polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime

end Polynomial

namespace MvPolynomial

lemma aeval_natDegree_le {R : Type*} [CommSemiring R] {m n : ℕ}
    (F : MvPolynomial σ R) (hF : F.totalDegree ≤ m)
    (f : σ → Polynomial R) (hf : ∀ i, (f i).natDegree ≤ n) :
    (MvPolynomial.aeval f F).natDegree ≤ m * n := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro d hd
  simp_rw [Function.comp_apply, ← C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have : ∑ i ∈ d.support, (d i) * n ≤ m * n := by
    rw [← Finset.sum_mul]
    apply mul_le_mul' (.trans _ hF) le_rfl
    rw [MvPolynomial.totalDegree]
    exact Finset.le_sup_of_le hd le_rfl
  apply (Finset.sum_le_sum _).trans this
  rintro i -
  apply Polynomial.natDegree_pow_le.trans
  exact mul_le_mul' le_rfl (hf i)

theorem isNoetherianRing_fin_0 [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial (Fin 0) R) := by
  apply isNoetherianRing_of_ringEquiv R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)
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
  haveI := noZeroDivisors_fin R (Fintype.card σ)
  exact (renameEquiv R (Fintype.equivFin σ)).injective.noZeroDivisors _ (map_zero _) (map_mul _)
#align mv_polynomial.no_zero_divisors_of_finite MvPolynomial.noZeroDivisors_of_finite

instance {R : Type u} [CommSemiring R] [NoZeroDivisors R] {σ : Type v} :
    NoZeroDivisors (MvPolynomial σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {p q} h := by
    obtain ⟨s, p, q, rfl, rfl⟩ := exists_finset_rename₂ p q
    let _nzd := MvPolynomial.noZeroDivisors_of_finite R s
    have : p * q = 0 := by
      apply rename_injective _ Subtype.val_injective
      simpa using h
    rw [mul_eq_zero] at this
    apply this.imp <;> rintro rfl <;> simp

/-- The multivariate polynomial ring over an integral domain is an integral domain. -/
instance isDomain {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] :
    IsDomain (MvPolynomial σ R) := by
  apply @NoZeroDivisors.to_isDomain (MvPolynomial σ R) _ ?_ _
  apply AddMonoidAlgebra.nontrivial

-- instance {R : Type u} {σ : Type v} [CommRing R] [IsDomain R] :
--     IsDomain (MvPolynomial σ R)[X] := inferInstance

theorem map_mvPolynomial_eq_eval₂ {S : Type*} [CommRing S] [Finite σ] (ϕ : MvPolynomial σ R →+* S)
    (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.C) (fun s => ϕ (MvPolynomial.X s)) p := by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq', map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]
#align mv_polynomial.map_mv_polynomial_eq_eval₂ MvPolynomial.map_mvPolynomial_eq_eval₂

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
    (hcoe : ∀ m : σ →₀ ℕ, p.coeff m ∈ I.comap (C : R →+* MvPolynomial σ R)) : p ∈ I := by
  rw [as_sum p]
  suffices ∀ m ∈ p.support, monomial m (MvPolynomial.coeff m p) ∈ I by
    exact Submodule.sum_mem I this
  intro m _
  rw [← mul_one (coeff m p), ← C_mul_monomial]
  suffices C (coeff m p) ∈ I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] using hcoe m
#align mv_polynomial.mem_ideal_of_coeff_mem_ideal MvPolynomial.mem_ideal_of_coeff_mem_ideal

/-- The push-forward of an ideal `I` of `R` to `MvPolynomial σ R` via inclusion
 is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      ∀ m : σ →₀ ℕ, f.coeff m ∈ I := by
  classical
  constructor
  · intro hf
    apply @Submodule.span_induction _ _ _ _ Semiring.toModule f _ _ hf
    · intro f hf n
      cases' (Set.mem_image _ _ _).mp hf with x hx
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · exact fun f g hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine fun f g hg n => ?_
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [as_sum f]
    suffices ∀ m ∈ f.support, monomial m (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Submodule.sum_mem _ this
    intro m _
    rw [← mul_one (coeff m f), ← C_mul_monomial]
    suffices C (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Ideal.mul_mem_right _ _ this
    apply Ideal.mem_map_of_mem _
    exact hf m
set_option linter.uppercaseLean3 false in
#align mv_polynomial.mem_map_C_iff MvPolynomial.mem_map_C_iff

attribute [-instance] Ring.toNonAssocRing in
theorem ker_map (f : R →+* S) :
    RingHom.ker (map f : MvPolynomial σ R →+* MvPolynomial σ S) =
    Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  ext
  rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]
#align mv_polynomial.ker_map MvPolynomial.ker_map

end MvPolynomial

section UniqueFactorizationDomain

variable {D : Type u} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] (σ)

open UniqueFactorizationMonoid

namespace Polynomial

instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] := by
  letI := Classical.arbitrary (NormalizedGCDMonoid D)
  exact ufm_of_decomposition_of_wfDvdMonoid
#align polynomial.unique_factorization_monoid Polynomial.uniqueFactorizationMonoid

/-- If `D` is a unique factorization domain, `f` is a non-zero polynomial in `D[X]`, then `f` has
only finitely many monic factors.
(Note that its factors up to unit may be more than monic factors.)
See also `UniqueFactorizationMonoid.fintypeSubtypeDvd`. -/
noncomputable def fintypeSubtypeMonicDvd (f : D[X]) (hf : f ≠ 0) :
    Fintype { g : D[X] // g.Monic ∧ g ∣ f } := by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y ≠ 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G → H := fun x ↦ ⟨Associates.mk x.1, Associates.mk_dvd_mk.2 x.2.2⟩
  refine Fintype.ofInjective i fun x y heq ↦ ?_
  rw [Subtype.mk.injEq] at heq ⊢
  exact eq_of_monic_of_associated x.2.1 y.2.1 (Associates.mk_eq_mk_iff_associated.mp heq)

end Polynomial

namespace MvPolynomial
variable (d : ℕ)

private theorem uniqueFactorizationMonoid_of_fintype [Fintype σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  (renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid <| by
    induction' Fintype.card σ with d hd
    · apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    · apply (finSuccEquiv D d).toMulEquiv.symm.uniqueFactorizationMonoid
      exact Polynomial.uniqueFactorizationMonoid

instance (priority := 100) uniqueFactorizationMonoid :
    UniqueFactorizationMonoid (MvPolynomial σ D) := by
  rw [iff_exists_prime_factors]
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
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

/-- A polynomial over a field which is not a unit must have a monic irreducible factor.
See also `WfDvdMonoid.exists_irreducible_factor`. -/
theorem Polynomial.exists_monic_irreducible_factor {F : Type*} [Field F] (f : F[X])
    (hu : ¬IsUnit f) : ∃ g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f := by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
  have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _ <|
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨_, monic_mul_leadingCoeff_inv hi.ne_zero, ha.irreducible hi, ha.dvd_iff_dvd_left.1 hf⟩
