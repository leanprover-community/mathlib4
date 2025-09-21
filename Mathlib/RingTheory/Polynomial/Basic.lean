/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Ring-theoretic supplement of Algebra.Polynomial.

## Main results
* `MvPolynomial.isDomain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `Polynomial.isNoetherianRing`:
  Hilbert basis theorem, that if a ring is Noetherian then so is its polynomial ring.
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

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
def degreeLT (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R k)

variable {R}

theorem mem_degreeLE {n : WithBot ℕ} {f : R[X]} : f ∈ degreeLE R n ↔ degree f ≤ n := by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl

@[mono]
theorem degreeLE_mono {m n : WithBot ℕ} (H : m ≤ n) : degreeLE R m ≤ degreeLE R n := fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)

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
    rw [Nat.cast_withBot, WithBot.coe_lt_coe, lt_iff_not_ge, Ne, not_imp_not]
  rfl

@[mono]
theorem degreeLT_mono {m n : ℕ} (H : m ≤ n) : degreeLT R m ≤ degreeLT R n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)

theorem degreeLT_eq_span_X_pow [DecidableEq R] {n : ℕ} :
    degreeLT R n = Submodule.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X]) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine Submodule.smul_mem _ _ (Submodule.subset_span <| by grind)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk
  apply mem_degreeLT.2
  exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.2 <| Finset.mem_range.1 hk)

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
    simp only
    by_cases hp0 : p = 0
    · subst hp0
      simp only [coeff_zero, LinearMap.map_zero, Finset.sum_const_zero]
    rw [mem_degreeLT, degree_eq_natDegree hp0, Nat.cast_lt] at hp
    conv_rhs => rw [p.as_sum_range' n hp, ← Fin.sum_univ_eq_sum_range]
  right_inv f := by
    ext i
    simp only [finset_sum_coeff]
    rw [Finset.sum_eq_single i, coeff_monomial, if_pos rfl]
    · rintro j - hji
      rw [coeff_monomial, if_neg]
      rwa [← Fin.ext_iff]
    · intro h
      exact (h (Finset.mem_univ _)).elim

theorem degreeLTEquiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) :
    degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by simp

theorem eval_eq_sum_degreeLTEquiv {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) (x : R) :
    p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : ℕ) := by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm

theorem degreeLT_succ_eq_degreeLE {n : ℕ} : degreeLT R (n + 1) = degreeLE R n := by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ]

/-- The equivalence between monic polynomials of degree `n` and polynomials of degree less than
`n`, formed by adding a term `X ^ n`. -/
def monicEquivDegreeLT [Nontrivial R] (n : ℕ) :
    { p : R[X] // p.Monic ∧ p.natDegree = n } ≃ degreeLT R n where
  toFun p := ⟨p.1.eraseLead, by
    rcases p with ⟨p, hp, rfl⟩
    simp only [mem_degreeLT]
    refine lt_of_lt_of_le ?_ degree_le_natDegree
    exact degree_eraseLead_lt (Polynomial.Monic.ne_zero_of_polynomial_ne hp one_ne_zero)⟩
  invFun := fun p =>
    ⟨X^n + p.1, monic_X_pow_add (mem_degreeLT.1 p.2), by
        rw [natDegree_add_eq_left_of_degree_lt]
        · simp
        · simp [mem_degreeLT.1 p.2]⟩
  left_inv := by
    rintro ⟨p, hp, rfl⟩
    ext1
    simp only
    conv_rhs => rw [← eraseLead_add_C_mul_X_pow p]
    simp [Monic.def.1 hp, add_comm]
  right_inv := by
    rintro ⟨p, hp⟩
    ext1
    simp only
    rw [eraseLead_add_of_degree_lt_left]
    · simp
    · simp [mem_degreeLT.1 hp]

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
every element of `p ∈ span R s`. -/
theorem exists_degree_le_of_mem_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty) :
    ∃ p' ∈ s, ∀ (p : R[X]), p ∈ Submodule.span R s → degree p ≤ degree p' := by
  obtain ⟨a, has, hmax⟩ := s_fin.exists_maximalFor degree s hs
  refine ⟨a, has, fun p hp => ?_⟩
  obtain ⟨p', hp', hpp'⟩ := exists_degree_le_of_mem_span hs hp
  exact hpp'.trans <| not_lt.1 <| not_lt_iff_le_imp_ge.2 <| hmax hp'

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
a field, this is equivalent to `R[X]` being an infinite-dimensional vector space over `R`. -/
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

theorem geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
    (∑ i ∈ range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : ℕ => (n.choose (i + 1) : R[X]) * X ^ i := by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finset_sum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i, if_pos rfl]
    · simp +contextual only [@eq_comm _ i, if_false,
        imp_true_iff]
    · simp +contextual only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, if_true, imp_true_iff]
  induction n generalizing i with
  | zero => dsimp; simp only [zero_comp, coeff_zero, Nat.cast_zero]
  | succ n ih =>
    simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
      Nat.cast_add, coeff_X_add_one_pow]

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

theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn

theorem monic_geom_sum_X {n : ℕ} (hn : n ≠ 0) : (∑ i ∈ range n, (X : R[X]) ^ i).Monic := by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]

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
          else Subring.subset_closure (p.coeff_mem_coeffs H)⟩ :
        Subring.closure (↑p.coeffs : Set R))

@[simp]
theorem coeff_restriction {p : R[X]} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := by
  classical
  simp only [restriction, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

theorem coeff_restriction' {p : R[X]} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n := by
  simp

@[simp]
theorem support_restriction (p : R[X]) : support (restriction p) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubring_apply, coeff_restriction]

@[simp]
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]

@[simp]
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [natDegree]

@[simp]
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]

@[simp]
theorem restriction_one : restriction (1 : R[X]) = 1 :=
  ext fun i => Subtype.eq <| by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl

variable [Semiring S] {f : R →+* S} {x : S}

theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.coeffs : Set R)))) x p.restriction := by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coe_subtype]

section ToSubring

variable (p : R[X]) (T : Subring R)

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def toSubring (hp : (↑p.coeffs : Set R) ⊆ T) : T[X] :=
  ∑ i ∈ p.support,
    monomial i
      (⟨p.coeff i,
        letI := Classical.decEq R
        if H : p.coeff i = 0 then H.symm ▸ T.zero_mem else hp (p.coeff_mem_coeffs H)⟩ : T)

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

theorem coeff_toSubring' {n : ℕ} : (coeff (toSubring p T hp) n).1 = coeff p n := by
  simp

@[simp]
theorem support_toSubring : support (toSubring p T hp) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]
theorem degree_toSubring : (toSubring p T hp).degree = p.degree := by simp [degree]

@[simp]
theorem natDegree_toSubring : (toSubring p T hp).natDegree = p.natDegree := by simp [natDegree]

@[simp]
theorem monic_toSubring : Monic (toSubring p T hp) ↔ Monic p := by
  simp_rw [Monic, leadingCoeff, natDegree_toSubring, ← coeff_toSubring p T hp]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]
theorem toSubring_zero : toSubring (0 : R[X]) T (by simp [coeffs]) = 0 := by
  ext i
  simp

@[simp]
theorem toSubring_one :
    toSubring (1 : R[X]) T
        (Set.Subset.trans coeffs_one <| Finset.singleton_subset_set_iff.2 T.one_mem) =
      1 :=
  ext fun i => Subtype.eq <| by
    rw [coeff_toSubring', coeff_one, coeff_one, apply_ite Subtype.val, ZeroMemClass.coe_zero,
      OneMemClass.coe_one]

@[simp]
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p := by
  ext n
  simp [coeff_map]

end ToSubring

variable (T : Subring R)

/-- Given a polynomial whose coefficients are in some subring, return
the corresponding polynomial whose coefficients are in the ambient ring. -/
def ofSubring (p : T[X]) : R[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i : R)

theorem coeff_ofSubring (p : T[X]) (n : ℕ) : coeff (ofSubring T p) n = (coeff p n : T) := by
  simp only [ofSubring, coeff_monomial, finset_sum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, Classical.not_not, ite_eq_left_iff]
  intro h
  rw [h, ZeroMemClass.coe_zero]

@[simp]
theorem coeffs_ofSubring {p : T[X]} : (↑(p.ofSubring T).coeffs : Set R) ⊆ T := by
  classical
  intro i hi
  simp only [coeffs, Set.mem_image, mem_support_iff, Ne, Finset.mem_coe,
    (Finset.coe_image)] at hi
  rcases hi with ⟨n, _, h'n⟩
  rw [← h'n, coeff_ofSubring]
  exact Subtype.mem (coeff p n : T)

end Ring

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

variable {I : Ideal R[X]}

theorem mem_ofPolynomial (x) : x ∈ I.ofPolynomial ↔ x ∈ I :=
  Iff.rfl

variable (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  Polynomial.degreeLE R n ⊓ I.ofPolynomial

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
def leadingCoeffNth (n : ℕ) : Ideal R :=
  (I.degreeLE n).map <| lcoeff R n

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n

end Semiring

section CommSemiring

variable [CommSemiring R] [Semiring S]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X])
    (hp : ∀ n : ℕ, p.coeff n ∈ I.comap (C : R →+* R[X])) : p ∈ I :=
  sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)

/-- The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : R[X]} :
    f ∈ (Ideal.map (C : R →+* R[X]) I : Ideal R[X]) ↔ ∀ n : ℕ, f.coeff n ∈ I := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine fun f g _ hg n => ?_
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [← sum_monomial_eq f]
    refine (I.map C : Ideal R[X]).sum_mem fun n _ => ?_
    simp only [← C_mul_X_pow_eq_monomial]
    rw [mul_comm]
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))

theorem _root_.Polynomial.ker_mapRingHom (f : R →+* S) :
    RingHom.ker (Polynomial.mapRingHom f) = (RingHom.ker f).map (C : R →+* R[X]) := by
  ext
  simp only [RingHom.mem_ker, coe_mapRingHom]
  rw [mem_map_C_iff, Polynomial.ext_iff]
  simp [RingHom.mem_ker]

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
      rw [Polynomial.leadingCoeff, natDegree, hpdeg, Nat.cast_withBot, WithBot.unbotD_coe]
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine ⟨p * X ^ (n - natDegree p), ⟨?_, I.mul_mem_right _ hpI⟩, ?_⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      rw [← Nat.cast_add, this]
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), this]

theorem mem_leadingCoeffNth_zero (x) : x ∈ I.leadingCoeffNth 0 ↔ C x ∈ I :=
  (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩

theorem leadingCoeffNth_mono {m n : ℕ} (H : m ≤ n) : I.leadingCoeffNth m ≤ I.leadingCoeffNth n := by
  intro r hr
  simp only [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  grw [hpdeg, degree_X_pow_le]
  rw [← Nat.cast_add, add_tsub_cancel_of_le H]

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

/-- If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ⁻ᵏ` with `n = ∑ nᵢ`.
-/
theorem _root_.Polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (I : Ideal R) (n : ι → ℕ) (h : ∀ i ∈ s, ∀ (k), (f i).coeff k ∈ I ^ (n i - k)) (k : ℕ) :
    (s.prod f).coeff k ∈ I ^ (s.sum n - k) := by
  classical
    induction s using Finset.induction generalizing k with
    | empty =>
      rw [sum_empty, prod_empty, coeff_one, zero_tsub, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | insert a s ha hs =>
      rw [sum_insert ha, prod_insert ha, coeff_mul]
      apply sum_mem
      rintro ⟨i, j⟩ e
      obtain rfl : i + j = k := mem_antidiagonal.mp e
      apply Ideal.pow_le_pow_right add_tsub_add_le_tsub_add_tsub
      rw [pow_add]
      exact Ideal.mul_mem_mul (by grind) (by grind)

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

/-- The only constant in a maximal ideal over a field is `0`. -/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : C x ∈ I) : x = 0 := by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert I.mul_mem_left (C y) hx
  rw [← C.map_mul, hR.mul_comm y x, hy, RingHom.map_one]

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
          Finset.sum_insert (Finset.notMem_erase _ _), (P.add_mem_iff_left _).not]
        · apply mt h.2
          rw [not_or]
          exact ⟨Nat.find_spec hf, Nat.find_spec hg⟩
        apply P.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_erase, Finset.mem_antidiagonal] at hij
        simp only [Ne, Prod.mk_inj, not_and_or] at hij
        obtain hi | hj : i < m ∨ j < n := by
          omega
        · rw [mul_comm]
          apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hf hi)
        · apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hg hj)

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
theorem isPrime_map_C_of_isPrime {P : Ideal R} (H : IsPrime P) :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) :=
  (isPrime_map_C_iff_isPrime P).mpr H

theorem is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X]) (n : ℕ) :
    Submodule.FG (I.degreeLE n) :=
  letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _

end CommRing

end Ideal

section Ideal

open Submodule Set

variable [Semiring R] {f : R[X]} {I : Ideal R[X]}

/-- If the coefficients of a polynomial belong to an ideal, then that ideal contains
the ideal spanned by the coefficients of the polynomial. -/
theorem span_le_of_C_coeff_mem (cf : ∀ i : ℕ, C (f.coeff i) ∈ I) :
    Ideal.span { g | ∃ i, g = C (f.coeff i) } ≤ I := by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf

theorem mem_span_C_coeff : f ∈ Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) } := by
  let p := Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) ∈ p := by
    apply subset_span
    rw [mem_setOf_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n) ∈ p := p.smul_mem _ this
  convert this using 1
  simp only [monomial_mul_C, one_mul, smul_eq_mul]
  rw [← C_mul_X_pow_eq_monomial]

theorem exists_C_coeff_notMem : f ∉ I → ∃ i : ℕ, C (coeff f i) ∉ I :=
  Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

@[deprecated (since := "2025-05-23")] alias exists_C_coeff_not_mem := exists_C_coeff_notMem

end Ideal

variable {σ : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

theorem prime_C_iff : Prime (C r) ↔ Prime r :=
  ⟨comap_prime C (evalRingHom (0 : R)) fun _ => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      apply Ideal.isPrime_map_C_of_isPrime hr
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩

end Polynomial

namespace MvPolynomial

private theorem prime_C_iff_of_fintype {R : Type u} (σ : Type v) {r : R} [CommRing R] [Fintype σ] :
    Prime (C r : MvPolynomial σ R) ↔ Prime r := by
  rw [← MulEquiv.prime_iff (renameEquiv R (Fintype.equivFin σ))]
  convert_to Prime (C r) ↔ _
  · congr!
    simp only [renameEquiv_apply, algHom_C, algebraMap_eq]
  · induction Fintype.card σ with
    | zero => exact MulEquiv.prime_iff (isEmptyAlgEquiv R (Fin 0)).symm (p := r)
    | succ d hd =>
      convert MulEquiv.prime_iff (finSuccEquiv R d).symm (p := Polynomial.C (C r))
      · simp [← finSuccEquiv_comp_C_eq_C]
      · simp [← hd, Polynomial.prime_C_iff]

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
        convert _root_.map_dvd (killCompl Subtype.val_injective) hd
        · simp
        · simp
      rw [← rename_C ((↑) : s → σ)]
      let f := (rename (R := R) ((↑) : s → σ)).toRingHom
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp (map_dvd f) (map_dvd f)⟩⟩

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
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.toAlgHom_toRingHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [this, MulEquiv.prime_iff, prime_C_iff]

end MvPolynomial

end Prime

/-- **Hilbert basis theorem**: a polynomial ring over a Noetherian ring is a Noetherian ring. -/
protected theorem Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M := inst.wf.min (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M ∈ Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := fun k =>
        Or.casesOn (le_or_gt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h _ hx =>
          Classical.by_contradiction fun hxm =>
            haveI : IsNoetherian R R := inst
            have : ¬M < I.leadingCoeffNth k := by
              refine WellFounded.not_lt_min inst.wf _ _ ?_; exact ⟨k, rfl⟩
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : ∀ {x}, x ∈ I.degreeLE N → x ∈ Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun hx =>
          Submodule.span_induction (hx := hx) (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ _ _ => Ideal.add_mem _) fun c f _ hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s, le_antisymm (Ideal.span_le.2 fun x hx =>
          have : x ∈ I.degreeLE N := hs ▸ Submodule.subset_span hx
          this.2) <| by
        have : Submodule.span R[X] ↑s = Ideal.span ↑s := rfl
        rw [this]
        intro p hp
        generalize hn : p.natDegree = k
        induction k using Nat.strong_induction_on generalizing p with | _ k ih
        rcases le_or_gt k N with h | h
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

attribute [instance] Polynomial.isNoetherianRing

namespace Polynomial

theorem linearIndependent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : ℕ => (f ^ n) v) ↔ ∀ p : R[X], aeval f p v = 0 → p = 0 := by
  rw [linearIndependent_iff]
  simp only [Finsupp.linearCombination_apply, aeval_endomorphism, forall_iff_forall_finsupp,
    ofFinsupp_eq_zero]
  exact Iff.rfl

theorem disjoint_ker_aeval_of_isCoprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm

theorem sup_aeval_range_eq_top_of_isCoprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'

theorem sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) ≤ LinearMap.ker (aeval f (p * q)) := by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm, aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hx, LinearMap.map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hy, LinearMap.map_zero]
  rw [LinearMap.mem_ker, ← hxy, LinearMap.map_add, h_eval_x, h_eval_y, add_zero]

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
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]
  have h_eval₂_pqq' :=
    calc
      aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v := by rw [← mul_assoc, mul_comm]
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, LinearMap.map_zero]
  rw [aeval_mul] at h_eval₂_qpp' h_eval₂_pqq'
  refine
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', ?_⟩
  rw [add_comm, mul_comm p p', mul_comm q q']
  simpa only [map_add, map_mul, aeval_one] using congr_arg (fun p : R[X] => aeval f p v) hpq'

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

theorem isNoetherianRing_fin [IsNoetherianRing R] :
    ∀ {n : ℕ}, IsNoetherianRing (MvPolynomial (Fin n) R)
  | 0 => isNoetherianRing_fin_0
  | n + 1 =>
    @isNoetherianRing_of_ringEquiv (Polynomial (MvPolynomial (Fin n) R)) _ _ _
      (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
      (@Polynomial.isNoetherianRing (MvPolynomial (Fin n) R) _ isNoetherianRing_fin)

/-- The multivariate polynomial ring in finitely many variables over a Noetherian ring
is itself a Noetherian ring. -/
instance isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin

/-- Auxiliary lemma:
Multivariate polynomials over an integral domain
with variables indexed by `Fin n` form an integral domain.
This fact is proven inductively,
and then used to prove the general case without any finiteness hypotheses.
See `MvPolynomial.noZeroDivisors` for the general case. -/
@[deprecated "MvPolynomial.noZeroDivisors" (since := "2025-07-18")]
theorem noZeroDivisors_fin (R : Type u) [CommSemiring R] [NoZeroDivisors R] :
    ∀ n : ℕ, NoZeroDivisors (MvPolynomial (Fin n) R) := fun _ ↦ inferInstance

/-- Auxiliary lemma:
Multivariate polynomials in finitely many variables over an integral domain form an integral domain.
This fact is proven by transport of structure from the `MvPolynomial.noZeroDivisors_fin`,
and then used to prove the general case without finiteness hypotheses.
See `MvPolynomial.noZeroDivisors` for the general case. -/
@[deprecated "MvPolynomial.noZeroDivisors" (since := "2025-07-18")]
theorem noZeroDivisors_of_finite (R : Type u) (σ : Type v) [CommSemiring R]
    [NoZeroDivisors R] : NoZeroDivisors (MvPolynomial σ R) := inferInstance

theorem map_mvPolynomial_eq_eval₂ {S : Type*} [CommSemiring S] [Finite σ]
    (ϕ : MvPolynomial σ R →+* S) (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.C) (fun s => ϕ (MvPolynomial.X s)) p := by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq', map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

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

/-- The push-forward of an ideal `I` of `R` to `MvPolynomial σ R` via inclusion
is exactly the set of polynomials whose coefficients are in `I` -/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      ∀ m : σ →₀ ℕ, f.coeff m ∈ I := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · refine fun f g _ hg n => ?_
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

theorem ker_map (f : R →+* S) :
    RingHom.ker (map f : MvPolynomial σ R →+* MvPolynomial σ S) =
    Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  ext
  rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]

lemma ker_mapAlgHom {S₁ S₂ σ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁]
    [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    RingHom.ker (MvPolynomial.mapAlgHom (σ := σ) f) = Ideal.map MvPolynomial.C (RingHom.ker f) :=
  MvPolynomial.ker_map (f.toRingHom : S₁ →+* S₂)

end MvPolynomial
