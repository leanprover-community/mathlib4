/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.Polynomial.Degree.TrailingDegree
import Mathlib.Data.Polynomial.EraseLead
import Mathlib.Data.Polynomial.Eval

#align_import data.polynomial.reverse from "leanprover-community/mathlib"@"44de64f183393284a16016dfb2a48ac97382f2bd"

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : R[X]` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.natDegree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/


namespace Polynomial

open Polynomial Finsupp Finset

open Polynomial

section Semiring

variable {R : Type*} [Semiring R] {f : R[X]}

/-- If `i ≤ N`, then `revAtFun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `revAt`.
-/
def revAtFun (N i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i
#align polynomial.rev_at_fun Polynomial.revAtFun

theorem revAtFun_invol {N i : ℕ} : revAtFun N (revAtFun N i) = i := by
  unfold revAtFun
  split_ifs with h j
  · exact tsub_tsub_cancel_of_le h
  · exfalso
    apply j
    exact Nat.sub_le N i
  · rfl
#align polynomial.rev_at_fun_invol Polynomial.revAtFun_invol

theorem revAtFun_inj {N : ℕ} : Function.Injective (revAtFun N) := by
  intro a b hab
  rw [← @revAtFun_invol N a, hab, revAtFun_invol]
#align polynomial.rev_at_fun_inj Polynomial.revAtFun_inj

/-- If `i ≤ N`, then `revAt N i` returns `N - i`, otherwise it returns `i`.
Essentially, this embedding is only used for `i ≤ N`.
The advantage of `revAt N i` over `N - i` is that `revAt` is an involution.
-/
def revAt (N : ℕ) : Function.Embedding ℕ ℕ
    where
  toFun i := ite (i ≤ N) (N - i) i
  inj' := revAtFun_inj
#align polynomial.rev_at Polynomial.revAt

/-- We prefer to use the bundled `revAt` over unbundled `revAtFun`. -/
@[simp]
theorem revAtFun_eq (N i : ℕ) : revAtFun N i = revAt N i :=
  rfl
#align polynomial.rev_at_fun_eq Polynomial.revAtFun_eq

@[simp]
theorem revAt_invol {N i : ℕ} : (revAt N) (revAt N i) = i :=
  revAtFun_invol
#align polynomial.rev_at_invol Polynomial.revAt_invol

@[simp]
theorem revAt_le {N i : ℕ} (H : i ≤ N) : revAt N i = N - i :=
  if_pos H
#align polynomial.rev_at_le Polynomial.revAt_le

lemma revAt_eq_self_of_lt {N i : ℕ} (h : N < i) : revAt N i = i := by simp [revAt, Nat.not_le.mpr h]

theorem revAt_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
    revAt (N + O) (n + o) = revAt N n + revAt O o := by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [revAt_le (le_add_right rfl.le)]
  rw [add_assoc, add_left_comm n' o, ← add_assoc, revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]
#align polynomial.rev_at_add Polynomial.revAt_add

-- @[simp] -- Porting note (#10618): simp can prove this
theorem revAt_zero (N : ℕ) : revAt N 0 = N := by simp
#align polynomial.rev_at_zero Polynomial.revAt_zero

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (revAt N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.  -/
noncomputable def reflect (N : ℕ) : R[X] → R[X]
  | ⟨f⟩ => ⟨Finsupp.embDomain (revAt N) f⟩
#align polynomial.reflect Polynomial.reflect

theorem reflect_support (N : ℕ) (f : R[X]) :
    (reflect N f).support = Finset.image (revAt N) f.support := by
  rcases f with ⟨⟩
  ext1
  simp only [reflect, support_ofFinsupp, support_embDomain, Finset.mem_map, Finset.mem_image]
#align polynomial.reflect_support Polynomial.reflect_support

@[simp]
theorem coeff_reflect (N : ℕ) (f : R[X]) (i : ℕ) : coeff (reflect N f) i = f.coeff (revAt N i) := by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    Finsupp.embDomain (revAt N) f i = Finsupp.embDomain (revAt N) f (revAt N (revAt N i)) := by
      rw [revAt_invol]
    _ = f (revAt N i) := Finsupp.embDomain_apply _ _ _
#align polynomial.coeff_reflect Polynomial.coeff_reflect

@[simp]
theorem reflect_zero {N : ℕ} : reflect N (0 : R[X]) = 0 :=
  rfl
#align polynomial.reflect_zero Polynomial.reflect_zero

@[simp]
theorem reflect_eq_zero_iff {N : ℕ} {f : R[X]} : reflect N (f : R[X]) = 0 ↔ f = 0 := by
  rw [ofFinsupp_eq_zero, reflect, embDomain_eq_zero, ofFinsupp_eq_zero]
#align polynomial.reflect_eq_zero_iff Polynomial.reflect_eq_zero_iff

@[simp]
theorem reflect_add (f g : R[X]) (N : ℕ) : reflect N (f + g) = reflect N f + reflect N g := by
  ext
  simp only [coeff_add, coeff_reflect]
#align polynomial.reflect_add Polynomial.reflect_add

@[simp]
theorem reflect_C_mul (f : R[X]) (r : R) (N : ℕ) : reflect N (C r * f) = C r * reflect N f := by
  ext
  simp only [coeff_reflect, coeff_C_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.reflect_C_mul Polynomial.reflect_C_mul

-- @[simp] -- Porting note (#10618): simp can prove this (once `reflect_monomial` is in simp scope)
theorem reflect_C_mul_X_pow (N n : ℕ) {c : R} : reflect N (C c * X ^ n) = C c * X ^ revAt N n := by
  ext
  rw [reflect_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_reflect]
  split_ifs with h
  · rw [h, revAt_invol, coeff_X_pow_self]
  · rw [not_mem_support_iff.mp]
    intro a
    rw [← one_mul (X ^ n), ← C_1] at a
    apply h
    rw [← mem_support_C_mul_X_pow a, revAt_invol]
set_option linter.uppercaseLean3 false in
#align polynomial.reflect_C_mul_X_pow Polynomial.reflect_C_mul_X_pow

@[simp]
theorem reflect_C (r : R) (N : ℕ) : reflect N (C r) = C r * X ^ N := by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.reflect_C Polynomial.reflect_C

@[simp]
theorem reflect_monomial (N n : ℕ) : reflect N ((X : R[X]) ^ n) = X ^ revAt N n := by
  rw [← one_mul (X ^ n), ← one_mul (X ^ revAt N n), ← C_1, reflect_C_mul_X_pow]
#align polynomial.reflect_monomial Polynomial.reflect_monomial

@[simp] lemma reflect_one_X : reflect 1 (X : R[X]) = 1 := by
  simpa using reflect_monomial 1 1 (R := R)

theorem reflect_mul_induction (cf cg : ℕ) :
    ∀ N O : ℕ,
      ∀ f g : R[X],
        f.support.card ≤ cf.succ →
          g.support.card ≤ cg.succ →
            f.natDegree ≤ N →
              g.natDegree ≤ O → reflect (N + O) (f * g) = reflect N f * reflect O g := by
  induction' cf with cf hcf
  --first induction (left): base case
  · induction' cg with cg hcg
    -- second induction (right): base case
    · intro N O f g Cf Cg Nf Og
      rw [← C_mul_X_pow_eq_self Cf, ← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), reflect_C_mul,
        reflect_monomial, add_comm, revAt_add Nf Og, mul_assoc, X_pow_mul, mul_assoc, ←
        pow_add (X : R[X]), add_comm]
    -- second induction (right): induction step
    · intro N O f g Cf Cg Nf Og
      by_cases g0 : g = 0
      · rw [g0, reflect_zero, mul_zero, mul_zero, reflect_zero]
      rw [← eraseLead_add_C_mul_X_pow g, mul_add, reflect_add, reflect_add, mul_add, hcg, hcg] <;>
        try assumption
      · exact le_add_left card_support_C_mul_X_pow_le_one
      · exact le_trans (natDegree_C_mul_X_pow_le g.leadingCoeff g.natDegree) Og
      · exact Nat.lt_succ_iff.mp (gt_of_ge_of_gt Cg (eraseLead_support_card_lt g0))
      · exact le_trans eraseLead_natDegree_le_aux Og
  --first induction (left): induction step
  · intro N O f g Cf Cg Nf Og
    by_cases f0 : f = 0
    · rw [f0, reflect_zero, zero_mul, zero_mul, reflect_zero]
    rw [← eraseLead_add_C_mul_X_pow f, add_mul, reflect_add, reflect_add, add_mul, hcf, hcf] <;>
      try assumption
    · exact le_add_left card_support_C_mul_X_pow_le_one
    · exact le_trans (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree) Nf
    · exact Nat.lt_succ_iff.mp (gt_of_ge_of_gt Cf (eraseLead_support_card_lt f0))
    · exact le_trans eraseLead_natDegree_le_aux Nf
#align polynomial.reflect_mul_induction Polynomial.reflect_mul_induction

@[simp]
theorem reflect_mul (f g : R[X]) {F G : ℕ} (Ff : f.natDegree ≤ F) (Gg : g.natDegree ≤ G) :
    reflect (F + G) (f * g) = reflect F f * reflect G g :=
  reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg
#align polynomial.reflect_mul Polynomial.reflect_mul

section Eval₂

variable {S : Type*} [CommSemiring S]

theorem eval₂_reflect_mul_pow (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟ x) (reflect N f) * x ^ N = eval₂ i x f := by
  refine'
    induction_with_natDegree_le (fun f => eval₂ i (⅟ x) (reflect N f) * x ^ N = eval₂ i x f) _ _ _
      _ f hf
  · simp
  · intro n r _ hnN
    simp only [revAt_le hnN, reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow_add, ← mul_assoc, mul_assoc (i r), ← mul_pow, invOf_mul_self, one_pow, mul_one]
  · intros
    simp [*, add_mul]
#align polynomial.eval₂_reflect_mul_pow Polynomial.eval₂_reflect_mul_pow

theorem eval₂_reflect_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟ x) (reflect N f) = 0 ↔ eval₂ i x f = 0 := by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h, zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟ x) _), ← one_pow N, ← mul_invOf_self x, mul_pow, ← mul_assoc, h,
      zero_mul]
#align polynomial.eval₂_reflect_eq_zero_iff Polynomial.eval₂_reflect_eq_zero_iff

end Eval₂

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, `reverse f = f (1/X) * X ^ f.natDegree`. -/
noncomputable def reverse (f : R[X]) : R[X] :=
  reflect f.natDegree f
#align polynomial.reverse Polynomial.reverse

theorem coeff_reverse (f : R[X]) (n : ℕ) : f.reverse.coeff n = f.coeff (revAt f.natDegree n) := by
  rw [reverse, coeff_reflect]
#align polynomial.coeff_reverse Polynomial.coeff_reverse

@[simp]
theorem coeff_zero_reverse (f : R[X]) : coeff (reverse f) 0 = leadingCoeff f := by
  rw [coeff_reverse, revAt_le (zero_le f.natDegree), tsub_zero, leadingCoeff]
#align polynomial.coeff_zero_reverse Polynomial.coeff_zero_reverse

@[simp]
theorem reverse_zero : reverse (0 : R[X]) = 0 :=
  rfl
#align polynomial.reverse_zero Polynomial.reverse_zero

@[simp]
theorem reverse_eq_zero : f.reverse = 0 ↔ f = 0 := by simp [reverse]
#align polynomial.reverse_eq_zero Polynomial.reverse_eq_zero

theorem reverse_natDegree_le (f : R[X]) : f.reverse.natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse, revAt, Function.Embedding.coeFn_mk, if_neg (not_le_of_gt hn),
    coeff_eq_zero_of_natDegree_lt hn]
#align polynomial.reverse_nat_degree_le Polynomial.reverse_natDegree_le

theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) :
    f.natDegree = f.reverse.natDegree + f.natTrailingDegree := by
  by_cases hf : f = 0
  · rw [hf, reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine' tsub_le_iff_right.mp _
    apply le_natDegree_of_ne_zero
    rw [reverse, coeff_reflect, ← revAt_le f.natTrailingDegree_le_natDegree, revAt_invol]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hf
  · rw [← le_tsub_iff_left f.reverse_natDegree_le]
    apply natTrailingDegree_le_of_ne_zero
    have key := mt leadingCoeff_eq_zero.mp (mt reverse_eq_zero.mp hf)
    rwa [leadingCoeff, coeff_reverse, revAt_le f.reverse_natDegree_le] at key
#align polynomial.nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree Polynomial.natDegree_eq_reverse_natDegree_add_natTrailingDegree

theorem reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTrailingDegree := by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree, add_tsub_cancel_right]
#align polynomial.reverse_nat_degree Polynomial.reverse_natDegree

theorem reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff := by
  rw [leadingCoeff, reverse_natDegree, ← revAt_le f.natTrailingDegree_le_natDegree,
    coeff_reverse, revAt_invol, trailingCoeff]
#align polynomial.reverse_leading_coeff Polynomial.reverse_leadingCoeff

theorem natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero, reverse_eq_zero, coeff_zero_reverse, leadingCoeff_ne_zero]
  exact eq_or_ne _ _
#align polynomial.reverse_nat_trailing_degree Polynomial.natTrailingDegree_reverse

theorem reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoeff := by
  rw [trailingCoeff, natTrailingDegree_reverse, coeff_zero_reverse]
#align polynomial.reverse_trailing_coeff Polynomial.reverse_trailingCoeff

theorem reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff ≠ 0) :
    reverse (f * g) = reverse f * reverse g := by
  unfold reverse
  rw [natDegree_mul' fg, reflect_mul f g rfl.le rfl.le]
#align polynomial.reverse_mul Polynomial.reverse_mul

@[simp]
theorem reverse_mul_of_domain {R : Type*} [Ring R] [NoZeroDivisors R] (f g : R[X]) :
    reverse (f * g) = reverse f * reverse g := by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]
#align polynomial.reverse_mul_of_domain Polynomial.reverse_mul_of_domain

theorem trailingCoeff_mul {R : Type*} [Ring R] [NoZeroDivisors R] (p q : R[X]) :
    (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff := by
  rw [← reverse_leadingCoeff, reverse_mul_of_domain, leadingCoeff_mul, reverse_leadingCoeff,
    reverse_leadingCoeff]
#align polynomial.trailing_coeff_mul Polynomial.trailingCoeff_mul

@[simp]
theorem coeff_one_reverse (f : R[X]) : coeff (reverse f) 1 = nextCoeff f := by
  rw [coeff_reverse, nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, revAt]
  · rw [revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)
#align polynomial.coeff_one_reverse Polynomial.coeff_one_reverse

@[simp] lemma reverse_C (t : R) :
    reverse (C t) = C t := by
  simp [reverse]

@[simp] lemma reverse_mul_X (p : R[X]) : reverse (p * X) = reverse p := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]

@[simp] lemma reverse_X_mul (p : R[X]) : reverse (X * p) = reverse p := by
  rw [commute_X p, reverse_mul_X]

@[simp] lemma reverse_mul_X_pow (p : R[X]) (n : ℕ) : reverse (p * X ^ n) = reverse p := by
  induction' n with n ih; simp
  rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]

@[simp] lemma reverse_X_pow_mul (p : R[X]) (n : ℕ) : reverse (X ^ n * p) = reverse p := by
  rw [commute_X_pow p, reverse_mul_X_pow]

@[simp] lemma reverse_add_C (p : R[X]) (t : R) :
    reverse (p + C t) = reverse p + C t * X ^ p.natDegree := by
  simp [reverse]

@[simp] lemma reverse_C_add (p : R[X]) (t : R) :
    reverse (C t + p) = C t * X ^ p.natDegree + reverse p := by
  rw [add_comm, reverse_add_C, add_comm]

section Eval₂

variable {S : Type*} [CommSemiring S]

theorem eval₂_reverse_mul_pow (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟ x) (reverse f) * x ^ f.natDegree = eval₂ i x f :=
  eval₂_reflect_mul_pow i _ _ f le_rfl
#align polynomial.eval₂_reverse_mul_pow Polynomial.eval₂_reverse_mul_pow

@[simp]
theorem eval₂_reverse_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟ x) (reverse f) = 0 ↔ eval₂ i x f = 0 :=
  eval₂_reflect_eq_zero_iff i x _ _ le_rfl
#align polynomial.eval₂_reverse_eq_zero_iff Polynomial.eval₂_reverse_eq_zero_iff

end Eval₂

end Semiring

section Ring

variable {R : Type*} [Ring R]

@[simp]
theorem reflect_neg (f : R[X]) (N : ℕ) : reflect N (-f) = -reflect N f := by
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg, reflect_C_mul, C_neg, C_1, ← neg_eq_neg_one_mul]
#align polynomial.reflect_neg Polynomial.reflect_neg

@[simp]
theorem reflect_sub (f g : R[X]) (N : ℕ) : reflect N (f - g) = reflect N f - reflect N g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, reflect_add, reflect_neg]
#align polynomial.reflect_sub Polynomial.reflect_sub

@[simp]
theorem reverse_neg (f : R[X]) : reverse (-f) = -reverse f := by
  rw [reverse, reverse, reflect_neg, natDegree_neg]
#align polynomial.reverse_neg Polynomial.reverse_neg

end Ring

end Polynomial
