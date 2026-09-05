/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Henselian rings

In this file we set up the basic theory of Henselian (local) rings.
A ring `R` is *Henselian* at an ideal `I` if the following conditions hold:
* `I` is contained in the Jacobson radical of `R`
* for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
  there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.)

A local ring `R` is *Henselian* if it is Henselian at its maximal ideal.
In this case the first condition is automatic, and in the second condition we may ask for
`f.derivative.eval a ≠ 0`, since the quotient ring `R/I` is a field in this case.

## Main declarations

* `HenselianRing`: a typeclass on commutative rings,
  asserting that the ring is Henselian at the ideal `I`.
* `HenselianLocalRing`: a typeclass on commutative rings, asserting that the ring is local Henselian
* `Field.henselian`: fields are Henselian local rings
* `Henselian.TFAE`: equivalent ways of expressing the Henselian property for local rings
* `HenselianRing.exists_isRoot`: in a Henselian ring the simple roots of *arbitrary* polynomials
  lift, not just those of monic ones
* `IsAdicComplete.henselianRing`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`

## References

https://stacks.math.columbia.edu/tag/04GE

## TODO

After a good API for étale ring homomorphisms has been developed,
we can give more equivalent characterization of Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598

-/

public section


noncomputable section

universe u v

open Polynomial IsLocalRing Function List
open scoped Ring

theorem isLocalHom_of_le_jacobson_bot {R : Type*} [CommRing R] (I : Ideal R)
    (h : I ≤ Ideal.jacobson ⊥) : IsLocalHom (Ideal.Quotient.mk I) := by
  constructor
  intro a h
  have : IsUnit (Ideal.Quotient.mk (Ideal.jacobson ⊥) a) := by
    rw [isUnit_iff_exists_inv] at *
    obtain ⟨b, hb⟩ := h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    use Ideal.Quotient.mk _ b
    rw [← (Ideal.Quotient.mk _).map_one, ← (Ideal.Quotient.mk _).map_mul, Ideal.Quotient.eq] at hb ⊢
    exact h hb
  obtain ⟨⟨x, y, h1, h2⟩, rfl : x = _⟩ := this
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← (Ideal.Quotient.mk _).map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq,
    Ideal.mem_jacobson_bot] at h1 h2
  specialize h1 1
  have h1 : IsUnit a ∧ IsUnit y := by simpa using h1
  exact h1.1

/-- A ring `R` is *Henselian* at an ideal `I` if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.) -/
class HenselianRing (R : Type*) [CommRing R] (I : Ideal R) : Prop where
  jac : I ≤ Ideal.jacobson ⊥
  is_henselian :
    ∀ (f : R[X]) (_ : f.Monic) (a₀ : R) (_ : f.eval a₀ ∈ I)
      (_ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I

/-- A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `b` of a polynomial `g` is *simple* if it is not a double root, so if
`g.derivative.eval b ≠ 0`.)

In other words, `R` is local Henselian if it is Henselian at the ideal `I`,
in the sense of `HenselianRing`. -/
class HenselianLocalRing (R : Type*) [CommRing R] : Prop extends IsLocalRing R where
  is_henselian :
    ∀ (f : R[X]) (_ : f.Monic) (a₀ : R) (_ : f.eval a₀ ∈ maximalIdeal R)
      (_ : IsUnit (f.derivative.eval a₀)), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R

-- see Note [lower instance priority]
instance (priority := 100) Field.henselian (K : Type*) [Field K] : HenselianLocalRing K where
  is_henselian f _ a₀ h₁ _ := by
    simp only [(maximalIdeal K).eq_bot_of_prime, Ideal.mem_bot] at h₁ ⊢
    exact ⟨a₀, h₁, sub_self _⟩

instance (R : Type*) [CommRing R] [hR : HenselianLocalRing R] :
    HenselianRing R (maximalIdeal R) where
  jac := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro I ⟨-, hI⟩
    exact (eq_maximalIdeal hI).ge
  is_henselian := by
    intro f hf a₀ h₁ h₂
    refine HenselianLocalRing.is_henselian f hf a₀ h₁ ?_
    contrapose h₂
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← Ideal.Quotient.eq_zero_iff_mem] at h₂
    rw [h₂]
    exact not_isUnit_zero

/-- **Hensel's lemma** for a ring that is Henselian at an ideal `I`: a simple root modulo `I` of an
arbitrary polynomial lifts to a root in `R`.

Contrary to `HenselianRing.is_henselian`, the polynomial `f` is not assumed to be monic. -/
theorem HenselianRing.exists_isRoot {R : Type*} [CommRing R] {I : Ideal R} [HenselianRing R I]
    {f : R[X]} {a₀ : R} (h₁ : f.eval a₀ ∈ I)
      (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a, f.IsRoot a ∧ a - a₀ ∈ I := by
  /- The reduction to the monic case goes as follows: after translating `a₀` to `0` and rescaling by
  `c₀ = f.eval a₀ ∈ I`, one obtains a polynomial `G` with `G ≡ 1 + c₁ * X` modulo `I`, where
  `c₁ = f.derivative.eval a₀`. Since `G` has constant coefficient `1`, its reverse `P` is monic, and
  `-c₁` is a simple root of `P` modulo `I`. A root `t` of `P` is a unit, and `⅟t` is then a root of
  `G`, which produces the root `a₀ + c₀ * ⅟t` of `f`. -/
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact ⟨a₀, Subsingleton.elim _ _, by simp⟩
  have := isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  set φ := Ideal.Quotient.mk I
  set c₀ := f.eval a₀ with hc₀
  set c₁ := f.derivative.eval a₀ with hc
  have hc₁ : IsUnit c₁ := IsUnit.of_map φ _ h₂
  have key : ∀ (p : R[X]) (x : R), φ (p.eval x) = (p.map φ).eval (φ x) := fun p x => by
    rw [eval_map, eval₂_at_apply]
  -- `f (y + a₀) = c₀ + y * q y`
  set q := (taylor a₀ f).divX with hq
  -- rescale by `c₀`: we look for a root of `f` of the form `a₀ + c₀ * b`
  set G : R[X] := 1 + X * q.comp (C c₀ * X) with hG
  have hGeval : ∀ b, c₀ * G.eval b = f.eval (c₀ * b + a₀) := fun b => by
    rw [← taylor_eval, ← divX_mul_X_add (taylor a₀ f), hG]
    simp
    ring
  have hG0 : G.coeff 0 = 1 := by simp [hG]
  have hG1 : G.coeff 1 = c₁ := by simpa [hG, coeff_one, coeff_X_mul, hq]
  -- modulo `I`, `G` is `1 + c₁ * X`
  have hGmap : G.map φ = 1 + C (φ c₁) * X := by
    ext (_ | _ | n)
    · simp [hG0, coeff_one]
    · simp [hG1, coeff_one]
    · have h : G.coeff (n + 2) ∈ I := by
        simpa [pow_succ, hG, coeff_one] using Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h₁)
      simpa [coeff_map, coeff_one, coeff_C_mul, coeff_X] using Ideal.Quotient.eq_zero_iff_mem.mpr h
  -- `G` has constant coefficient `1`, so its reverse `P` is monic; modulo `I` it is
  -- `X ^ M * (X + c₁)`, which has `-c₁` as a simple root
  have hM : G.natDegree = G.natDegree - 1 + 1 := by
    simp [le_natDegree_of_ne_zero, hG1, IsUnit.ne_zero hc₁]
  set P := G.reverse with hP
  have hPmonic : P.Monic := by
    rw [Monic, hP, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (hG0 ▸ one_ne_zero), hG0]
  have hPmap : P.map φ = X ^ (G.natDegree - 1) * (X + C (φ c₁)) := by
    rw [hP, Polynomial.reverse, map_reflect, hGmap, hM, ← C_1, ← pow_one X, reflect_add, reflect_C,
      reflect_C_mul_X_pow, revAt_le (Nat.le_add_left 1 _)]
    simp
    ring
  obtain ⟨t, htroot, htI⟩ := HenselianRing.is_henselian P hPmonic (-c₁)
    (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [key, hPmap]; simp))
    (by rw [key, ← derivative_map, hPmap]; simpa [derivative_mul] using (h₂.neg.pow _))
  let : Invertible t := (IsUnit.of_map φ _ ((Ideal.Quotient.eq.2 htI) ▸ hc₁.neg.map _)).invertible
  have hGroot : G.eval (⅟t) = 0 := by
    have h := eval₂_reflect_eq_zero_iff (RingHom.id R) (⅟t) G.natDegree G le_rfl
    rw [invOf_invOf, show reflect G.natDegree G = P from rfl] at h
    simpa [eval₂_eq_eval_map] using h.mp (by simpa [eval₂_eq_eval_map] using htroot)
  use c₀ * ⅟t + a₀
  simp [IsRoot, ← hGeval, hGroot, mul_zero, Ideal.mul_mem_right, h₁]

/-- **Hensel's lemma** for a Henselian local ring: a simple root in the residue field of an
arbitrary polynomial lifts to a root in `R`.

Contrary to `HenselianLocalRing.is_henselian`, the polynomial `f` is not assumed to be monic. -/
theorem HenselianLocalRing.exists_isRoot {R : Type*} [CommRing R] [HenselianLocalRing R]
    {f : R[X]} {a₀ : R} (h₁ : f.eval a₀ ∈ maximalIdeal R) (h₂ : IsUnit (f.derivative.eval a₀)) :
    ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := HenselianRing.exists_isRoot h₁ (h₂.map _)

@[stacks 04GG]
theorem HenselianLocalRing.TFAE (R : Type u) [CommRing R] [IsLocalRing R] :
    TFAE
      [HenselianLocalRing R,
        ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
          aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀,
        ∀ {K : Type u} [Field K], ∀ (φ : R →+* K), Surjective φ →
          ∀ f : R[X], f.Monic → ∀ a₀, f.eval₂ φ a₀ = 0 → f.derivative.eval₂ φ a₀ ≠ 0 →
            ∃ a : R, f.IsRoot a ∧ φ a = a₀,
        ∀ f a₀, f.aeval a₀ = 0 → (derivative f).aeval a₀ ≠ 0 → ∃ a, f.IsRoot a ∧ residue R a = a₀,
        ∀ {K : Type u} [Field K], ∀ (φ : R →+* K), Surjective φ →
          ∀ (f : R[X]) (a₀ : K), f.eval₂ φ a₀ = 0 → f.derivative.eval₂ φ a₀ ≠ 0 →
            ∃ a : R, f.IsRoot a ∧ φ a = a₀] := by
  tfae_have 3 → 2
  | H => H (residue R) Ideal.Quotient.mk_surjective
  tfae_have 2 → 1
  | H => by
    constructor
    intro f hf a₀ h₁ h₂
    specialize H f hf (residue R a₀)
    have aux := flip mem_nonunits_iff.mp h₂
    simp only [aeval_def, ResidueField.algebraMap_eq, eval₂_at_apply, ←
      Ideal.Quotient.eq_zero_iff_mem, ← IsLocalRing.mem_maximalIdeal] at H h₁ aux
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ aux
    refine ⟨a, ha₁, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rwa [← sub_eq_zero, ← map_sub] at ha₂
  tfae_have 5 → 3
  | H, K, _K, φ, hφ, f, _, a₀ => H φ hφ f a₀
  tfae_have 5 → 4
  | H => H (residue R) Ideal.Quotient.mk_surjective
  tfae_have 4 → 2
  | H, f, _ => H f
  tfae_have 1 → 5
  | hR, K, _K, φ, hφ, f, a₀, h₁, h₂ => by
    obtain ⟨a₀, rfl⟩ := hφ a₀
    have H : f.eval a₀ ∈ maximalIdeal R → IsUnit (f.derivative.eval a₀) →
        ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R :=
      fun h₁ h₂ => HenselianLocalRing.exists_isRoot h₁ h₂
    simp only [← ker_eq_maximalIdeal φ hφ, eval₂_at_apply, RingHom.mem_ker] at H h₁ h₂
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ (by
      contrapose h₂
      rwa [← mem_nonunits_iff, ← mem_maximalIdeal, ← ker_eq_maximalIdeal φ hφ,
        RingHom.mem_ker] at h₂)
    refine ⟨a, ha₁, ?_⟩
    rwa [φ.map_sub, sub_eq_zero] at ha₂
  tfae_finish

-- see Note [lower instance priority]
/-- A ring `R` that is `I`-adically complete is Henselian at `I`. -/
instance (priority := 100) IsAdicComplete.henselianRing (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] : HenselianRing R I where
  jac := IsAdicComplete.le_jacobson_bot _
  is_henselian := by
    intro f _ a₀ h₁ h₂
    classical
      let f' := derivative f
      -- we define a sequence `c n` by starting at `a₀` and then continually
      -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
      -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
      let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
      have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
        intro n
        simp only [c]
      -- we now spend some time determining properties of the sequence `c : ℕ → R`
      -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
      -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
      -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
      have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => ?_
        rw [hc, sub_eq_add_neg, ← add_zero a₀]
        refine ih.add ?_
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine I.mul_mem_right _ ?_
        rw [← SModEq.zero] at h₁ ⊢
        exact (ih.eval f).trans h₁
      have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
        intro n
        have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
        apply IsUnit.of_map (Ideal.Quotient.mk I)
        convert! h₂ using 1
        exact SModEq.def.mp ((hc_mod n).eval _)
      have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
        intro n
        induction n with
        | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
        | succ n ih => ?_
        rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
          add_neg_cancel_comm]
        rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
          Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
        swap
        · intro i
          rw [zero_mul]
        refine Ideal.add_mem _ ?_ ?_
        · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
            taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
            mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
          exact Ideal.zero_mem _
        · refine Submodule.sum_mem _ ?_
          simp only [Finset.mem_Ico]
          rintro i ⟨h2i, _⟩
          have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
          refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
          rw [pow_mul']
          exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
      -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
      have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
        intro m n hmn
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        clear hmn
        induction k with
        | zero => rw [add_zero]
        | succ k ih => ?_
        rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
        refine ih.add ?_
        symm
        rw [SModEq.zero, Ideal.neg_mem_iff]
        refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
        rw [add_assoc]
        exact le_self_add
      -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
      obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
      refine ⟨a, ?_, ?_⟩
      · show f.IsRoot a
        suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
        intro n
        specialize ha n
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
        refine (ha.symm.eval f).trans ?_
        rw [SModEq.zero]
        exact Ideal.pow_le_pow_right le_self_add (hfcI _)
      · show a - a₀ ∈ I
        specialize ha (0 + 1)
        rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
        rw [← SModEq.sub_mem, ← add_zero a₀]
        refine ha.symm.trans (SModEq.rfl.add ?_)
        rw [SModEq.zero, Ideal.neg_mem_iff]
        exact Ideal.mul_mem_right _ _ h₁

open Polynomial in
@[stacks 06RR]
theorem IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub {R : Type*} [CommRing R] [IsLocalRing R]
    {f : Polynomial R} {a b : R} (ha : f.eval a = 0) (hb : f.eval b = 0) (h : ¬ IsUnit (a - b))
    (h' : IsUnit (f.derivative.eval a)) : a = b := by
  obtain ⟨c, _⟩ := exists_mul_sq_add_linear_part_eq_eval_add f a (b - a)
  have hc : (c * (b - a) + eval a (derivative f)) * (b - a) = 0 := by grind
  suffices (c * (b - a) + eval a (derivative f)) ∉ maximalIdeal R by
    rw [notMem_maximalIdeal, isUnit_iff_exists] at this
    grind
  by_contra!
  replace this := (maximalIdeal R).add_mem this ((maximalIdeal R).mul_mem_left c h)
  ring_nf at this
  contradiction
