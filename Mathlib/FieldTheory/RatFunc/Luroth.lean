/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Lüroth's theorem

The goal of this project is to prove Lüroth's theorem, which says that for every field K,
every intermediate field between K and the rational function field K(X) is either K or
isomorphic to K(X) as an K-algebra. The proof depends on the following lemma on degrees of
rational functions:

If `f` is a rational function, i.e. an element in the field `K(X)` (`FractionRing K[X]`)
for some field `K`, we can write `f = p / q` where `p` and `q` are coprime polynomials in `K[X]`
with `q` nonzero.

We define the degree of `f` to be the larger of the degrees (`Polynomial.natDegree`)
of `p` and `q`. It turns out that if `f` is not a constant, its degree is equal to the degree of
the field extension K(X)/K(f) (`Module.finrank K⟮f⟯ (FractionRing K[X])`).

(In fact, since `finrank` is defined to be 0 when the extension is infinite,
the equality continue to hold even when `f` is a constant.)

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

variable {K : Type*} [Field K]

namespace Polynomial

open Polynomial

noncomputable abbrev swap : K[X][X] ≃+* K[X][X] :=
  .ofRingHom (eval₂RingHom (mapRingHom C) (C X)) (eval₂RingHom (mapRingHom C) (C X))
    (by ext <;> simp) (by ext <;> simp)

@[simp]
theorem swap_C (e : K[X]) : swap (C e) = e.map (algebraMap K K[X]) := by simp

@[simp]
theorem swap_X : swap (X : K[X][X]) = C X := by simp

end Polynomial

namespace RatFunc

open IntermediateField
open scoped Polynomial

variable (f : RatFunc K)

theorem constant_iff_natDegree_num_denom :
    (∃ c, f = C c) ↔ f.num.natDegree = 0 ∧ f.denom.natDegree = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · rintro ⟨h₁, h₂⟩
    rw [Polynomial.natDegree_eq_zero] at h₁ h₂
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    use a / b
    rw [←num_div_denom f, ←ha, ←hb]
    simp

theorem adjoin_X_eq_top : K⟮(X : RatFunc K)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem adjoin_f_adjoin_X_eq_top : K⟮f⟯⟮(X : RatFunc K)⟯ = ⊤ := by
  rw [←restrictScalars_eq_top_iff (K := K), adjoin_simple_adjoin_simple, eq_top_iff]
  exact le_trans (le_of_eq adjoin_X_eq_top.symm) (IntermediateField.adjoin.mono _ _ _ (by simp))

noncomputable def adjoin_f_adjoin_X_equiv : K⟮f⟯⟮(X : RatFunc K)⟯ ≃ₐ[K⟮f⟯] RatFunc K :=
  (IntermediateField.equivOfEq (adjoin_f_adjoin_X_eq_top f)).trans IntermediateField.topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. -/
noncomputable abbrev minpoly_X : K⟮f⟯[X] :=
  f.num.map (algebraMap K K⟮f⟯) -
  Polynomial.C (AdjoinSimple.gen K f) * f.denom.map (algebraMap K K⟮f⟯)

@[simp]
theorem C_minpoly_X (x : K) : minpoly_X (C x) = 0 := by
  simp only [num_C, Polynomial.map_C, denom_C, Polynomial.map_one, mul_one, sub_eq_zero,
    Polynomial.C_inj]
  rfl

theorem minpoly_X_aeval_X : f.minpoly_X.aeval (X : RatFunc K) = 0 := by
  simp only [Polynomial.aeval_sub, Polynomial.aeval_map_algebraMap, aeval_X_left_eq_algebraMap,
    map_mul, Polynomial.aeval_C, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen]
  nth_rw 2 [←num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem is_constant_of_minpoly_X_coeff_eq_zero
    (hf : f.minpoly_X.coeff f.denom.natDegree = (0 : RatFunc K)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((map_ne_zero C).mpr
    (Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpoly_X_eq_zero_iff : f.minpoly_X = 0 ↔ ∃ c, f = C c := by
  refine ⟨fun h ↦ f.is_constant_of_minpoly_X_coeff_eq_zero (by simp [h]), ?_⟩
  rintro ⟨c, rfl⟩
  exact C_minpoly_X c

theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : RatFunc K) :=
   ⟨f.minpoly_X, fun H ↦ hf (f.minpoly_X_eq_zero_iff.mp H), f.minpoly_X_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' (hf : ¬∃ c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have P: Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : RatFunc K)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact f.adjoin_f_adjoin_X_equiv.isAlgebraic

theorem finrank_eq_natDegree_minpoly :
    Module.finrank K⟮f⟯ (RatFunc K) = (minpoly K⟮f⟯ (X : RatFunc K)).natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦  ?_, minpoly.eq_zero fun H ↦ ?_,
      Polynomial.natDegree_zero]
    · exact transcendental_X (Subalgebra.isAlgebraic_of_isAlgebraic_bot H.isAlgebraic)
    · exact Algebra.transcendental_iff_not_isAlgebraic.mp transcendental <|
        Algebra.IsAlgebraic.of_finite K (RatFunc K)
  rw [←(adjoin_f_adjoin_X_equiv f).toLinearEquiv.finrank_eq]
  exact IntermediateField.adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral

theorem natDegree_minpoly_X : f.minpoly_X.natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : f.minpoly_X.natDegree ≤ _ := Polynomial.natDegree_sub_le _ _
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C_mul fun H ↦
      hf ⟨0, by simpa [map_zero] using congr_arg Subtype.val H⟩,
      Polynomial.natDegree_map] at this
    exact this
  · apply max_le
    · sorry
    · exact Polynomial.le_natDegree_of_ne_zero
        (fun H ↦ hf (f.is_constant_of_minpoly_X_coeff_eq_zero (congr_arg Subtype.val H)))

theorem transcendental_of_not_constant (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have h₄ : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at h₄
  exact h₄ <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem transcendental_of_not_constant' (hf : ¬∃ c, f = C c) :
    Transcendental K (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}):= by
  rw [←transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (Algebra.adjoin K {f}) (RatFunc K))]
  exact f.transcendental_of_not_constant hf

noncomputable def adjoinSimpleEquiv (hf : ¬∃ c, f = C c) :
    K[X] ≃ₐ[K] (Algebra.adjoin K {f}) :=
  AlgEquiv.ofBijective (Polynomial.aeval ⟨f, Algebra.self_mem_adjoin_singleton K f⟩) <| by
    refine ⟨transcendental_iff_injective.mp (f.transcendental_of_not_constant' hf), ?_⟩
    rw [←AlgHom.range_eq_top, eq_top_iff]
    rintro ⟨g, g_mem⟩ _
    obtain ⟨r, hr⟩ := Algebra.adjoin_mem_exists_aeval _ _ g_mem
    use r
    ext
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [←hr, Polynomial.coe_aeval_mk_apply]

@[simp]
theorem adjoinSimpleEquiv_coe (hf : ¬∃ c, f = C c) :
    (f.adjoinSimpleEquiv hf : K[X] →+* Algebra.adjoin K {f}) =
    Polynomial.aeval (R := K) 
      (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}) := rfl

@[simp]
theorem adjoinSimpleEquiv_apply (hf : ¬∃ c, f = C c) (g : K[X]) :
    f.adjoinSimpleEquiv hf g =
    Polynomial.aeval (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : Algebra.adjoin K {f}) g := rfl

def adjoin_f_NormalizedGCDMonoid (hq : 0 < q.natDegree) : NormalizedGCDMonoid K[f] :=
  have : UniqueFactorizationMonoid K[f]
    := (adjoinSimpleEquiv p q coprime hq).toMulEquiv.uniqueFactorizationMonoid inferInstance
  Nonempty.some inferInstance

lemma algEquivOfTranscendental_apply_X (hq : 0 < q.natDegree) :
    adjoinSimpleEquiv p q coprime hq X = ⟨f, Algebra.subset_adjoin rfl⟩ := by
  rw [algEquivOfTranscendental_apply, Subtype.ext_iff, coe_aeval_mk_apply, aeval_X]

/- Since K[f] is isomorphic to K[X] and K[X] is integrally closed, K[f] is also integrally closed.-/
theorem isIntegrallyClosed_adjoin_div (hq : 0 < q.natDegree) : IsIntegrallyClosed K[f] :=
  .of_equiv (adjoinSimpleEquiv p q coprime hq).toRingEquiv

variable (lt : q.natDegree ≤ p.natDegree)
include lt

/- By `minpoly.eq_iff_aeval_eq_zero`, to show that `minpolyDiv p q` is indeed the minimal
polynomial of X over K(f), it suffices to show it is irreducible.
The key lemma `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (due to Gauss)
shows that it suffices to show it is irreducible over K[f]. -/

/-- Same as `minpolyDiv` but as a polynomial over K[f] instead of K(f). -/
def minpolyDiv' : K[f][X] :=
  p.map (algebraMap ..) - C ⟨f, Algebra.subset_adjoin rfl⟩ * q.map (algebraMap ..)

open scoped IntermediateField.algebraAdjoinAdjoin

omit coprime lt in
theorem map_minpolyDiv' : (minpolyDiv' p q).map (algebraMap ..) = minpoly_X p q := by
  simp only [minpolyDiv', Polynomial.map_sub, Polynomial.map_mul, map_C]
  congr 1
  · rw [map_map, ←IsScalarTower.algebraMap_eq]
  · rw [map_map, ←IsScalarTower.algebraMap_eq]
    simp only [mul_eq_mul_right_iff, C_inj]
    exact .inl rfl

theorem natDegree_minpolyDiv' (hq : 0 < q.natDegree) :
    (minpolyDiv' p q).natDegree = max p.natDegree q.natDegree := by
  rw [←natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ K⟮f⟯) (minpolyDiv' p q),
    map_minpolyDiv']
  exact natDegree_minpolyDiv p q coprime lt hq

omit lt in
theorem algEquivOfTranscendental_swap_C_sub_C_X (hq : 0 < q.natDegree) :
    map (adjoinSimpleEquiv p q coprime hq) (swap (C p - X * C q)) = minpolyDiv' p q := by
  rw [map_sub, map_mul, swap_C, swap_C, swap_X]
  simp only [algEquivOfTranscendental_coe, algebraMap_eq, Polynomial.map_sub, Polynomial.map_mul,
    map_C, RingHom.coe_coe, aeval_X]
  rw [map_map, map_map]
  congr 2 <;> ext <;> simp

omit coprime lt in
lemma C_sub_X_mul_C_natDegree_eq_one (hq : q ≠ 0) : (C p - X * C q).natDegree = 1 := by
  rw [show C p - X * C q = C (- q) * X + C p by simp only [X_mul_C, map_neg, neg_mul]; ring]
  exact natDegree_linear (neg_ne_zero.mpr hq)

omit lt in
lemma C_p_neg_X_mul_C_q_isPrimitive (hq : q ≠ 0) : (C p - X * C q).IsPrimitive := by
  classical
  rw [isPrimitive_iff_content_eq_one, content_eq_gcd_leadingCoeff_content_eraseLead]
  have leadingCoeff_eq : (C p - X * C q).leadingCoeff = -q := by
    rw [leadingCoeff, C_sub_X_mul_C_natDegree_eq_one p q hq]
    simp only [X_mul_C, coeff_sub, coeff_C_succ, coeff_mul_X, coeff_C_zero, zero_sub]
  rw [leadingCoeff_eq]
  have eraseLead_eq : (C p - X * C q).eraseLead = C p := by
    rw [sub_eq_add_neg, eraseLead_add_of_natDegree_lt_right, X_mul_C, add_eq_left,
      neg_mul_eq_neg_mul, ←C_neg, eraseLead_C_mul_X]
    · rw [natDegree_C, X_mul_C, natDegree_neg, natDegree_C_mul_X _ hq]
      exact zero_lt_one
  rwa [eraseLead_eq, content_C, ← normalize_gcd, normalize_eq_one, gcd_isUnit_iff,
    normalize_apply, isCoprime_mul_unit_right_right (normUnit p).isUnit, IsCoprime.neg_left_iff,
    isCoprime_comm]

omit lt in
theorem irreducible_mul_X_sub (hq : q ≠ 0) : Irreducible (C p - X * C q) := by
  classical
  have hnezero : C p - X * C q ≠ 0 := by
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [C_sub_X_mul_C_natDegree_eq_one p q hq]
    exact zero_lt_one
  apply Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective
    (FaithfulSMul.algebraMap_injective K[X] K(X)) (C_p_neg_X_mul_C_q_isPrimitive p q coprime hq)
  apply Polynomial.irreducible_of_degree_eq_one
  rw [degree_eq_natDegree, Nat.cast_eq_one, ← C_sub_X_mul_C_natDegree_eq_one p q hq,
    natDegree_map_eq_iff]
  · simp only [X_mul_C, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, leadingCoeff_eq_zero]
    left
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [mul_comm]
    rw [C_sub_X_mul_C_natDegree_eq_one p q hq]
    exact zero_lt_one
  exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K[X] K(X))).mpr hnezero

omit lt in
theorem irreducible_minpolyDiv' (hq : 0 < q.natDegree) : Irreducible (minpolyDiv' p q) := by
  rw [←algEquivOfTranscendental_swap_C_sub_C_X p q coprime hq, ←AlgEquiv.toRingEquiv_toRingHom,
    ←mapEquiv_apply, MulEquiv.irreducible_iff, MulEquiv.irreducible_iff]
  exact irreducible_mul_X_sub p q coprime (ne_zero_of_natDegree_gt hq)

theorem irreducible_minpolyDiv (hq : 0 < q.natDegree) : Irreducible (minpoly_X p q) := by
  have : NormalizedGCDMonoid K[f] := adjoin_f_NormalizedGCDMonoid p q coprime hq
  rw [←map_minpolyDiv', ←IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact irreducible_minpolyDiv' p q coprime hq
  apply (irreducible_minpolyDiv' p q coprime hq).isPrimitive
  rw [natDegree_minpolyDiv' p q coprime lt hq]
  simp only [ne_eq, Nat.max_eq_zero_iff, not_and]
  intro H
  exact Nat.ne_zero_of_lt hq

theorem minpolyDiv_eq_minpoly (hq : 0 < q.natDegree) :
    (minpoly_X p q).natDegree = (minpoly K⟮f⟯ rfX).natDegree := by
  rw [←minpoly.eq_of_irreducible (irreducible_minpolyDiv p q coprime lt hq), mul_comm,
    natDegree_C_mul]
  · apply inv_ne_zero
    rw [leadingCoeff_ne_zero]
    exact minpolyDiv_ne_zero p q coprime hq
  apply minpolyDiv_aeval
  exact ne_zero_of_natDegree_gt hq

-- Finally we conclude:
theorem finrank_eq_max_natDegree (hq : 0 < q.natDegree) :
    Module.finrank K⟮f⟯ K(X) = max p.natDegree q.natDegree := by
  rw [finrank_eq_natDegree_minpoly p q coprime hq, ←minpolyDiv_eq_minpoly p q coprime lt hq]
  exact natDegree_minpolyDiv p q coprime lt hq

/-
Now we are ready to attack Lüroth's theorem.
Let `E` be an intermediate field between `K` and `K(X)`,
we must show that `E = K⟮f⟯` for some `f : K(X)` transcendental over `K`.
-/

end

end Polynomial

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
theorem IntermediateField.adjoin_inv {x : L} :
    adjoin K {x⁻¹} = adjoin K {x} :=
  le_antisymm (adjoin_le_iff.mpr <| by simpa using mem_adjoin_simple_self K x)
    (adjoin_le_iff.mpr <| by rintro _ rfl; apply inv_mem_iff.mp; exact mem_adjoin_simple_self K _)

end

open Polynomial

/- First it is easy to show that `K(X)` does not contain any algebraic element over `K` other than
elements of `K`. Proof: use (a generalized version of) `transcendental_div`.
Potentially useful: `Localization.rec` and `FractionRing.mk_eq_div`. -/
instance : IsIntegrallyClosedIn K K(X) := by
  sorry

variable (E : IntermediateField K K(X)) (hE : E ≠ ⊥)
include hE

instance : Algebra.IsAlgebraic E K(X) := by
  have h₁ : ∃ p q : K[X], IsCoprime p q ∧ ¬ (p.natDegree = 0 ∧ q.natDegree = 0) ∧ p.toRatFunc / q.toRatFunc ∈ E := by
    have h₂ : ∃ f ∈ E, K⟮f⟯ ≠ ⊥ := by
      have g₁ : ¬ (E ≤ ⊥) := by
          rwa [le_bot_iff]
      rw [SetLike.not_le_iff_exists] at g₁
      rcases g₁ with ⟨x, xin, xnotin⟩
      use x
      constructor
      · exact xin
      · contrapose xnotin
        push_neg
        rw [← IntermediateField.adjoin_simple_eq_bot_iff]
        push_neg at xnotin
        exact xnotin
    rcases h₂ with ⟨f, finE, fnotinK⟩
    have h₃ : ∃ p q : K[X], IsCoprime p q ∧ f = p.toRatFunc / q.toRatFunc := by
      exact FractionRing.exists_isCoprime_eq_div f
    rcases h₃ with ⟨p, q, coprimepq, feqpdivq⟩
    use p
    use q
    constructor
    · exact coprimepq
    · constructor
      · intro h
        rw [← adjoin_p_dvd_q_eq_bot_iff p q coprimepq] at h
        rw [← feqpdivq] at h
        contradiction
      · rw [← feqpdivq]
        exact finE
  rcases h₁ with ⟨p, q, rest⟩
  have h₄ : Algebra.IsAlgebraic K⟮p.toRatFunc / q.toRatFunc⟯ K(X) := by
    by_cases hq : 0 < q.natDegree
    · exact isAlgebraic_adjoin_div p q rest.1 hq
    · have h₅ : q.natDegree = 0 := by
        exact Nat.eq_zero_of_not_pos hq
      have h₆ : 0 < p.natDegree := by
        rcases rest with ⟨coprime, degree, quotient⟩
        push_neg at degree
        contrapose degree
        push_neg
        constructor
        · exact Nat.eq_zero_of_not_pos degree
        · exact h₅
      have h₇ : K⟮toRatFunc p / toRatFunc q⟯ = K⟮toRatFunc q / toRatFunc p⟯ := by
        have h₈ : toRatFunc p / toRatFunc q = (toRatFunc q / toRatFunc p)⁻¹ := by
          exact Eq.symm (inv_div (toRatFunc q) (toRatFunc p))
        rw [h₈]
        exact IntermediateField.adjoin_inv K K(X)
      rw [h₇]
      have h₉ : IsCoprime q p := by
        have g₂ : IsCoprime p q := by
          exact rest.1
        exact id (IsCoprime.symm g₂)
      exact isAlgebraic_adjoin_div q p h₉ h₆
  have h₅ : K⟮p.toRatFunc / q.toRatFunc⟯ ≤ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact rest.2.2
  let : Algebra K⟮p.toRatFunc / q.toRatFunc⟯ E := (IntermediateField.inclusion h₅).toAlgebra
  have : IsScalarTower K⟮p.toRatFunc / q.toRatFunc⟯ E K(X) := .of_algebraMap_eq fun _ _ _ => rfl
  apply Algebra.IsAlgebraic.tower_top (K := K⟮p.toRatFunc / q.toRatFunc⟯)

/-- The minimal polynomial of `X : K(X)` over an intermediate field `E`. -/
noncomputable def IntermediateField.minpolyX : E[X] :=
  minpoly E (X : K[X]).toRatFunc

/- Write each coefficient as a rational function such that the numerator and denominator
  are coprime. Then multiply the minimal polynomial with the least common multiple of
  the denominators. The resulting polynomial over `K(X)` is primitive. -/

/- Since `X` is not algebraic over K, the minimal polynomial of `X` over `E`
  must have a coefficient not contained in `K`. -/
lemma minpolyX_existence_coeff_transcendent : ∃ j : ℕ, IntermediateField.minpolyX.coeff j ∉ K := by
  sorry

/- Choose such a coefficient and call this `uj`, write `uj` as a fraction of coprime polynomials
  `p` and `q` over `K[X]`. The field `K(uj)` is a subfield of `E` of degree
  `max p.natDegree q.natDegree` by above.
  The goal is to show that these two fields are equal. This implies luroth.
  For this it suffices to show that `max p.natDegree q.natDegree` is smaller or equal than
  the degree of `IntermediateField.minpolyX`. -/


-- TODO: fill in more details here from [Cohn] and [Jacobson]

theorem luroth : ∃ f : K(X), Transcendental K f ∧ E = K⟮f⟯ := by
  sorry

