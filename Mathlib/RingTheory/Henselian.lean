/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.IdempotentInstances
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.IsIntegral
public import Mathlib.RingTheory.Unramified.LocalStructure

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
* `IsAdicComplete.henselianRing`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`
* `HenselianLocalRing.ofId_comp_bijective`: The étale lifting property for Henselian local rings:
  If `R` is a Henselian local ring with residue field `k`, then for any étale `R`-algebra `A`,
  every `A →ₐ[R] k` lifts uniquely to an `A →ₐ[R] R`.
* `HenselianLocalRing.of_finite`: Finite local extensions of Henselian local rings are Henselian.
* `HenselianLocalRing.algEquivEquiv`: If `A` is finite local étale over a Henselian local ring `R`,
  then `Aut(A/R) ≃ Gal(k(A)/k(R))`.

## References

https://stacks.math.columbia.edu/tag/04GE

-/

public section


noncomputable section

universe u v

open Polynomial IsLocalRing List
open scoped Ring

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

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

theorem HenselianLocalRing.TFAE (R : Type u) [CommRing R] [IsLocalRing R] :
    TFAE
      [HenselianLocalRing R,
        ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
          aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀,
        ∀ {K : Type u} [Field K],
          ∀ (φ : R →+* K), Function.Surjective φ → ∀ f : R[X], f.Monic → ∀ a₀ : K,
            f.eval₂ φ a₀ = 0 → f.derivative.eval₂ φ a₀ ≠ 0 → ∃ a : R, f.IsRoot a ∧ φ a = a₀] := by
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
  tfae_have 1 → 3
  | hR, K, _K, φ, hφ, f, hf, a₀, h₁, h₂ => by
    obtain ⟨a₀, rfl⟩ := hφ a₀
    have H := HenselianLocalRing.is_henselian f hf a₀
    simp only [← ker_eq_maximalIdeal φ hφ, eval₂_at_apply, RingHom.mem_ker] at H h₁ h₂
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ (by
      contrapose h₂
      rwa [← mem_nonunits_iff, ← mem_maximalIdeal, ← ker_eq_maximalIdeal φ hφ,
        RingHom.mem_ker] at h₂)
    refine ⟨a, ha₁, ?_⟩
    rwa [φ.map_sub, sub_eq_zero] at ha₂
  tfae_finish

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

open Polynomial TensorProduct KaehlerDifferential

open nonZeroDivisors

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
/-- If `R` is a local ring with residue field `k`, then for any étale `R`-algebra `A`,
every `A →ₐ[R] k` lifts to at most one an `A →ₐ[R] R`. -/
lemma IsLocalRing.ofId_comp_injective [Algebra.Etale R A] [IsLocalRing R] :
    Function.Injective ((Algebra.ofId R 𝓀[R]).comp : (A →ₐ[R] R) → (A →ₐ[R] 𝓀[R])) := by
  intro f₁ f₂ H
  wlog _ : Algebra.IsStandardEtale R A
  · let P := RingHom.ker ((IsScalarTower.toAlgHom R R 𝓀[R]).comp f₁).toRingHom
    have inst : P.IsPrime := RingHom.ker_isPrime _
    obtain ⟨r, hrP, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) P
    have hf₁ : IsUnit (f₁ r) := by
      rw [← residue_ne_zero_iff_isUnit]
      exact hrP
    have hf₂ : IsUnit (f₂ r) := by
      rw [← residue_ne_zero_iff_isUnit]
      refine congr($H r).symm.trans_ne hrP
    have : IsLocalization.liftAlgHom (S := Localization.Away r) (f := f₁) (M := .powers r)
          (by simp [Submonoid.mem_powers_iff, hf₁.pow _]) =
        IsLocalization.liftAlgHom (f := f₂) (M := .powers r)
          (by simp [Submonoid.mem_powers_iff, hf₂.pow _]) := by
      refine this (IsLocalization.algHom_ext (.powers r) ?_) inferInstance
      ext x
      simpa [Algebra.algHom] using congr($H x)
    ext x
    simpa using congr($this (algebraMap _ _ x))
  obtain ⟨𝓟⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := A)
  apply 𝓟.hom_ext
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := 𝓟.f)
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]
  · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact congr($H _)
  · rw [← coe_aeval_eq_eval, aeval_algHom_apply]
    simpa using 𝓟.hasMap.isUnit_derivative_f.map f₁

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
/-- If `R` is a Henselian local ring with residue field `k`, then for any étale `R`-algebra `A`,
every `A →ₐ[R] k` lifts uniquely to an `A →ₐ[R] R`. -/
@[stacks 04GG "(1) => (7)"]
lemma HenselianLocalRing.ofId_comp_bijective [Algebra.Etale R A] [HenselianLocalRing R] :
    Function.Bijective ((Algebra.ofId R 𝓀[R]).comp : (A →ₐ[R] R) → (A →ₐ[R] 𝓀[R])) := by
  refine ⟨IsLocalRing.ofId_comp_injective, fun f ↦ ?_⟩
  let P := RingHom.ker f.toRingHom
  have : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨r, hrP, ⟨⟨𝓟⟩⟩⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) P
  let φ : Localization.Away r →ₐ[R] 𝓀[R] :=
    IsLocalization.liftAlgHom (M := .powers r) (f := f) <| Subtype.forall.mpr <|
      show Submonoid.powers r ≤ (IsUnit.submonoid _).comap _ from Submonoid.powers_le.mpr
      (by simpa [IsUnit.mem_submonoid_iff])
  obtain ⟨x, hx⟩ := residue_surjective (φ 𝓟.x)
  obtain ⟨y, hy, hxy⟩ := HenselianLocalRing.is_henselian 𝓟.f 𝓟.monic_f x (by
    rw [← residue_eq_zero_iff, ← ResidueField.algebraMap_eq, eval, hom_eval₂, RingHom.comp_id,
      ← aeval_def, ResidueField.algebraMap_eq, hx, aeval_algHom_apply, 𝓟.hasMap.1, map_zero]) (by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, eval, hom_eval₂,
      RingHom.comp_id, ← aeval_def, ResidueField.algebraMap_eq, hx, aeval_algHom_apply]
    exact (𝓟.hasMap.isUnit_derivative_f.map φ).ne_zero)
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hxy
  have Hy : 𝓟.HasMap y := by
    refine ⟨hy, ?_⟩
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq, ← aeval_algebraMap_apply,
      ResidueField.algebraMap_eq, hxy, hx, aeval_algHom_apply]
    exact (𝓟.hasMap.2.map φ).ne_zero
  refine ⟨((𝓟.lift _ Hy).comp 𝓟.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom _ _ _), ?_⟩
  trans ((φ.comp 𝓟.equivRing.symm.toAlgHom).comp 𝓟.equivRing.toAlgHom).comp
      (IsScalarTower.toAlgHom _ _ _)
  · simp_rw [← AlgHom.comp_assoc]
    congr 2
    ext
    simp [hxy, hx]
  · ext; simp [φ]

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
set_option backward.isDefEq.respectTransparency false in
/-- A finite algebra over a Henselian local ring is a product of (Henselian) local rings.
(See `HenselianLocalRing.of_finite` for the Henselian part)

TODO: show that the local rings are exactly `Aₘ` with `m` maximal ideals of `A`. -/
@[stacks 04GG "(1) => (10)"]
lemma HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    [HenselianLocalRing R] [Module.Finite R A] :
    ∃ (n : ℕ) (e : Fin n → A) (he : CompleteOrthogonalIdempotents e),
      ∀ i, IsLocalRing (he.idem i).Corner := by
  obtain ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hP, hP', H⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (R := R) (S := A) 𝓂[R]
  let φ : 𝓀[R] ≃ₐ[R] 𝓂[R].ResidueField := .ofBijective
    (IsScalarTower.toAlgHom R (R ⧸ 𝓂[R]) 𝓂[R].ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField _)
  let φ' := φ.trans (AlgEquiv.ofBijective _ hP)
  obtain ⟨ψ, hψ⟩ := HenselianLocalRing.ofId_comp_bijective.surjective
    (φ'.symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' _))
  have hPeq : P = 𝓂[R].comap ψ.toRingHom := by
    trans RingHom.ker (IsScalarTower.toAlgHom R R' P.ResidueField).toRingHom
    · exact P.ker_algebraMap_residueField.symm
    · rw [← RingHom.ker_comp_of_injective _ (f := RingHomClass.toRingHom φ'.symm) φ'.symm.injective,
        ← AlgEquiv.toAlgHom_toRingHom, AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, ← hψ,
        AlgHom.comp_toRingHom, ← RingHom.comap_ker, ← 𝓂[R].mk_ker]; rfl
  have hψ : Function.Surjective ψ.toRingHom := fun x ↦ ⟨algebraMap _ _ x, by simp⟩
  have : P.IsMaximal := by rw [hPeq]; exact Ideal.comap_isMaximal_of_surjective _ hψ
  let ψ' : R' ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId _ _).comp ψ) (.id R A) fun _ _ ↦ .all _ _
  have hψ' : Function.Surjective ψ'.toRingHom := fun x ↦ ⟨1 ⊗ₜ x, by simp [ψ']⟩
  have h₁ : ψ' (e (.last _)) = 0 := by
    suffices IsUnit (1 - ψ' (e (Fin.last n))) by
      simpa using this.mul_left_cancel
        (((he.idem (.last n)).map ψ').one_sub.eq.trans (mul_one _).symm)
    by_contra he'
    obtain ⟨M, hM, heM⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ψ' (e (Fin.last n))}) (by simpa)
    have := (H (M.comap ψ'.toRingHom) inferInstance ⟨by
      rw [Ideal.under, Ideal.comap_comap]
      trans M.comap ((algebraMap R A).comp ψ.toRingHom); swap
      · congr 1; ext; simp [ψ']
      · rw [hPeq, ← Ideal.comap_comap,
          eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) M)]⟩).1
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_comap, RingHom.coe_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe] at this heM
    exact Ideal.one_notMem M (by convert add_mem this heM; ring)
  refine ⟨n, ψ' ∘ e ∘ Fin.castSucc, ⟨(he.map ψ'.toRingHom).1.embedding Fin.castSuccEmb, ?_⟩, ?_⟩
  · simpa [Fin.sum_univ_castSucc, h₁] using (he.map ψ'.toRingHom).2
  · intro i
    have he₀ := (he.idem i.castSucc).map ψ'
    let Q := (P' i).comap Algebra.TensorProduct.includeRight.toRingHom
    have _ : (P' i).LiesOver 𝓂[R] := .trans _ P _
    have _ : Q.LiesOver 𝓂[R] :=
      inferInstanceAs (((P' i).comap Algebra.TensorProduct.includeRight).LiesOver _)
    have _ : (P' i).LiesOver 𝓂[R] := .trans _ P _
    have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _
      (by rw [← Ideal.under, ← Q.over_def 𝓂[R]]; infer_instance)
    have hψ' : Function.Surjective ψ'.toRingHom := fun x ↦ ⟨1 ⊗ₜ x, by simp [ψ']⟩
    have hQP' : Q.comap ψ'.toRingHom = P' i := by
      have : (Ideal.comap ψ'.toRingHom Q).LiesOver P := by
        rw [hPeq]
        simp only [Ideal.liesOver_iff, Ideal.under, Ideal.comap_comap, Q, (P' i).over_def 𝓂[R]]
        congr 1
        ext a; simp [ψ']
      apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
      simp only [Ideal.comap_comap, Q]
      congr 1; ext; simp [ψ']
    have hQP'' : (P' i).comap Algebra.TensorProduct.includeRight.toRingHom = Q := by
      rw [← hQP', Ideal.comap_comap]; convert Ideal.comap_id _; ext; simp [ψ']
    have heQ : RingHom.ker (algebraMap A he₀.Corner) ≤ Q := by
      rw [he₀.ker_algebraMap_corner, Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      rw [← Ideal.IsPrime.mul_mem_left_iff (I := Q) fun h ↦ hP' i (hQP'.le h)]
      simp [mul_sub, ← map_mul, (he.idem _).eq]
    have := Ideal.IsMaximal.map_of_surjective_of_ker_le he₀.algebraMap_corner_surjective heQ
    refine IsLocalRing.of_unique_max_ideal ⟨Q.map (algebraMap A he₀.Corner), ‹_›, fun Q' hQ' ↦ ?_⟩
    have inst := Ideal.comap_isMaximal_of_surjective _ he₀.algebraMap_corner_surjective (K := Q')
    refine (hQ'.eq_of_le this.ne_top ?_)
    refine Ideal.le_map_of_comap_le_of_surjective _ he₀.algebraMap_corner_surjective ?_
    suffices (Q'.comap (algebraMap A _)).comap ψ'.toRingHom = P' i by
      rw [← hQP'', ← this, Ideal.comap_comap,]
      simp only [AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, ψ', Function.comp_apply, le_refl,
        Algebra.TensorProduct.lift_comp_includeRight', AlgHom.id_toRingHom, Ideal.comap_id]
    refine (H _ inferInstance ⟨?_⟩).2 _ ?_
    · rw [hPeq, ← eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R)
        (Q'.comap (algebraMap A he₀.Corner)))]
      simp only [Ideal.under, Ideal.comap_comap, RingHom.comp_assoc]
      congr 2; ext; simp [ψ']
    · have : algebraMap _ he₀.Corner (ψ' (e i.castSucc)) = 1 := Subtype.ext ((he.idem _).map ψ')
      simpa [this] using Ideal.one_notMem Q'

attribute [local instance] RingHom.ker_isPrime in
private theorem HenselianLocalRing.of_finite_aux [IsLocalRing A]
    (f : A[X]) (a₀ : A) (ha₀ : eval a₀ f ∈ 𝓂[A])
    (ha₀' : IsUnit (eval a₀ (derivative f))) (e : AdjoinRoot f)
    (he : IsIdempotentElem e) [IsLocalRing he.Corner]
    (ha₀'' : AdjoinRoot.liftAlgHom _ (Algebra.ofId _ 𝓀[A]) (algebraMap _ _ a₀)
      (by simpa using ha₀) e ≠ 0) :
    1 ⊗ₜ[A] (algebraMap (AdjoinRoot f) he.Corner) (AdjoinRoot.root f) = residue A a₀ ⊗ₜ[A] 1 := by
  let φ : AdjoinRoot f →ₐ[A] 𝓀[A] := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap _ _ a₀) (by simpa using ha₀)
  have hφ : Function.Surjective φ := residue_surjective.forall.mpr fun x ↦ ⟨.of f x, by simp [φ]⟩
  set root := (1 : 𝓀[A]) ⊗ₜ[A] algebraMap _ he.Corner (AdjoinRoot.root f)
  obtain ⟨g, hg⟩ : X - C (residue A a₀) ∣ f.map (residue A) := by
    simpa [dvd_iff_isRoot, eval_map] using ha₀
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective _ residue_surjective g
  have hga₀ : IsUnit (eval a₀ g) := by
    rw [← residue_ne_zero_iff_isUnit, ← ResidueField.algebraMap_eq,
      eval, hom_eval₂, RingHom.comp_id, ← eval_map, ResidueField.algebraMap_eq] at ha₀' ⊢
    rw [← derivative_map, hg] at ha₀'
    simpa using ha₀'
  let φ' : he.Corner →ₐ[A] 𝓀[A] := by
    refine AlgHom.liftOfSurjective (IsScalarTower.toAlgHom _ _ _)
      he.algebraMap_corner_surjective φ ?_
    refine he.ker_algebraMap_corner.trans_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [← Ideal.IsPrime.mul_mem_left_iff (by exact ha₀''), mul_sub, mul_one, he.eq, sub_self]
    exact zero_mem _
  have hφ' (x : AdjoinRoot f) : φ' (algebraMap _ _ x) = φ x :=
    AlgHom.liftOfSurjective_apply ..
  have hφ'' : IsLocalHom φ'.toRingHom :=
    .of_surjective _ (AlgHom.liftOfSurjective_surjective _ _ _ _ hφ)
  have hrootf : aeval root f = 0 := by
    refine (aeval_algHom_apply Algebra.TensorProduct.includeRight _ _).trans ?_
    simp [aeval_algebraMap_apply]
  have hrootg : IsUnit (aeval root g) := by
    have := hφ''.1 (algebraMap _ _ (AdjoinRoot.mk f g)) (by simpa [hφ', φ])
    convert this.map (Algebra.TensorProduct.includeRight : _ →ₐ[A] 𝓀[A] ⊗[A] he.Corner)
    rw [← AdjoinRoot.aeval_eq, ← aeval_algebraMap_apply, ← aeval_algHom_apply]
    rfl
  rw [← sub_eq_zero, ← hrootg.mul_left_inj]
  simpa [← ResidueField.algebraMap_eq, hrootf, -mul_eq_zero, -mul_eq_left₀, -mul_eq_right₀] using
    congr(aeval root $hg).symm

/-- A finite local ring over a Henselian local ring is also Henselian.

This proof hides the fact that
(every finite extension is a product of local rings) implies henselian.

Consider splitting this fact out (if useful) once we have a nice way of stating the
former condition (as `Function.Surjective (MaximalSpectrum.toPiLocalization R)`). -/
lemma HenselianLocalRing.of_finite
    [HenselianLocalRing R] [Module.Finite R A] [IsLocalRing A] : HenselianLocalRing A := by
  refine ⟨fun f hf a₀ ha₀ ha₀' ↦ ?_⟩
  have := hf.finite_adjoinRoot
  have := hf.free_adjoinRoot
  have : Module.Finite R (AdjoinRoot f) := .trans A _
  obtain ⟨n, e, he, h⟩ := HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing
    (R := R) (A := AdjoinRoot f)
  let φ : AdjoinRoot f →ₐ[A] 𝓀[A] := AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap _ _ a₀) (by simpa using ha₀)
  have hφ : Function.Surjective φ := residue_surjective.forall.mpr fun x ↦ ⟨.of f x, by simp [φ]⟩
  have : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hφ
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ RingHom.ker φ := by
    by_contra! H
    exact Ideal.one_notMem (RingHom.ker φ.toRingHom) (he.complete ▸ sum_mem fun i _ ↦ H i)
  have : Module.Free A (he.idem i).Corner := Module.free_of_flat_of_isLocalRing
  have hroot :
      1 ⊗ₜ algebraMap _ (he.idem i).Corner (AdjoinRoot.root f) = residue A a₀ ⊗ₜ[A] 1 :=
    HenselianLocalRing.of_finite_aux f a₀ ha₀ ha₀' _ (he.idem i) hi
  have H : Function.Surjective (algebraMap 𝓀[A] (𝓀[A] ⊗[A] (he.idem i).Corner)) := by
    intro x
    obtain ⟨x, rfl⟩ := Algebra.TensorProduct.includeRight_surjective _
      (by exact residue_surjective) x
    obtain ⟨x, rfl⟩ := (he.idem i).algebraMap_corner_surjective x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have h₁ : residue _ (eval a₀ g) = φ (.mk f g) := by simp [φ]
    have h₂ : (IsScalarTower.toAlgHom _ _ (𝓀[A] ⊗[A] (he.idem i).Corner)).comp φ =
        Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom _ _ _) := by
      ext; simp [φ, ← hroot]
    use algebraMap _ _ (aeval a₀ g)
    trans algebraMap _ _ (eval a₀ g)
    · simp
    · simpa [φ] using congr($h₂ (.mk f g))
  have : Module.finrank A (he.idem i).Corner = 1 := by
    apply le_antisymm ?_ ((Module.finrank_pos_iff_of_free _ _).mpr inferInstance)
    · rw [← Module.finrank_baseChange (R := 𝓀[A]), finrank_le_one_iff]
      refine ⟨1, H.forall.mpr fun x ↦ ⟨x, by simp [Algebra.smul_def]⟩⟩
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap] at this
  obtain ⟨a, ha⟩ := this.2 (algebraMap _ _ (AdjoinRoot.root f))
  refine ⟨a, this.1 ?_, ?_⟩
  · rw [eval, hom_eval₂, RingHom.comp_id, ← aeval_def, ha, aeval_algebraMap_apply]
    simp
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    apply (algebraMap 𝓀[A] (𝓀[A] ⊗[A] (he.idem i).Corner)).injective
    trans Algebra.TensorProduct.includeRight (algebraMap _ _ a)
    · simp
    · rw [ha]; simp [← hroot]

/-- Let `R` be an henselian local ring, `A, B` be local `R`-algebras.
Suppose `A` is etale and `B` is module-finite, then any `k(R)`-algebra map `k(A) → k(B)` lifts to
an `R`-algebra map `A → B`.

See `HenselianLocalRing.eq_of_residueFieldMap_eq` for the uniqueness of the lift. -/
lemma HenselianLocalRing.exists_residueFieldMap_eq_of_etale [HenselianLocalRing R] [IsLocalRing A]
    [IsLocalHom (algebraMap R A)] [Algebra.Etale R A] [IsLocalRing B] [Module.Finite R B]
    (f : 𝓀[A] →ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A →ₐ[R] B) (_ : IsLocalHom g.toRingHom), ResidueField.map g.toRingHom = f.toRingHom := by
  have : HenselianLocalRing B := .of_finite (R := R)
  let f' : B ⊗[R] A →ₐ[B] 𝓀[B] :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((f.restrictScalars R).comp <| IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  obtain ⟨g, hg⟩ := HenselianLocalRing.ofId_comp_bijective.surjective f'
  let g' := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have H (x : _) : residue B (g' x) = f (residue _ x) := by
    trans f' (1 ⊗ₜ x)
    · exact congr($hg (1 ⊗ₜ x))
    · simp [f']
  have : IsLocalHom g'.toRingHom := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [← residue_ne_zero_iff_isUnit] at hx
    simpa [H, f'] using hx
  refine ⟨g', this, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp [ResidueField.map_residue, H]

lemma IsLocalRing.eq_of_residueFieldMap_eq
    [IsLocalRing A] [Algebra.Etale R A] [IsLocalRing B]
    (f₁ f₂ : A →ₐ[R] B) [IsLocalHom f₁.toRingHom] [IsLocalHom f₂.toRingHom]
    (H : ResidueField.map f₁.toRingHom = ResidueField.map f₂.toRingHom) : f₁ = f₂ := by
  have := (IsLocalRing.ofId_comp_injective (R := B) (A := B ⊗[R] A))
    (a₁ := (Algebra.TensorProduct.lift (Algebra.ofId _ _) f₁ fun _ _ ↦ .all _ _))
    (a₂ := (Algebra.TensorProduct.lift (Algebra.ofId _ _) f₂ fun _ _ ↦ .all _ _))
    (by ext a; simpa using congr($H (algebraMap _ _ a)))
  ext x
  simpa using congr($this (1 ⊗ₜ x))

lemma HenselianLocalRing.exist_algEquiv_residueFieldMap_eq_of_etale [HenselianLocalRing R]
    [IsLocalRing A] [Module.Finite R A] [Algebra.Etale R A]
    [IsLocalRing B] [Module.Finite R B] [Algebra.Etale R B]
    (f : 𝓀[A] ≃ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A ≃ₐ[R] B), ResidueField.map g.toRingHom = f.toRingHom := by
  obtain ⟨φ, hφ, hφ'⟩ := exists_residueFieldMap_eq_of_etale f.toAlgHom
  obtain ⟨ψ, hψ, hψ'⟩ := exists_residueFieldMap_eq_of_etale f.symm.toAlgHom
  have : φ.comp ψ = .id _ _ := by
    have : IsLocalHom (AlgHom.id R B).toRingHom := by dsimp; infer_instance
    have : IsLocalHom (φ.comp ψ).toRingHom := by
      dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢; exact RingHom.isLocalHom_comp _ _
    apply IsLocalRing.eq_of_residueFieldMap_eq
    dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢ hφ' hψ'
    simp only [ResidueField.map_comp, ResidueField.map_id, *]
    ext; simp
  have : ψ.comp φ = .id _ _ := by
    have : IsLocalHom (AlgHom.id R A).toRingHom := by dsimp; infer_instance
    have : IsLocalHom (ψ.comp φ).toRingHom := by
      dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢; exact RingHom.isLocalHom_comp _ _
    apply IsLocalRing.eq_of_residueFieldMap_eq
    dsimp [AlgHom.comp_toRingHom] at hφ hψ ⊢ hφ' hψ'
    simp only [ResidueField.map_comp, ResidueField.map_id, *]
    ext; simp
  exact ⟨.ofAlgHom φ ψ ‹_› ‹_›, hφ'⟩

/-- Suppose `R` is a henselian local ring and `A` is a finite étale local `R-`algebra.
Then `Aut(A/R) ≃ Gal(k(A)/k(R))`.

Paired with `galRestrict`, this shows that `Gal(Frac A / Frac R) ≃* Gal(k(A)/k(R))`. -/
def HenselianLocalRing.algEquivEquiv [HenselianLocalRing R]
    [IsLocalRing A] [Module.Finite R A] [Algebra.Etale R A] :
    (A ≃ₐ[R] A) ≃* Gal(𝓀[A]/𝓀[R]) :=
  .ofBijective (F := MonoidHom _ _)
    { toFun f :=
      { __ := ResidueField.mapEquiv f,
        commutes' r := by obtain ⟨r, rfl⟩ := residue_surjective r; simp  }
      map_one' := AlgEquiv.ext fun _ ↦ congr($ResidueField.map_id _)
      map_mul' f g :=
        AlgEquiv.ext fun x ↦ congr($(ResidueField.map_comp g.toRingHom f.toRingHom) x) } <|
    ⟨fun f g e ↦ AlgEquiv.coe_toAlgHom_injective (IsLocalRing.eq_of_residueFieldMap_eq
      f.toAlgHom g.toAlgHom congr(($e).toRingHom)), fun f ↦ by
    have ⟨g, hg⟩ := HenselianLocalRing.exist_algEquiv_residueFieldMap_eq_of_etale f
    exact ⟨g, AlgEquiv.ext fun _ ↦ congr($hg _)⟩⟩
