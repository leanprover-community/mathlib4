/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `GaloisField p n` is defined as the splitting field of `X^(p^n) - X` over `ZMod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `GaloisField p n` is a field with `p ^ n` elements

## Main Results

- `GaloisField.algEquivGaloisField`: Any finite field is isomorphic to some Galois field
- `FiniteField.algEquivOfCardEq`: Uniqueness of finite fields : algebra isomorphism
- `FiniteField.ringEquivOfCardEq`: Uniqueness of finite fields : ring isomorphism

-/


noncomputable section


open Polynomial Finset

open scoped Polynomial

instance FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  splits' := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [← splits_id_iff_splits, splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow,
      map_X, h, FiniteField.roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_rootSet' := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [rootSet, aroots, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_toFinset, coe_univ, Algebra.adjoin_univ]

theorem galois_poly_separable {K : Type*} [Field K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub, derivative_X_pow, derivative_X, C_eq_natCast, h]
  ring

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
-- deriving Field -- Porting note: see https://github.com/leanprover-community/mathlib4/issues/5020

instance : Field (GaloisField p n) :=
  inferInstanceAs (Field (SplittingField _))

instance : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) := ⟨37⟩

namespace GaloisField

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

instance : Algebra (ZMod p) (GaloisField p n) := SplittingField.algebra _

instance : IsSplittingField (ZMod p) (GaloisField p n) (X ^ p ^ n - X) :=
  Polynomial.IsSplittingField.splittingField _

instance : CharP (GaloisField p n) p :=
  (Algebra.charP_iff (ZMod p) (GaloisField p n) p).mp (by infer_instance)

instance : FiniteDimensional (ZMod p) (GaloisField p n) := by
  dsimp only [GaloisField]; infer_instance

instance : Finite (GaloisField p n) :=
  Module.finite_of_finite (ZMod p)

theorem finrank {n} (h : n ≠ 0) : Module.finrank (ZMod p) (GaloisField p n) = n := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := h_prime.out.one_lt
  have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) = g_poly.natDegree :=
    card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
      (SplittingField.splits (g_poly : (ZMod p)[X]))
  have nat_degree_eq : g_poly.natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ h hp
  rw [nat_degree_eq] at key
  suffices g_poly.rootSet (GaloisField p n) = Set.univ by
    simp_rw [this, ← Fintype.ofEquiv_card (Equiv.Set.univ _)] at key
    -- Porting note: prevents `card_eq_pow_finrank` from using a wrong instance for `Fintype`
    rw [@card_eq_pow_finrank (ZMod p) _ _ _ _ _ (_), ZMod.card] at key
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  suffices ∀ (x) (hx : x ∈ (⊤ : Subalgebra (ZMod p) (GaloisField p n))),
      x ∈ (X ^ p ^ n - X : (ZMod p)[X]).rootSet (GaloisField p n)
    by simpa
  rw [← SplittingField.adjoin_rootSet]
  simp_rw [Algebra.mem_adjoin_iff]
  intro x hx
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  simp only [g_poly] at aux
  refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hx
    <;> simp_rw [mem_rootSet_of_ne aux]
  · rintro x (⟨r, rfl⟩ | hx)
    · simp only [g_poly, map_sub, map_pow, aeval_X]
      rw [← map_pow, ZMod.pow_card_pow, sub_self]
    · dsimp only [GaloisField] at hx
      rwa [mem_rootSet_of_ne aux] at hx
  · rw [← coeff_zero_eq_aeval_zero']
    simp only [g_poly, coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    exact Nat.not_lt_zero 1 (pow_eq_zero hn.symm ▸ hp)
  · simp [g_poly]
  · simp only [g_poly, aeval_X_pow, aeval_X, map_sub, add_pow_char_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx, hy]
  · intro x _ hx
    simp only [g_poly, sub_eq_zero, aeval_X_pow, aeval_X, map_sub, sub_neg_eq_add] at *
    rw [neg_pow, hx, neg_one_pow_char_pow]
    simp
  · simp only [g_poly, aeval_X_pow, aeval_X, map_sub, mul_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx, hy]

theorem card (h : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card, Module.card_fintype b, ← Module.finrank_eq_card_basis b,
    ZMod.card, finrank p h]

theorem splits_zmod_X_pow_sub_X : Splits (RingHom.id (ZMod p)) (X ^ p - X) := by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, ZMod.card]

/-- A Galois field with exponent 1 is equivalent to `ZMod` -/
def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  let h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  let inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

section Fintype

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

theorem _root_.FiniteField.splits_X_pow_card_sub_X :
    Splits (algebraMap (ZMod p) K) (X ^ Fintype.card K - X) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits

@[deprecated (since := "2024-11-12")]
alias splits_X_pow_card_sub_X := FiniteField.splits_X_pow_card_sub_X

theorem _root_.FiniteField.isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)

@[deprecated (since := "2024-11-12")]
alias isSplittingField_of_card_eq := FiniteField.isSplittingField_of_card_eq

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def algEquivGaloisFieldOfFintype (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Fintype

section Finite

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

theorem _root_.FiniteField.splits_X_pow_nat_card_sub_X [Finite K] :
    Splits (algebraMap (ZMod p) K) (X ^ Nat.card K - X) := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits

theorem _root_.FiniteField.isSplittingField_of_nat_card_eq (h : Nat.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) := by
  haveI : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  haveI : Fintype K := Fintype.ofFinite K
  rw [← h, Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)

instance (priority := 100) {K K' : Type*} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP K p := hp
  haveI : CharP K' p := charP_of_injective_algebraMap' K K' p
  exact IsGalois.of_separable_splitting_field
    (galois_poly_separable p (Fintype.card K')
      (let ⟨n, _, hn⟩ := FiniteField.card K' p
      hn.symm ▸ dvd_pow_self p n.ne_zero))

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Finite

end GaloisField

namespace FiniteField

variable {K : Type*} [Field K] [Fintype K] {K' : Type*} [Field K'] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic -/
def algEquivOfCardEq (p : ℕ) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K' := by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK, hK'] at hKK'
  have hGalK := GaloisField.algEquivGaloisFieldOfFintype p n hK
  have hK'Gal := (GaloisField.algEquivGaloisFieldOfFintype p n' hK').symm
  rw [Nat.pow_right_injective h_prime.out.one_lt hKK'] at *
  exact AlgEquiv.trans hGalK hK'Gal

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic -/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    have h2 := Nat.coprime_pow_primes n n' hp hp' hne
    rw [(Eq.congr hK hK').mp hKK', Nat.coprime_self, pow_eq_one_iff (PNat.ne_zero n')] at h2
    exact Nat.Prime.ne_one hp' h2
  rw [← hpp'] at _char_p'_K'
  haveI := fact_iff.2 hp
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) K' := ZMod.algebra _ _
  exact ↑(algEquivOfCardEq p hKK')

theorem pow_finrank_eq_card [CharP K p] : p ^ Module.finrank (⊥ : Subfield K) K = Nat.card K := by
  obtain ⟨⟨n, npos⟩, hp, hn⟩ := FiniteField.card K p
  have _ := finite_bot K p
  have _ := Fintype.ofFinite (⊥ : Subfield K)
  have := (card_eq_pow_finrank (K := (⊥ : Subfield K)) (V := K)).symm
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_bot K p] at this

theorem finrank_ne [CharP K p] : Module.finrank (⊥ : Subfield K) K ≠ 0 := by
  by_contra h
  have : p ^ Module.finrank (⊥ : Subfield K) K = Fintype.card K := by
    rw [pow_finrank_eq_card, Nat.card_eq_fintype_card]
  rw [h, pow_zero, ← Nat.card_eq_fintype_card] at this
  apply (Nat.ne_of_lt' Finite.one_lt_card) this.symm

/-- The frobenius map as an equivalence on a finite field. -/
def frobeniusEquiv (K) [Field K] [Fintype K] (p) [Fact p.Prime] [CharP K p] : K ≃+* K where
  toFun x := frobenius K p x
  invFun x := (frobenius K p ^ (Module.finrank (⊥ : Subfield K) K - 1)) x
  left_inv := by
    simp only [Function.LeftInverse, frobenius, powMonoidHom, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, RingHom.coe_pow, pow_iterate]
    intro x
    rw [← npow_mul', pow_sub_one_mul (finrank_ne p) p, pow_finrank_eq_card,
      Nat.card_eq_fintype_card, pow_card]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, frobenius, powMonoidHom,
      RingHom.coe_pow, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, pow_iterate]
    intro x
    rw [← npow_mul, pow_sub_one_mul (finrank_ne p) p, pow_finrank_eq_card, Nat.card_eq_fintype_card,
      pow_card]
  map_mul' x y := by simp
  map_add' x y := by simp

-- TODO : frobeniusEquiv as an automorphism of any algebraic extension of `⊥`, or perfect field.

/-- This needs to be generalized to arbitrary characteristic -/
@[simps!]
def RingEquivToAlgEquiv [CharP K p] : (K ≃+* K) ≃* (K ≃ₐ[(⊥ : Subfield K)] K) where
  toFun g := {
    toFun := fun x ↦ g x
    invFun := fun x ↦ g.symm x
    left_inv x := by simp
    right_inv x := by simp
    map_mul' x y := by simp
    map_add' x y := by simp
    commutes' x := by
      have hx := x.2
      obtain ⟨n, hn⟩ := (mem_bot (x := x.1) p K).mp x.2
      have : (algebraMap (⊥ : Subfield K) K) x = x.1 := rfl
      rw [this, ← hn]
      exact map_intCast g n
  }
  invFun g := g
  left_inv g := by ext; simp
  right_inv g := by ext; simp
  map_mul' g h := by
    ext x
    simp only [AlgEquiv.coe_mk, Equiv.coe_fn_mk, AlgEquiv.mul_apply]
    exact rfl

/-- The action of the automorphism group of `K` on `K` -/
local instance : MulSemiringAction (K ≃+* K) K where
  smul g x := g x
  one_smul x := rfl
  mul_smul x y z := rfl
  smul_zero g := by simp [HSMul.hSMul]
  smul_add g x y := by simp [HSMul.hSMul]
  smul_one g := by simp [HSMul.hSMul]
  smul_mul g x y := by simp [HSMul.hSMul]

theorem fixedBy_frobenius [CharP K p] : FixedBy.subfield K (frobeniusEquiv (K := K) p) = ⊥ := by
  refine bot_unique ?_
  rw [SetLike.le_def]
  intro _ h
  exact (mem_bot_iff p).mpr h

theorem fixedPoints_eq_bot [CharP K p] :
    FixedPoints.subfield (K ≃+* K) K  = (⊥ : Subfield K) := by
  rw [eq_bot_iff, SetLike.le_def]
  intro x hx
  have hx : ∀ (g : K ≃+* K), g x = x := hx
  specialize hx (frobeniusEquiv (K := K) p)
  have hx : x ^ p = x := hx
  exact (mem_bot_iff p (F := K)).mpr hx

omit [Fact (Nat.Prime p)] [Fintype K] in
theorem mem_bot_iff_mem_bot (x : K) :
    x ∈ (⊥ : IntermediateField (⊥ : Subfield K) K) ↔ x ∈ (⊥ : Subfield K) := by
  rw [IntermediateField.mem_bot, Set.mem_range]
  refine ⟨fun h ↦ ?_, fun h ↦ Exists.intro ⟨x, h⟩ rfl⟩
  obtain ⟨⟨a, hha⟩, ha⟩ := h
  have : a = x := ha
  rwa [this] at hha
--#find_home! mem_bot_iff_mem_bot --[Mathlib.FieldTheory.IntermediateField.Adjoin.Defs]

theorem fixedField_eq_bot [CharP K p] :
    IntermediateField.fixedField (Subgroup.closure {(RingEquivToAlgEquiv p) (frobeniusEquiv K p)}) =
      (⊥ : IntermediateField (⊥ : Subfield K) K) := by
  ext x
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    specialize h ((RingEquivToAlgEquiv p) (frobeniusEquiv K p))
    have h : x ^ p = x := by simpa using h
    rwa [← mem_bot_iff, ← mem_bot_iff_mem_bot] at h
  · intro h f hf
    have := fixedPoints_eq_bot p (K := K)
    rw [Subfield.ext_iff] at this
    rw [mem_bot_iff_mem_bot, ← this] at h
    exact h ((RingEquivToAlgEquiv p).symm f)

theorem closure_frobenius_intermediate [CharP K p] :
    Subgroup.closure {RingEquivToAlgEquiv p (frobeniusEquiv p (K := K))} =
      (⊤ : Subgroup (K ≃ₐ[(⊥ : Subfield K)] K)) := by
  have h := IntermediateField.fixingSubgroup_fixedField (Subgroup.closure
    ({RingEquivToAlgEquiv p (frobeniusEquiv p (K := K))} : Set (K ≃ₐ[(⊥ : Subfield K)] K)))
  have := fixedField_eq_bot p (K := K)
  rw [this] at h
  rw [← h, Subgroup.eq_top_iff']
  intro g
  have : ∀ x ∈ (⊥ : Subfield K), ((RingEquivToAlgEquiv p).symm g) x = x := by
    intro x hx
    have := fixedPoints_eq_bot p (K := K)
    rw [Subfield.ext_iff] at this
    rw [← this] at hx
    exact hx ((RingEquivToAlgEquiv p).symm g)
  have : ∀ x ∈ (⊥ : Subfield K), g x = x := this
  simp_rw [← mem_bot_iff_mem_bot] at this
  intro y
  exact this y.1 y.2

theorem aut_cyclic_intermediate [CharP K p] : IsCyclic (K ≃ₐ[(⊥ : Subfield K)] K) := by
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ?_
  use (RingEquivToAlgEquiv p (frobeniusEquiv p (K := K)))
  rw [Subgroup.zpowers_eq_closure]
  exact closure_frobenius_intermediate p

theorem aut_cyclic [CharP K p] : IsCyclic (K ≃+* K) := by
  have := aut_cyclic_intermediate p (K := K)
  refine isCyclic_of_injective (G' := (K ≃ₐ[(⊥ : Subfield K)] K))
    (RingEquivToAlgEquiv p).toMonoidHom ?_
  rw [MulEquiv.coe_toMonoidHom]
  exact MulEquiv.injective (RingEquivToAlgEquiv p)


-- IsGalois.card_aut_eq_finrank : If L/K is Galois, then rank_K L is the order of the group.

/-!
theorem closure_frobenius [CharP K p] :
    Subgroup.closure {frobeniusEquiv p (K := K)} = (⊤ : Subgroup (K ≃+* K)) := by
  have := closure_frobenius_intermediate p (K := K)

  sorry
`Gal K/⊥` is precisely the cyclic group generated by `frobenius K p`, by Galois correspondence.

`FiniteField.frobenius_pow` says that `frobenius K p ^ n = 1` under the assumption
`hcard : q = p ^ n`.  I want to say that `frobenius K p` generates the automorphism group of `K` and
has order exactly `n`.

Then, since subgroups of cyclic groups are classified, we can classify
intermediate fields: If `d∣n`, then `frobenius K p ^ d` has order `n/d`, and the fixed field is
precisely the splitting subfield.



-/

end FiniteField
