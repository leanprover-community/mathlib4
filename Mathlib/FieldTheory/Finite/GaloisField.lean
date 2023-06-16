/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde

! This file was ported from Lean 3 source module field_theory.finite.galois_field
! leanprover-community/mathlib commit 4b05d3f4f0601dca8abf99c4ec99187682ed0bba
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

## Main Results

- `galois_field.alg_equiv_galois_field`: Any finite field is isomorphic to some Galois field
- `finite_field.alg_equiv_of_card_eq`: Uniqueness of finite fields : algebra isomorphism
- `finite_field.ring_equiv_of_card_eq`: Uniqueness of finite fields : ring isomorphism

-/


noncomputable section

open Polynomial Finset

open scoped Polynomial

instance FiniteField.HasSub.Sub.Polynomial.isSplittingField (K F : Type _) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  Splits := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [← splits_id_iff_splits, splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow,
      map_X, h, FiniteField.roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_rootSet := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [root_set, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_to_finset, coe_univ, Algebra.adjoin_univ]
#align finite_field.has_sub.sub.polynomial.is_splitting_field FiniteField.HasSub.Sub.Polynomial.isSplittingField

theorem galois_poly_separable {K : Type _} [Field K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h 
  rw [derivative_sub, derivative_X_pow, derivative_X, C_eq_nat_cast, h]
  ring
#align galois_poly_separable galois_poly_separable

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
def GaloisField (p : ℕ) [Fact p.Prime] (n : ℕ) :=
  SplittingField (X ^ p ^ n - X : (ZMod p)[X])
deriving Field
#align galois_field GaloisField

instance : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) :=
  ⟨37⟩

namespace GaloisField

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

instance : Algebra (ZMod p) (GaloisField p n) :=
  SplittingField.algebra _

instance : IsSplittingField (ZMod p) (GaloisField p n) (X ^ p ^ n - X) :=
  Polynomial.IsSplittingField.splittingField _

instance : CharP (GaloisField p n) p :=
  (Algebra.charP_iff (ZMod p) (GaloisField p n) p).mp (by infer_instance)

instance : Fintype (GaloisField p n) := by
  dsimp only [GaloisField]
  exact FiniteDimensional.fintypeOfFintype (ZMod p) (GaloisField p n)

theorem finrank {n} (h : n ≠ 0) : FiniteDimensional.finrank (ZMod p) (GaloisField p n) = n := by
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt
  have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) = g_poly.natDegree :=
    card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
      (splitting_field.splits g_poly)
  have nat_degree_eq : g_poly.natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ h hp
  rw [nat_degree_eq] at key 
  suffices g_poly.rootSet (GaloisField p n) = Set.univ by
    simp_rw [this, ← Fintype.ofEquiv_card (Equiv.Set.univ _)] at key 
    rw [@card_eq_pow_finrank (ZMod p), ZMod.card] at key 
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  suffices
    ∀ (x) (hx : x ∈ (⊤ : Subalgebra (ZMod p) (GaloisField p n))),
      x ∈ (X ^ p ^ n - X : (ZMod p)[X]).rootSet (GaloisField p n)
    by simpa
  rw [← splitting_field.adjoin_root_set]
  simp_rw [Algebra.mem_adjoin_iff]
  intro x hx
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  cases p;
  cases hp
  apply Subring.closure_induction hx <;> clear! x <;> simp_rw [mem_root_set_of_ne aux]
  · rintro x (⟨r, rfl⟩ | hx)
    · simp only [aeval_X_pow, aeval_X, AlgHom.map_sub]
      rw [← map_pow, ZMod.pow_card_pow, sub_self]
    · dsimp only [GaloisField] at hx 
      rwa [mem_root_set_of_ne aux] at hx ; infer_instance
  · dsimp only [g_poly]
    rw [← coeff_zero_eq_aeval_zero']
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    exact Nat.not_lt_zero 1 (pow_eq_zero hn.symm ▸ hp)
  · simp
  · simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, add_pow_char_pow, sub_eq_zero]
    intro x y hx hy
    rw [hx, hy]
  · intro x hx
    simp only [sub_eq_zero, aeval_X_pow, aeval_X, AlgHom.map_sub, sub_neg_eq_add] at *
    rw [neg_pow, hx, CharP.neg_one_pow_char_pow]
    simp
  · simp only [aeval_X_pow, aeval_X, AlgHom.map_sub, mul_pow, sub_eq_zero]
    intro x y hx hy
    rw [hx, hy]
#align galois_field.finrank GaloisField.finrank

theorem card (h : n ≠ 0) : Fintype.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b, ZMod.card, finrank p h]
#align galois_field.card GaloisField.card

theorem splits_zMod_x_pow_sub_x : Splits (RingHom.id (ZMod p)) (X ^ p - X) := by
  have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X _
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  cases p;
  cases hp
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, ZMod.card]
#align galois_field.splits_zmod_X_pow_sub_X GaloisField.splits_zMod_x_pow_sub_x

attribute [-instance] ZMod.algebra

/-- A Galois field with exponent 1 is equivalent to `zmod` -/
def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  let h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  let inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm
#align galois_field.equiv_zmod_p GaloisField.equivZmodP

variable {K : Type _} [Field K] [Fintype K] [Algebra (ZMod p) K]

theorem splits_x_pow_card_sub_x : Splits (algebraMap (ZMod p) K) (X ^ Fintype.card K - X) :=
  (FiniteField.HasSub.Sub.Polynomial.isSplittingField K (ZMod p)).Splits
#align galois_field.splits_X_pow_card_sub_X GaloisField.splits_x_pow_card_sub_x

theorem isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.HasSub.Sub.Polynomial.isSplittingField K (ZMod p)
#align galois_field.is_splitting_field_of_card_eq GaloisField.isSplittingField_of_card_eq

instance (priority := 100) {K K' : Type _} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP K p := hp
  haveI : CharP K' p := charP_of_injective_algebraMap' K K' p
  exact
    IsGalois.of_separable_splitting_field
      (galois_poly_separable p (Fintype.card K')
        (let ⟨n, hp, hn⟩ := FiniteField.card K' p
        hn.symm ▸ dvd_pow_self p n.NeZero))

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def algEquivGaloisField (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := is_splitting_field_of_card_eq _ _ h
  is_splitting_field.alg_equiv _ _
#align galois_field.alg_equiv_galois_field GaloisField.algEquivGaloisField

end GaloisField

namespace FiniteField

variable {K : Type _} [Field K] [Fintype K] {K' : Type _} [Field K'] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def algEquivOfCardEq (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K' := by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK, hK'] at hKK' 
  have hGalK := GaloisField.algEquivGaloisField p n hK
  have hK'Gal := (GaloisField.algEquivGaloisField p n' hK').symm
  rw [Nat.pow_right_injective (Fact.out (Nat.Prime p)).one_lt hKK'] at *
  use AlgEquiv.trans hGalK hK'Gal
#align finite_field.alg_equiv_of_card_eq FiniteField.algEquivOfCardEq

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  skip
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    -- := eq_prime_of_eq_prime_pow
    by_contra hne
    have h2 := Nat.coprime_pow_primes n n' hp hp' hne
    rw [(Eq.congr hK hK').mp hKK', Nat.coprime_self, pow_eq_one_iff (PNat.ne_zero n')] at h2 
    exact Nat.Prime.ne_one hp' h2
    all_goals infer_instance
  rw [← hpp'] at *
  haveI := fact_iff.2 hp
  exact alg_equiv_of_card_eq p hKK'
#align finite_field.ring_equiv_of_card_eq FiniteField.ringEquivOfCardEq

end FiniteField

