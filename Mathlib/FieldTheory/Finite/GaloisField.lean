/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity

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

theorem galois_poly_separable {K : Type*} [CommRing K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
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
deriving Inhabited, Field, CharP _ p,
  Algebra (ZMod p),
  Finite, FiniteDimensional (ZMod p),
  IsSplittingField (ZMod p) _ (X ^ p ^ n - X)

namespace GaloisField

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

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
    rw [@Module.card_eq_pow_finrank (K := ZMod p), ZMod.card] at key
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
    · simp only [map_sub, map_pow, aeval_X]
      rw [← map_pow, ZMod.pow_card_pow, sub_self]
    · dsimp only [GaloisField] at hx
      rwa [mem_rootSet_of_ne aux] at hx
  · rw [← coeff_zero_eq_aeval_zero']
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    exact Nat.not_lt_zero 1 (eq_zero_of_pow_eq_zero hn.symm ▸ hp)
  · simp
  · simp only [aeval_X_pow, aeval_X, map_sub, add_pow_char_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx, hy]
  · intro x _ hx
    simp only [g_poly, sub_eq_zero, aeval_X_pow, aeval_X, map_sub, sub_neg_eq_add] at *
    rw [neg_pow, hx, neg_one_pow_char_pow]
    simp
  · simp only [aeval_X_pow, aeval_X, map_sub, mul_pow, sub_eq_zero]
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
  have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

section Fintype

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

theorem _root_.FiniteField.splits_X_pow_card_sub_X :
    Splits (algebraMap (ZMod p) K) (X ^ Fintype.card K - X) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits

theorem _root_.FiniteField.isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
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

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
def algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Finite

end GaloisField

namespace FiniteField

variable {K K' : Type*} [Field K] [Field K']

section norm

variable [Algebra K K'] [Finite K']

theorem algebraMap_norm_eq_pow {x : K'} :
    algebraMap K K' (Algebra.norm K x) = x ^ ((Nat.card K' - 1) / (Nat.card K - 1)) := by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range, Nat.geomSum_eq Fintype.one_lt_card, ← Module.card_eq_pow_finrank]

variable (K K')

theorem unitsMap_norm_surjective : Function.Surjective (Units.map <| Algebra.norm K (S := K')) :=
  have := Finite.of_injective_finite_range (algebraMap K K').injective
  MonoidHom.surjective_of_card_ker_le_div _ <| by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert IsCyclic.card_pow_eq_one_le (α := K'ˣ) <| Nat.div_pos
      (Nat.sub_le_sub_right (Nat.card_le_card_of_injective _ (algebraMap K K').injective) _) <|
      Nat.sub_pos_of_lt Finite.one_lt_card
    rw [← Set.ncard_coe_finset, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]; congr; ext
    simp [Units.ext_iff, ← (algebraMap K K').injective.eq_iff, algebraMap_norm_eq_pow]

theorem norm_surjective : Function.Surjective (Algebra.norm K (S := K')) := fun k ↦ by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

end norm

variable [Fintype K] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) isomorphic -/
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
  Any two finite fields of the same cardinality are (possibly noncanonically) isomorphic -/
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

end FiniteField
