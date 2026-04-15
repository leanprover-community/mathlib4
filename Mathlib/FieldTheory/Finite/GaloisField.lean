/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity

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
- `card_algHom_of_finrank_dvd`: if `[K:F] ∣ [L:F]` then `#(K →ₐ[F] L) = [K:F]`
- `nonempty_algHom_iff_finrank_dvd`: `(K →ₐ[F] L)` is nonempty iff `[K:F] ∣ [L:F]`. This and the
  above result helps to classify the category of finite fields.

-/

noncomputable section


open Polynomial Finset

open scoped Polynomial

public instance FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  splits' := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow,
      map_X, h, FiniteField.roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_rootSet' := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [rootSet, aroots, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_toFinset, coe_univ, Algebra.adjoin_univ]

public theorem galois_poly_separable {K : Type*} [CommRing K] (p q : ℕ) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub, derivative_X_pow, derivative_X, C_eq_natCast, h]
  ring

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
@[expose] public def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])

namespace GaloisField

@[implicit_reducible]
def instFieldAux (p : ℕ) [Fact p.Prime] (n : ℕ) : Field (GaloisField p n) :=
  inferInstanceAs (Field (delta% GaloisField p n))

variable {p : ℕ} [h_prime : Fact p.Prime] {n : ℕ}

/-- The encapsulated addition for `GaloisField p n`. Use `x + y` instead. -/
public protected def add : (x y : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).add

/-- The encapsulated zero for `GaloisField p n`. Use `0` instead. -/
public protected def zero : GaloisField p n :=
  (instFieldAux p n).zero

/-- The encapsulated natural scalar multiplication for `GaloisField p n`. Use `m • x` instead. -/
public protected def nsmul : (m : ℕ) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).nsmul

/-- The encapsulated multiplication for `GaloisField p n`. Use `x * y` instead. -/
public protected def mul : (x y : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).mul

/-- The encapsulated one for `GaloisField p n`. Use `1` instead. -/
public protected def one : GaloisField p n :=
  (instFieldAux p n).one

/-- The encapsulated cast from natural for `GaloisField p n`. Use `↑m` instead. -/
public protected def natCast : (m : ℕ) → GaloisField p n :=
  (instFieldAux p n).natCast

/-- The encapsulated natural power for `GaloisField p n`. Use `x ^ m` instead. -/
public protected def npow : (m : ℕ) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).npow

/-- The encapsulated negation for `GaloisField p n`. Use `-x` instead. -/
public protected def neg : (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).neg

/-- The encapsulated subtraction for `GaloisField p n`. Use `x - y` instead. -/
public protected def sub : (x y : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).sub

/-- The encapsulated integer scalar multiplication for `GaloisField p n`. Use `m • x` instead. -/
public protected def zsmul : (m : ℤ) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).zsmul

/-- The encapsulated cast from integer for `GaloisField p n`. Use `↑m` instead. -/
public protected def intCast : (m : ℤ) → GaloisField p n :=
  (instFieldAux p n).intCast

/-- The encapsulated inverse for `GaloisField p n`. Use `x⁻¹` instead. -/
public protected def inv : (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).inv

/-- The encapsulated division for `GaloisField p n`. Use `x / y` instead. -/
public protected def div : (x y : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).div

/-- The encapsulated integer power for `GaloisField p n`. Use `x ^ m` instead. -/
public protected def zpow : (m : ℤ) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).zpow

/-- The encapsulated cast from nonnegative rational for `GaloisField p n`. Use `↑q` instead. -/
public protected def nnratCast : (q : ℚ≥0) → GaloisField p n :=
  (instFieldAux p n).nnratCast

/-- The encapsulated cast from rational for `GaloisField p n`. Use `↑q` instead. -/
public protected def ratCast : (q : ℚ) → GaloisField p n :=
  (instFieldAux p n).ratCast

/-- The encapsulated nonnegative rational scalar multiplication for `GaloisField p n`.
Use `q • x` instead. -/
public protected def nnqsmul : (q : ℚ≥0) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).nnqsmul

/-- The encapsulated rational scalar multiplication for `GaloisField p n`. Use `q • x` instead. -/
public protected def qsmul : (q : ℚ) → (x : GaloisField p n) → GaloisField p n :=
  (instFieldAux p n).qsmul

public instance (p : ℕ) [Fact p.Prime] (n : ℕ) : Field (GaloisField p n) where
  add := GaloisField.add
  add_assoc := by exact (instFieldAux p n).add_assoc
  zero := GaloisField.zero
  zero_add := by exact (instFieldAux p n).zero_add
  add_zero := by exact (instFieldAux p n).add_zero
  nsmul := GaloisField.nsmul
  nsmul_zero := by exact (instFieldAux p n).nsmul_zero
  nsmul_succ := by exact (instFieldAux p n).nsmul_succ
  add_comm := by exact (instFieldAux p n).add_comm
  mul := GaloisField.mul
  left_distrib := by exact (instFieldAux p n).left_distrib
  right_distrib := by exact (instFieldAux p n).right_distrib
  zero_mul := by exact (instFieldAux p n).zero_mul
  mul_zero := by exact (instFieldAux p n).mul_zero
  mul_assoc := by exact (instFieldAux p n).mul_assoc
  one := GaloisField.one
  one_mul := by exact (instFieldAux p n).one_mul
  mul_one := by exact (instFieldAux p n).mul_one
  natCast := GaloisField.natCast
  natCast_zero := by exact (instFieldAux p n).natCast_zero
  natCast_succ := by exact (instFieldAux p n).natCast_succ
  npow := GaloisField.npow
  npow_zero := by exact (instFieldAux p n).npow_zero
  npow_succ := by exact (instFieldAux p n).npow_succ
  neg := GaloisField.neg
  sub := GaloisField.sub
  sub_eq_add_neg := by exact (instFieldAux p n).sub_eq_add_neg
  zsmul := GaloisField.zsmul
  zsmul_zero' := by exact (instFieldAux p n).zsmul_zero'
  zsmul_succ' := by exact (instFieldAux p n).zsmul_succ'
  zsmul_neg' := by exact (instFieldAux p n).zsmul_neg'
  neg_add_cancel := by exact (instFieldAux p n).neg_add_cancel
  intCast := GaloisField.intCast
  intCast_ofNat := by exact (instFieldAux p n).intCast_ofNat
  intCast_negSucc := by exact (instFieldAux p n).intCast_negSucc
  mul_comm := by exact (instFieldAux p n).mul_comm
  inv := GaloisField.inv
  div := GaloisField.div
  div_eq_mul_inv := by exact (instFieldAux p n).div_eq_mul_inv
  zpow := GaloisField.zpow
  zpow_zero' := by exact (instFieldAux p n).zpow_zero'
  zpow_succ' := by exact (instFieldAux p n).zpow_succ'
  zpow_neg' := by exact (instFieldAux p n).zpow_neg'
  exists_pair_ne := by exact (instFieldAux p n).exists_pair_ne
  nnratCast := GaloisField.nnratCast
  ratCast := GaloisField.ratCast
  mul_inv_cancel := by exact (instFieldAux p n).mul_inv_cancel
  inv_zero := by exact (instFieldAux p n).inv_zero
  nnratCast_def := by exact (instFieldAux p n).nnratCast_def
  nnqsmul := GaloisField.nnqsmul
  nnqsmul_def := by exact (instFieldAux p n).nnqsmul_def
  ratCast_def := by exact (instFieldAux p n).ratCast_def
  qsmul := GaloisField.qsmul
  qsmul_def := by exact (instFieldAux p n).qsmul_def

@[implicit_reducible]
def instAlgebraZModAux (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ) :
    Algebra (ZMod p) (GaloisField p n) :=
  inferInstanceAs (Algebra (ZMod p) (delta% GaloisField p n))

/-- The encapsulated integers modulo `p` scalar multiplication for `GaloisField p n`.
Use `m • x` instead. -/
public protected def zmodsmul : (m : ZMod p) → (x : GaloisField p n) → GaloisField p n :=
  (instAlgebraZModAux p n).smul

/-- The encapsulated cast from integers modulo `p` for `GaloisField p n`. Use `↑m` instead. -/
public protected def zmodCast : (m : ZMod p) → GaloisField p n :=
  ⇑(instAlgebraZModAux p n).algebraMap

public instance (p : ℕ) [Fact p.Prime] (n : ℕ) : Algebra (ZMod p) (GaloisField p n) where
  smul := GaloisField.zmodsmul
  algebraMap.toFun := GaloisField.zmodCast
  algebraMap.map_one' := by exact (instAlgebraZModAux p n).algebraMap.map_one'
  algebraMap.map_mul' := by exact (instAlgebraZModAux p n).algebraMap.map_mul'
  algebraMap.map_zero' := by exact (instAlgebraZModAux p n).algebraMap.map_zero'
  algebraMap.map_add' := by exact (instAlgebraZModAux p n).algebraMap.map_add'
  commutes' := by exact (instAlgebraZModAux p n).commutes'
  smul_def' := by exact (instAlgebraZModAux p n).smul_def'

variable (p : ℕ) [h_prime : Fact p.Prime] (n : ℕ)

public instance : Inhabited (GaloisField p n) where
  default := 0

public instance : CharP (GaloisField p n) p :=
  inferInstanceAs (CharP (delta% GaloisField p n) p)

public instance : Finite (GaloisField p n) :=
  inferInstanceAs (Finite (delta% GaloisField p n))

public instance : FiniteDimensional (ZMod p) (GaloisField p n) :=
  inferInstanceAs (FiniteDimensional (ZMod p) (delta% GaloisField p n))

public instance : IsSplittingField (ZMod p) (GaloisField p n) (X ^ p ^ n - X) :=
  inferInstanceAs (IsSplittingField (ZMod p) (delta% GaloisField p n) (X ^ p ^ n - X))

public theorem finrank {n} (h : n ≠ 0) : Module.finrank (ZMod p) (GaloisField p n) = n := by
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
  suffices ∀ (x) (hx : x ∈ (⊤ : Subalgebra (ZMod p) (X ^ p ^ n - X : (ZMod p)[X]).SplittingField)),
      x ∈ (X ^ p ^ n - X : (ZMod p)[X]).rootSet (X ^ p ^ n - X : (ZMod p)[X]).SplittingField by
    simpa
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
    · rwa [mem_rootSet_of_ne aux] at hx
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

public theorem card (h : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card, Module.card_fintype b, ← Module.finrank_eq_card_basis b,
    ZMod.card, finrank p h]

public theorem splits_zmod_X_pow_sub_X : Splits (X ^ p - X : (ZMod p)[X]) := by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, ZMod.card]

/-- A Galois field with exponent 1 is equivalent to `ZMod` -/
public def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

section Fintype

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

public theorem _root_.FiniteField.splits_X_pow_card_sub_X :
    Splits (map (algebraMap (ZMod p) K) (X ^ Fintype.card K - X)) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits

public theorem _root_.FiniteField.isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
public def algEquivGaloisFieldOfFintype (h : Fintype.card K = p ^ n) :
    K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Fintype

section Finite

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

public theorem _root_.FiniteField.splits_X_pow_nat_card_sub_X [Finite K] :
    Splits (map (algebraMap (ZMod p) K) (X ^ Nat.card K - X)) := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits

public theorem _root_.FiniteField.isSplittingField_of_nat_card_eq (h : Nat.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) := by
  haveI : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  haveI : Fintype K := Fintype.ofFinite K
  rw [← h, Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)

public theorem _root_.Polynomial.splits_X_pow_nat_card_sub_X :
    Splits (X ^ (Nat.card K) - X : K[X]) := by
  cases fintypeOrInfinite K
  · have := (IsSplittingField.splits (L := K) (X ^ (Fintype.card K) - X : K[X]))
    simpa [Algebra.algebraMap_self, map_sub, map_pow, map_X] using this
  · rw [← Polynomial.splits_neg_iff]
    simpa [Nat.card_eq_zero_of_infinite, pow_zero, neg_sub] using Splits.X_sub_C (1 : K)

public instance (priority := 100) {K K' : Type*} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP K p := hp
  haveI : CharP K' p := charP_of_injective_algebraMap' K p
  exact IsGalois.of_separable_splitting_field
    (galois_poly_separable p (Fintype.card K')
      (let ⟨n, _, hn⟩ := FiniteField.card K' p
      hn.symm ▸ dvd_pow_self p n.ne_zero))

/-- Any finite field is (possibly noncanonically) isomorphic to some Galois field. -/
public def algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Finite

end GaloisField

namespace FiniteField

variable {K K' : Type*} [Field K] [Field K']

section norm

variable [Algebra K K'] [Finite K']

public theorem algebraMap_norm_eq_pow {x : K'} :
    algebraMap K K' (Algebra.norm K x) = x ^ ((Nat.card K' - 1) / (Nat.card K - 1)) := by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range, Nat.geomSum_eq Fintype.one_lt_card, ← Module.card_eq_pow_finrank]

variable (K K')

public theorem unitsMap_norm_surjective :
    Function.Surjective (Units.map <| Algebra.norm K (S := K')) :=
  have := Finite.of_injective_finite_range (algebraMap K K').injective
  MonoidHom.surjective_of_card_ker_le_div _ <| by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert IsCyclic.card_pow_eq_one_le (α := K'ˣ) <| Nat.div_pos
      (Nat.sub_le_sub_right (Nat.card_le_card_of_injective _ (algebraMap K K').injective) _) <|
      Nat.sub_pos_of_lt Finite.one_lt_card
    rw [← Set.ncard_coe_finset, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]; congr 1; ext
    simp [Units.ext_iff, ← (algebraMap K K').injective.eq_iff, algebraMap_norm_eq_pow]

public theorem norm_surjective : Function.Surjective (Algebra.norm K (S := K')) := fun k ↦ by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

end norm

variable [Fintype K] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly noncanonically) isomorphic -/
public def algEquivOfCardEq (p : ℕ)
    [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
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
public def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    simpa [← hK, hK', hKK', hp'.ne_one] using Nat.coprime_pow_primes n n' hp hp' hne
  rw [← hpp'] at _char_p'_K'
  haveI := fact_iff.2 hp
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) K' := ZMod.algebra _ _
  exact ↑(algEquivOfCardEq p hKK')

public theorem pow_finrank_eq_natCard (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Nat.card k := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

public theorem pow_finrank_eq_card (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Fintype k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Fintype.card k := by
  rw [pow_finrank_eq_natCard, Fintype.card_eq_nat_card]

section
variable {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L] [Finite L]

public theorem nonempty_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nonempty (K →ₐ[F] L) := by
  have := Finite.of_injective _ (algebraMap F L).injective
  have := Fintype.ofFinite F
  have := Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  have := Module.finite_of_finite F (M := K)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  refine ⟨Polynomial.IsSplittingField.lift _ (X ^ Fintype.card K - X) ?_⟩
  refine (FiniteField.isSplittingField_sub L F).splits.of_dvd ?_ ?_
  · exact map_ne_zero (FiniteField.X_pow_card_sub_X_ne_zero _ Fintype.one_lt_card)
  · rw [Module.card_eq_pow_finrank (K := F), Module.card_eq_pow_finrank (K := F) (V := L)]
    exact (map_dvd_map' _).mpr (dvd_pow_pow_sub_self_of_dvd h)

public theorem natCard_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nat.card (K →ₐ[F] L) = Module.finrank F K := by
  obtain ⟨f⟩ := nonempty_algHom_of_finrank_dvd h
  algebraize [f.toRingHom]
  have := Finite.of_injective _ (algebraMap K L).injective
  rw [Nat.card_congr (Normal.algHomEquivAut F L K), IsGalois.card_aut_eq_finrank]

public theorem card_algHom_of_finrank_dvd [Finite K]
    (h : Module.finrank F K ∣ Module.finrank F L) :
    Fintype.card (K →ₐ[F] L) = Module.finrank F K := by
  rw [Fintype.card_eq_nat_card, natCard_algHom_of_finrank_dvd h]

public theorem nonempty_algHom_iff_finrank_dvd :
    Nonempty (K →ₐ[F] L) ↔ Module.finrank F K ∣ Module.finrank F L := by
  refine ⟨fun ⟨f⟩ ↦ ?_, nonempty_algHom_of_finrank_dvd⟩
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank F K L]
  exact dvd_mul_right _ _

end

end FiniteField
