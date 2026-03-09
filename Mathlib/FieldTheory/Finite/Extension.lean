/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Kevin Buzzard
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Extensions of finite fields

In this file we develop the theory of extensions of finite fields.

If `k` is a finite field (of cardinality `q = p ^ m`), then there is a unique (up to in general
non-unique isomorphism) extension `l` of `k` of any given degree `n > 0`.

This extension is Galois with cyclic Galois group of degree `n`, and the (arithmetic) Frobenius map
`x ↦ x ^ q` is a generator.


## Main definition

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n`
  (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
isomorphic to our chosen `FiniteField.Extension k p n`.

-/

@[expose] public section

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

set_option backward.isDefEq.respectTransparency false in
/-- Given a finite field `k` of characteristic `p`, we have a non-canonically chosen extension
of any given degree `n > 0`. -/
def Extension [CharP k p] : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

set_option backward.isDefEq.respectTransparency false in
theorem finrank_zmod_extension [Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  letI := ZMod.algebra k p
  convert GaloisField.finrank p (n := Module.finrank (ZMod p) k * n) <|
    mul_ne_zero Module.finrank_pos.ne' <| NeZero.ne n using 4
  subsingleton

theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

noncomputable instance : Algebra k (Extension k p n) :=
  letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

set_option backward.isDefEq.respectTransparency false in
instance : Module.Finite k (Extension k p n) :=
  .of_finite

instance [Algebra (ZMod p) k] : IsScalarTower (ZMod p) k (Extension k p n) :=
  -- there is at most one map from `𝔽_p` to any ring
  .of_algebraMap_eq' <| Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  letI := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p, ← pow_finrank_eq_natCard p, finrank_zmod_extension, pow_mul]

set_option backward.isDefEq.respectTransparency false in
theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

instance : IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X) := by
  have := Fintype.ofFinite (Extension k p n)
  convert FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]

example : IsGalois k (Extension k p n) :=
  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

theorem natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n :=
  (IsGalois.card_aut_eq_finrank _ _).trans <| finrank_extension k p n

theorem card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n :=
  Fintype.card_eq_nat_card.trans <| natCard_algEquiv_extension k p n

/-- The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`. -/
noncomputable def Extension.frob :
    Gal(Extension k p n / k) :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  simp [frob, ← Nat.card_eq_fintype_card]

theorem Extension.exists_frob_pow_eq (g : Gal(Extension k p n/k)) :
    ∃ i < n, Extension.frob k p n ^ i = g := by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

/-- Given any field extension of finite fields `l/k` of degree `n`, we have a non-unique
isomorphism between `l` and our chosen `Extension k p n`. -/
noncomputable def algEquivExtension (l : Type*) [Field l] [Algebra k l]
    (h : Module.finrank k l = n) : l ≃ₐ[k] Extension k p n := by
  refine Nonempty.some ?_
  have : Module.Finite k l := Module.finite_of_finrank_pos <| h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h, ← Module.natCard_eq_pow_finrank, ← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

end FiniteField

section Polynomial

variable {K : Type*} [hf : Field K] [Fintype K]


open Polynomial FiniteField

theorem Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X {n : ℕ} [NeZero n] {f : K[X]}
    (hi : Irreducible f) (hd : f.degree ≠ 0) (h : f ∣ (X ^ ((Fintype.card K) ^ n) - X)) :
    f.natDegree ∣ n := by
  obtain ⟨p, _, m, hp, hm⟩ := FiniteField.card' K
  haveI : Fact <| Nat.Prime p := ⟨hp⟩
  haveI : Fact <| Irreducible f := ⟨hi⟩
  -- `F` is the splitting field of `X ^ ((Fintype.card K) ^ n) - X`
  let F := Extension K p n
  haveI : Fintype F := Fintype.ofFinite _
  haveI : Algebra (ZMod p) K := ZMod.algebra K p
  have haux : Nonempty (K →ₐ[ZMod p] F) := nonempty_algHom_extension K p n
  let ψ := (Classical.choice haux).toRingHom
  replace h := Polynomial.map_dvd ψ h
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Fintype.card_eq_nat_card] at h
  rw [← natCard_extension, ← Fintype.card_eq_nat_card] at h
  -- `f` has a root a in `F`. We have extensions `AdjoinRoot f / K` and `F / AdjoinRoot f`.
  choose a ha using exists_root_of_map_dvd_X_pow_card_sub_X hd ψ h
  letI := RingHom.toAlgebra (AdjoinRoot.lift ψ a ha)
  -- Compatible `K`-algebra structure on `F`
  letI : Algebra K F := RingHom.toAlgebra
    (RingHom.comp (algebraMap (AdjoinRoot f) F) (algebraMap K (AdjoinRoot f)))
  letI M1 : Module K F := Algebra.toModule
  letI M2 : Module (AdjoinRoot f) F := Algebra.toModule
  letI M3 : Module K (AdjoinRoot f) := Algebra.toModule
  haveI hfinite : IsScalarTower K (AdjoinRoot f) F := IsScalarTower.of_algebraMap_eq' rfl
  haveI hF1 : Module.Free K (AdjoinRoot f) := Module.Free.of_divisionRing K _
  have hdim1 : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (Irreducible.ne_zero hi)),
      AdjoinRoot.powerBasis_dim (Irreducible.ne_zero hi)]
  have hdim2 : Module.finrank K F = n := (pow_right_inj₀ (Nat.card_pos)
    (Ne.symm (Nat.ne_of_lt Finite.one_lt_card))).1 ((natCard_extension K p n) ▸
    (Module.natCard_eq_pow_finrank (K := K) (V := F))).symm
  rw [← hdim1, ← hdim2]
  use (Module.finrank (AdjoinRoot f) F)
  -- The rank of `AdjoinRoot f` over `K` divides the rank of `F` over `K`.
  refine (@Module.finrank_mul_finrank K (AdjoinRoot f) F _ _ _ M3 M2 M1 hfinite _ _ hF1 ?_ ).symm
  refine Module.Free.of_divisionRing (AdjoinRoot f) _


end Polynomial
