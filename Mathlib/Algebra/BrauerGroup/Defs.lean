/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Central.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Category.AlgebraCat.Basic

/-!
# Definition of BrauerGroup over a field K

We introduce the definition of Brauer group of a field K, which is the quotient of the set of
all finite-dimensional central simple algebras over K modulo the Brauer Equivalence where two
central simple algebras `A` and `B` are Brauer Equivalent if there exist `n, m ∈ ℕ+` such
that the `Mₙ(A) ≃ₐ[K] Mₙ(B)`.

# TODOs
1. Prove that the Brauer group is an abelian group where multiplication is defined as tensorproduct.
2. Prove that the Brauer group is a functor from the category of fields to the category of groups.
3. Prove that over a field, being Brauer equivalent is the same as being Morita equivalent.

# References
* [Algebraic Number Theory, *J.W.S Cassels*][cassels1967algebraic]

## Tags
Brauer group, Central simple algebra, Galois Cohomology
-/

universe u v

/-- `CSA` is the set of all finite dimensional central simple algebras over field `K`, for its
  generalisation over a `CommRing` please find `IsAzumaya` in `Mathlib.Algebra.Azumaya.Defs`. -/
structure CSA (K : Type u) [Field K] extends AlgebraCat.{v} K where
  /-- Amy member of `CSA` is central. -/
  [isCentral : Algebra.IsCentral K carrier]
  /-- Any member of `CSA` is simple. -/
  [isSimple : IsSimpleRing carrier]
  /-- Any member of `CSA` is finite-dimensional. -/
  [fin_dim : FiniteDimensional K carrier]

variable {K : Type u} [Field K]

instance : CoeSort (CSA.{u, v} K) (Type v) := ⟨(·.carrier)⟩

instance (A : CSA K): Ring A := A.toAlgebraCat.isRing

instance (A : CSA K): Algebra K A := A.toAlgebraCat.isAlgebra

attribute [instance] CSA.isCentral CSA.isSimple CSA.fin_dim

/-- Two finite dimensional central simple algebras `A` and `B` are Brauer Equivalent
  if there exist `n, m ∈ ℕ+` such that the `Mₙ(A) ≃ₐ[K] Mₙ(B)`. -/
structure BrauerEquivalence (A B : CSA K) where
  /-- dimension of the matrices -/
  (n m : ℕ)
  [hn: NeZero n]
  [hm : NeZero m]
  /-- The isomorphism between the `Mₙ(A)` and `Mₘ(B)`. -/
  iso : Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B

attribute [instance] BrauerEquivalence.hn BrauerEquivalence.hm

/-- `BrauerEquivalence` ad `Prop`. -/
abbrev IsBrauerEquivalent (A B : CSA K) : Prop := Nonempty (BrauerEquivalence A B)

namespace IsBrauerEquivalent

@[refl]
lemma refl (A : CSA K) : IsBrauerEquivalent A A := ⟨⟨1, 1, AlgEquiv.refl⟩⟩

@[symm]
lemma symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := by
  obtain ⟨n, m, iso⟩ := h
  exact ⟨⟨m, n, iso.symm⟩⟩

open Matrix in
@[trans]
lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, iso1⟩ := hAB
  obtain ⟨p, q, iso2⟩ := hBC
  exact ⟨⟨p * n, m * q,
    reindexAlgEquiv _ _ finProdFinEquiv |>.symm.trans <| Matrix.compAlgEquiv _ _ _ _|>.symm.trans <|
    iso1.mapMatrix (m := Fin p)|>.trans <| Matrix.compAlgEquiv _ _ _ _|>.trans <|
    Matrix.reindexAlgEquiv K B (.prodComm (Fin p) (Fin m))|>.trans <|
    Matrix.compAlgEquiv _ _ _ _|>.symm.trans <| iso2.mapMatrix.trans <|
    Matrix.compAlgEquiv _ _ _ _|>.trans <| reindexAlgEquiv _ _ finProdFinEquiv⟩⟩

lemma is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

variable (K)

/-- `CSA` equipped with Brauer Equivalence is indeed a setoid. -/
def Brauer.CSA_Setoid: Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.is_eqv

/-- `BrauerGroup` is the set of all finite-dimensional central simple algebras quotient
  by Brauer Equivalence. -/
abbrev BrauerGroup := Quotient (Brauer.CSA_Setoid K)
