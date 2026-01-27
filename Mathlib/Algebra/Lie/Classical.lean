/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `LieAlgebra.SpecialLinear.sl`
  * `LieAlgebra.Symplectic.sp`
  * `LieAlgebra.Orthogonal.so`
  * `LieAlgebra.Orthogonal.so'`
  * `LieAlgebra.Orthogonal.soIndefiniteEquiv`
  * `LieAlgebra.Orthogonal.typeD`
  * `LieAlgebra.Orthogonal.typeB`
  * `LieAlgebra.Orthogonal.typeDEquivSo'`
  * `LieAlgebra.Orthogonal.typeBEquivSo'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lieEquivMatrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
`2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `typeDEquivSo'`, `soIndefiniteEquiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/

@[expose] public section


universe u₁ u₂

namespace LieAlgebra

open Matrix

open scoped Matrix

variable (n p q l : Type*) (R : Type u₂)
variable [DecidableEq n] [DecidableEq p] [DecidableEq q] [DecidableEq l]
variable [CommRing R]

@[simp]
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }

theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl

section ElementaryBasis

variable {n R} [Fintype n] (i j k : n)

/-- When `i ≠ j`, the single-element matrices are elements of `sl n R`.

Along with some elements produced by `singleSubSingle`, these form a natural basis of `sl n R`. -/
def single (h : i ≠ j) : R →ₗ[R] sl n R :=
  Matrix.singleLinearMap R i j |>.codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h

@[simp]
theorem val_single (h : i ≠ j) (r : R) : (single i j h r).val = Matrix.single i j r :=
  rfl

/-- The matrices with matching positive and negative elements on the diagonal are elements of
`sl n R`. Along with `single`, a subset of these form a basis for `sl n R`. -/
def singleSubSingle : R →ₗ[R] sl n R :=
  LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
    LinearMap.sub_mem_ker_iff.mpr <| by simp

@[simp]
theorem val_singleSubSingle (r : R) :
    (singleSubSingle i j r).val = Matrix.single i i r - Matrix.single j j r :=
  rfl

@[simp]
theorem singleSubSingle_add_singleSubSingle (r : R) :
    singleSubSingle i j r + singleSubSingle j k r = singleSubSingle i k r := by
  ext : 1; simp

@[simp]
theorem singleSubSingle_sub_singleSubSingle (r : R) :
    singleSubSingle i k r - singleSubSingle i j r = singleSubSingle j k r := by
  ext : 1; simp

@[simp]
theorem singleSubSingle_sub_singleSubSingle' (r : R) :
    singleSubSingle i k r - singleSubSingle j k r = singleSubSingle i j r := by
  ext : 1; simp

end ElementaryBasis
section Basis

variable {n} [Fintype n]

/-- Off-diagonal index pairs `(i, j)` with `i ≠ j`. -/
abbrev OffDiag (n : Type*) := { p : n × n // p.1 ≠ p.2 }

variable {R}

/-- The index type for the standard basis of `sl n R` relative to a chosen diagonal index `i₀`:
off-diagonal pairs plus diagonal indices excluding `i₀`. The diagonal entry at `i₀` is determined
by the trace-zero condition. -/
abbrev slBasisIndex (i0 : n) := OffDiag n ⊕ { i : n // i ≠ i0 }

/-- The basis function for `sl n R` relative to `i₀`: off-diagonal indices map to single-entry
matrices, and diagonal indices `i ≠ i₀` map to `E_ii - E_{i₀i₀}`. -/
def slBasisFun (i0 : n) : slBasisIndex (n := n) i0 → sl n R
  | .inl ⟨⟨i, j⟩, hij⟩ => single i j hij 1
  | .inr i => singleSubSingle i.1 i0 1

/-- The linear map from coordinate functions to `sl n R`, given by linear combination
of basis elements. -/
noncomputable def slBasisRepr (i0 : n) : (slBasisIndex (n := n) i0 → R) →ₗ[R] sl n R :=
  Fintype.linearCombination R (slBasisFun (n := n) (R := R) i0)

/-- The coordinate map from `sl n R` to the coordinate function space: extracts the matrix
entry for off-diagonal indices and the diagonal entry for diagonal indices. -/
noncomputable def slBasisCoord (i0 : n) : sl n R →ₗ[R] (slBasisIndex (n := n) i0 → R) where
  toFun A x :=
    match x with
    | Sum.inl ij =>
        let i := ij.1.1
        let j := ij.1.2
        A.val i j
    | Sum.inr i =>
        A.val i.1 i.1
  map_add' A B := by
    classical
    ext x
    cases x with
    | inl ij =>
        rcases ij with ⟨⟨i, j⟩, hij⟩
        simp
    | inr i =>
        rcases i with ⟨i, hi⟩
        simp
  map_smul' r A := by
    classical
    ext x
    cases x with
    | inl ij =>
        rcases ij with ⟨⟨i, j⟩, hij⟩
        simp
    | inr i =>
        rcases i with ⟨i, hi⟩
        simp

/-- The diagonal entry at `i₀` equals the negative sum of all other diagonal entries,
by the trace-zero condition. -/
theorem sl_diag_i0_eq_neg_sum_diag_ne (i0 : n) (A : sl n R) :
    A.val i0 i0 = -∑ i : { i : n // i ≠ i0 }, A.val i.1 i.1 := by
  classical
  have hker : Matrix.traceLinearMap n R R A.val = 0 := (LinearMap.mem_ker).1 A.property
  have htrace : Matrix.trace A.val = 0 := hker
  have hsum : (∑ i : n, A.val i i) = A.val i0 i0 + ∑ i : { i : n // i ≠ i0 }, A.val i.1 i.1 := by
    simpa using (Fintype.sum_eq_add_sum_subtype_ne (fun i : n => A.val i i) i0)
  have h' : A.val i0 i0 + ∑ i : { i : n // i ≠ i0 }, A.val i.1 i.1 = 0 := by
    have : (∑ i : n, A.val i i) = 0 := by
      simp only [Matrix.trace, Matrix.diag] at htrace
      exact htrace
    simpa [hsum] using this
  exact eq_neg_of_add_eq_zero_left h'

theorem slBasisCoord_slBasisRepr (i0 : n) :
    (slBasisCoord (n := n) (R := R) i0).comp (slBasisRepr (n := n) (R := R) i0) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro g
  funext x
  simp only [slBasisCoord, slBasisRepr, slBasisFun, Fintype.linearCombination_apply,
    LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    LinearMap.id_coe, id_eq, Fintype.sum_sum_type]
  cases x with
  | inl ij =>
      rcases ij with ⟨⟨i, j⟩, hij⟩
      let a : OffDiag n := ⟨(i, j), hij⟩
      have hsum_off' :
          (∑ x : OffDiag n, (Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i j) = g (Sum.inl a) := by
        classical
        simpa [a] using
          (Fintype.sum_eq_single
            (f := fun x : OffDiag n => (Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i j)
            (a := a)
            (fun b hb => by
              have : ¬(b.1.1 = i ∧ b.1.2 = j) := by
                intro h
                exact hb (Subtype.ext (Prod.ext h.1 h.2))
              simp [this]))
      have hsum_off :
          ((∑ x : OffDiag n, Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i j) = g (Sum.inl a) := by
        let A : OffDiag n → Matrix n n R :=
          fun x => Matrix.single x.1.1 x.1.2 (g (Sum.inl x))
        have hrow : ((∑ x : OffDiag n, A x) i) = ∑ x : OffDiag n, (A x) i :=
          (Fintype.sum_apply (g := A) (a := i))
        have hrow' : ((∑ x : OffDiag n, A x) i) j = (∑ x : OffDiag n, (A x) i) j :=
          congrArg (fun f : n → R => f j) hrow
        have hcol : (∑ x : OffDiag n, (A x) i) j = ∑ x : OffDiag n, (A x) i j :=
          (Fintype.sum_apply (g := fun x : OffDiag n => (A x) i) (a := j))
        have hsum_off'' : (∑ x : OffDiag n, (A x) i j) = g (Sum.inl a) := by
          simpa [A] using hsum_off'
        calc
          (∑ x : OffDiag n, A x) i j = ((∑ x : OffDiag n, A x) i) j := rfl
          _ = (∑ x : OffDiag n, (A x) i) j := hrow'
          _ = ∑ x : OffDiag n, (A x) i j := hcol
          _ = g (Sum.inl a) := hsum_off''
      have hsum_diag' :
          (∑ x : { k : n // k ≠ i0 },
              g (Sum.inr x) •
                ((Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R)) i j)) = 0 := by
        classical
        refine Fintype.sum_eq_zero (f := fun x : { k : n // k ≠ i0 } =>
          g (Sum.inr x) • ((Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R)) i j)) ?_
        intro x
        have hx : (Matrix.single x.1 x.1 (1 : R) : Matrix n n R) i j = 0 := by
          have : ¬(x.1 = i ∧ x.1 = j) := by
            intro h
            exact hij (h.1.symm.trans h.2)
          simp [this]
        have hi0' : (Matrix.single i0 i0 (1 : R) : Matrix n n R) i j = 0 := by
          have : ¬(i0 = i ∧ i0 = j) := by
            intro h
            exact hij (h.1.symm.trans h.2)
          simp [this]
        simp [hx, hi0']
      have hsum_diag :
          ((∑ x : { k : n // k ≠ i0 },
                g (Sum.inr x) •
                  (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) i j) = 0 := by
        let A : { k : n // k ≠ i0 } → Matrix n n R :=
          fun x => g (Sum.inr x) • (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))
        have hrow : ((∑ x : { k : n // k ≠ i0 }, A x) i) = ∑ x : { k : n // k ≠ i0 }, (A x) i :=
          (Fintype.sum_apply (g := A) (a := i))
        have hrow' : ((∑ x : { k : n // k ≠ i0 }, A x) i) j =
            (∑ x : { k : n // k ≠ i0 }, (A x) i) j :=
          congrArg (fun f : n → R => f j) hrow
        have hcol : (∑ x : { k : n // k ≠ i0 }, (A x) i) j = ∑ x : { k : n // k ≠ i0 }, (A x) i j :=
          (Fintype.sum_apply (g := fun x : { k : n // k ≠ i0 } => (A x) i) (a := j))
        have hsum_diag'' : (∑ x : { k : n // k ≠ i0 }, (A x) i j) = 0 := by
          simpa [A] using hsum_diag'
        calc
          (∑ x : { k : n // k ≠ i0 }, A x) i j = ((∑ x : { k : n // k ≠ i0 }, A x) i) j := rfl
          _ = (∑ x : { k : n // k ≠ i0 }, (A x) i) j := hrow'
          _ = ∑ x : { k : n // k ≠ i0 }, (A x) i j := hcol
          _ = 0 := hsum_diag''
      simp [a, hsum_off, hsum_diag]
  | inr ii =>
      rcases ii with ⟨i, hi⟩
      let a : { k : n // k ≠ i0 } := ⟨i, hi⟩
      have hsum_off' :
          (∑ x : OffDiag n, (Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i i) = 0 := by
        classical
        refine Fintype.sum_eq_zero (f := fun x : OffDiag n =>
          (Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i i) ?_
        intro x
        have : ¬(x.1.1 = i ∧ x.1.2 = i) := by
          intro h
          exact x.2 (h.1.trans h.2.symm)
        simp [this]
      have hsum_off :
          ((∑ x : OffDiag n, Matrix.single x.1.1 x.1.2 (g (Sum.inl x))) i i) = 0 := by
        let A : OffDiag n → Matrix n n R :=
          fun x => Matrix.single x.1.1 x.1.2 (g (Sum.inl x))
        have hrow : ((∑ x : OffDiag n, A x) i) = ∑ x : OffDiag n, (A x) i :=
          (Fintype.sum_apply (g := A) (a := i))
        have hrow' : ((∑ x : OffDiag n, A x) i) i = (∑ x : OffDiag n, (A x) i) i :=
          congrArg (fun f : n → R => f i) hrow
        have hcol : (∑ x : OffDiag n, (A x) i) i = ∑ x : OffDiag n, (A x) i i :=
          (Fintype.sum_apply (g := fun x : OffDiag n => (A x) i) (a := i))
        have hsum_off'' : (∑ x : OffDiag n, (A x) i i) = 0 := by
          simpa [A] using hsum_off'
        calc
          (∑ x : OffDiag n, A x) i i = ((∑ x : OffDiag n, A x) i) i := rfl
          _ = (∑ x : OffDiag n, (A x) i) i := hrow'
          _ = ∑ x : OffDiag n, (A x) i i := hcol
          _ = 0 := hsum_off''
      have hsum_diag' :
          (∑ x : { k : n // k ≠ i0 },
              g (Sum.inr x) • ((Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R)) i i)) =
            g (Sum.inr a) := by
        classical
        have hi0' : (Matrix.single i0 i0 (1 : R) : Matrix n n R) i i = 0 := by
          simp [hi.symm]
        simpa [a, hi0', Matrix.single_apply] using
          (Fintype.sum_eq_single
            (f := fun x : { k : n // k ≠ i0 } =>
                g (Sum.inr x) • ((Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R)) i i))
            (a := a)
            (fun b hb => by
              have hb' : (b.1 : n) ≠ i := by
                intro h
                exact hb (Subtype.ext h)
              have hbii : (Matrix.single b.1 b.1 (1 : R) : Matrix n n R) i i = 0 := by
                by_cases hbi : b.1 = i
                · exfalso
                  exact hb' hbi
                · simp [hbi]
              have hi0'' : (Matrix.single i0 i0 (1 : R) : Matrix n n R) i i = 0 := by
                simp [hi.symm]
              simp [hbii, hi0'']))
      have hsum_diag :
          ((∑ x : { k : n // k ≠ i0 },
                g (Sum.inr x) •
                  (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) i i) =
            g (Sum.inr a) := by
        let A : { k : n // k ≠ i0 } → Matrix n n R :=
          fun x => g (Sum.inr x) • (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))
        have hrow : ((∑ x : { k : n // k ≠ i0 }, A x) i) = ∑ x : { k : n // k ≠ i0 }, (A x) i :=
          (Fintype.sum_apply (g := A) (a := i))
        have hrow' : ((∑ x : { k : n // k ≠ i0 }, A x) i) i =
            (∑ x : { k : n // k ≠ i0 }, (A x) i) i :=
          congrArg (fun f : n → R => f i) hrow
        have hcol : (∑ x : { k : n // k ≠ i0 }, (A x) i) i = ∑ x : { k : n // k ≠ i0 }, (A x) i i :=
          (Fintype.sum_apply (g := fun x : { k : n // k ≠ i0 } => (A x) i) (a := i))
        have hsum_diag'' : (∑ x : { k : n // k ≠ i0 }, (A x) i i) = g (Sum.inr a) := by
          simpa [A] using hsum_diag'
        calc
          (∑ x : { k : n // k ≠ i0 }, A x) i i = ((∑ x : { k : n // k ≠ i0 }, A x) i) i := rfl
          _ = (∑ x : { k : n // k ≠ i0 }, (A x) i) i := hrow'
          _ = ∑ x : { k : n // k ≠ i0 }, (A x) i i := hcol
          _ = g (Sum.inr a) := hsum_diag''
      simp [a, hsum_off, hsum_diag]

theorem slBasisRepr_slBasisCoord (i0 : n) :
    (slBasisRepr (n := n) (R := R) i0).comp (slBasisCoord (n := n) (R := R) i0) = LinearMap.id := by
  classical
  ext A ii jj
  simp only [slBasisRepr, slBasisCoord, slBasisFun, Fintype.linearCombination_apply,
    LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    LinearMap.id_coe, id_eq, Fintype.sum_sum_type]
  by_cases hij : ii = jj
  · subst hij
    by_cases hi0 : ii = i0
    · -- Case: ii = i0 (diagonal at i0)
      have hdiag : A.val ii ii = -∑ k : { k : n // k ≠ i0 }, A.val k.1 k.1 := by
        rw [hi0]; exact sl_diag_i0_eq_neg_sum_diag_ne (n := n) (R := R) i0 A
      -- Off-diagonal sum vanishes, diagonal sum uses trace-zero condition
      classical
      have hsum_off :
          ((∑ x : OffDiag n,
                Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)) ii ii) = 0 := by
        classical
        let f : OffDiag n → Matrix n n R :=
          fun x => Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)
        have hoff : ((∑ x : OffDiag n, f x) ii ii) = 0 := by
          have hrow : ((∑ x : OffDiag n, f x) ii) = ∑ x : OffDiag n, (f x) ii :=
            (Fintype.sum_apply (g := f) (a := ii))
          have hrow' : ((∑ x : OffDiag n, f x) ii) ii = (∑ x : OffDiag n, (f x) ii) ii :=
            congrArg (fun g : n → R => g ii) hrow
          have hcol : (∑ x : OffDiag n, (f x) ii) ii = ∑ x : OffDiag n, (f x) ii ii :=
            (Fintype.sum_apply (g := fun x : OffDiag n => (f x) ii) (a := ii))
          have hsum : (∑ x : OffDiag n, (f x) ii ii) = 0 := by
            refine Fintype.sum_eq_zero (f := fun x : OffDiag n => (f x) ii ii) ?_
            intro x
            have : ¬(x.1.1 = ii ∧ x.1.2 = ii) := by
              intro h
              exact x.2 (h.1.trans h.2.symm)
            simp [f, this]
          calc
            (∑ x : OffDiag n, f x) ii ii = ((∑ x : OffDiag n, f x) ii) ii := rfl
            _ = (∑ x : OffDiag n, (f x) ii) ii := hrow'
            _ = ∑ x : OffDiag n, (f x) ii ii := hcol
            _ = 0 := hsum
        simpa [f] using hoff
      have hsum_diag :
          ((∑ x : { k : n // k ≠ i0 },
                A.val x.1 x.1 •
                  (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) ii ii) =
            A.val ii ii := by
        classical
        have hxi : ∀ x : { k : n // k ≠ i0 }, x.1 ≠ ii := by
          intro x
          simpa [hi0] using x.2
        let f : { k : n // k ≠ i0 } → Matrix n n R :=
          fun x =>
            A.val x.1 x.1 • (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))
        have hcalc : ((∑ x : { k : n // k ≠ i0 }, f x) ii ii) =
            -∑ x : { k : n // k ≠ i0 }, A.val x.1 x.1 := by
          have hrow : ((∑ x : { k : n // k ≠ i0 }, f x) ii) =
              ∑ x : { k : n // k ≠ i0 }, (f x) ii :=
            (Fintype.sum_apply (g := f) (a := ii))
          have hrow' : ((∑ x : { k : n // k ≠ i0 }, f x) ii) ii =
              (∑ x : { k : n // k ≠ i0 }, (f x) ii) ii :=
            congrArg (fun g : n → R => g ii) hrow
          have hcol : (∑ x : { k : n // k ≠ i0 }, (f x) ii) ii =
              ∑ x : { k : n // k ≠ i0 }, (f x) ii ii :=
            (Fintype.sum_apply (g := fun x : { k : n // k ≠ i0 } => (f x) ii) (a := ii))
          have hterm : ∀ x : { k : n // k ≠ i0 }, (f x) ii ii = -A.val x.1 x.1 := by
            intro x
            have hx0 : (x.1 : n) ≠ i0 := x.2
            -- since `ii = i0`, the second singleton contributes `1` on the diagonal,
            -- and the first contributes `0`
            simp [f, Matrix.sub_apply, hi0, hx0]
          have hneg : (∑ x : { k : n // k ≠ i0 }, (-A.val x.1 x.1)) =
              -∑ x : { k : n // k ≠ i0 }, A.val x.1 x.1 := by
            classical
            simp
          calc
            (∑ x : { k : n // k ≠ i0 }, f x) ii ii = ((∑ x : { k : n // k ≠ i0 }, f x) ii) ii := rfl
            _ = (∑ x : { k : n // k ≠ i0 }, (f x) ii) ii := hrow'
            _ = ∑ x : { k : n // k ≠ i0 }, (f x) ii ii := hcol
            _ = ∑ x : { k : n // k ≠ i0 }, (-A.val x.1 x.1) := by
              simp [hterm]
            _ = -∑ x : { k : n // k ≠ i0 }, A.val x.1 x.1 := hneg
        have hcalc' :
            ((∑ x : { k : n // k ≠ i0 },
                  A.val x.1 x.1 •
                    (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) ii ii) =
              -∑ x : { k : n // k ≠ i0 }, A.val x.1 x.1 := by
          simpa [f] using hcalc
        exact hcalc'.trans hdiag.symm
      simp [hsum_off, hsum_diag]
    · -- Case: ii ≠ i0 (diagonal not at i0)
      -- Off-diagonal sum vanishes, diagonal sum picks out ii term
      classical
      have hsum_off :
          ((∑ x : OffDiag n,
                Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)) ii ii) = 0 := by
        classical
        let f : OffDiag n → Matrix n n R :=
          fun x => Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)
        have hoff : ((∑ x : OffDiag n, f x) ii ii) = 0 := by
          have hrow : ((∑ x : OffDiag n, f x) ii) = ∑ x : OffDiag n, (f x) ii :=
            (Fintype.sum_apply (g := f) (a := ii))
          have hrow' : ((∑ x : OffDiag n, f x) ii) ii = (∑ x : OffDiag n, (f x) ii) ii :=
            congrArg (fun g : n → R => g ii) hrow
          have hcol : (∑ x : OffDiag n, (f x) ii) ii = ∑ x : OffDiag n, (f x) ii ii :=
            (Fintype.sum_apply (g := fun x : OffDiag n => (f x) ii) (a := ii))
          have hsum : (∑ x : OffDiag n, (f x) ii ii) = 0 := by
            refine Fintype.sum_eq_zero (f := fun x : OffDiag n => (f x) ii ii) ?_
            intro x
            have : ¬(x.1.1 = ii ∧ x.1.2 = ii) := by
              intro h
              exact x.2 (h.1.trans h.2.symm)
            simp [f, this]
          calc
            (∑ x : OffDiag n, f x) ii ii = ((∑ x : OffDiag n, f x) ii) ii := rfl
            _ = (∑ x : OffDiag n, (f x) ii) ii := hrow'
            _ = ∑ x : OffDiag n, (f x) ii ii := hcol
            _ = 0 := hsum
        simpa [f] using hoff
      have hsum_diag :
          ((∑ x : { k : n // k ≠ i0 },
                A.val x.1 x.1 •
                  (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) ii ii) =
            A.val ii ii := by
        classical
        let a : { k : n // k ≠ i0 } := ⟨ii, hi0⟩
        let f : { k : n // k ≠ i0 } → Matrix n n R :=
          fun x =>
            A.val x.1 x.1 • (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))
        have hi0' : (Matrix.single i0 i0 (1 : R) : Matrix n n R) ii ii = 0 := by
          have hi0'' : i0 ≠ ii := Ne.symm hi0
          simp [hi0'']
        have hrow : ((∑ x : { k : n // k ≠ i0 }, f x) ii) =
            ∑ x : { k : n // k ≠ i0 }, (f x) ii :=
          (Fintype.sum_apply (g := f) (a := ii))
        have hrow' : ((∑ x : { k : n // k ≠ i0 }, f x) ii) ii =
            (∑ x : { k : n // k ≠ i0 }, (f x) ii) ii :=
          congrArg (fun g : n → R => g ii) hrow
        have hcol : (∑ x : { k : n // k ≠ i0 }, (f x) ii) ii =
            ∑ x : { k : n // k ≠ i0 }, (f x) ii ii :=
          (Fintype.sum_apply (g := fun x : { k : n // k ≠ i0 } => (f x) ii) (a := ii))
        have hsum : (∑ x : { k : n // k ≠ i0 }, (f x) ii ii) = A.val ii ii := by
          classical
          have hsum' : (∑ x : { k : n // k ≠ i0 }, (f x) ii ii) = (f a) ii ii := by
            simpa [a] using
              (Fintype.sum_eq_single
                (f := fun x : { k : n // k ≠ i0 } => (f x) ii ii)
                (a := a)
                (fun b hb => by
                  have hb' : (b.1 : n) ≠ ii := by
                    intro h
                    exact hb (Subtype.ext h)
                  have hbii : (Matrix.single b.1 b.1 (1 : R) : Matrix n n R) ii ii = 0 := by
                    simp [hb']
                  simp [f, Matrix.sub_apply, hbii, hi0']))
          -- compute the remaining term
          have hmain : (f a) ii ii = A.val ii ii := by
            -- `Matrix.single ii ii` contributes `1`, and the `i0` singleton is `0` since `ii ≠ i0`
            have hi0'' : i0 ≠ ii := Ne.symm hi0
            simp [f, a, Matrix.sub_apply, hi0'']
          exact hsum'.trans hmain
        calc
          ((∑ x : { k : n // k ≠ i0 }, f x) ii ii) =
              ((∑ x : { k : n // k ≠ i0 }, (f x) ii) ii) := by
            simpa using congrArg (fun g : n → R => g ii) hrow
          _ = ∑ x : { k : n // k ≠ i0 }, (f x) ii ii := hcol
          _ = A.val ii ii := hsum
      simp [hsum_off, hsum_diag]
  · -- Case: ii ≠ jj (off-diagonal)
    -- Off-diagonal sum picks out (ii,jj) term, diagonal sum vanishes
    classical
    let a : OffDiag n := ⟨(ii, jj), hij⟩
    have hsum_off :
        ((∑ x : OffDiag n,
              Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)) ii jj) = A.val ii jj := by
      classical
      let f : OffDiag n → Matrix n n R :=
        fun x => Matrix.single x.1.1 x.1.2 (A.val x.1.1 x.1.2)
      have hoff : ((∑ x : OffDiag n, f x) ii jj) = A.val ii jj := by
        have hrow : ((∑ x : OffDiag n, f x) ii) = ∑ x : OffDiag n, (f x) ii :=
          (Fintype.sum_apply (g := f) (a := ii))
        have hrow' : ((∑ x : OffDiag n, f x) ii) jj = (∑ x : OffDiag n, (f x) ii) jj :=
          congrArg (fun g : n → R => g jj) hrow
        have hcol : (∑ x : OffDiag n, (f x) ii) jj = ∑ x : OffDiag n, (f x) ii jj :=
          (Fintype.sum_apply (g := fun x : OffDiag n => (f x) ii) (a := jj))
        have hsum : (∑ x : OffDiag n, (f x) ii jj) = A.val ii jj := by
          simpa [a, f] using
            (Fintype.sum_eq_single
              (f := fun x : OffDiag n => (f x) ii jj)
              (a := a)
              (fun b hb => by
                have : ¬(b.1.1 = ii ∧ b.1.2 = jj) := by
                  intro h
                  exact hb (Subtype.ext (Prod.ext h.1 h.2))
                simp [f, this]))
        calc
          (∑ x : OffDiag n, f x) ii jj = ((∑ x : OffDiag n, f x) ii) jj := rfl
          _ = (∑ x : OffDiag n, (f x) ii) jj := hrow'
          _ = ∑ x : OffDiag n, (f x) ii jj := hcol
          _ = A.val ii jj := hsum
      simpa [f] using hoff
    have hsum_diag :
        ((∑ x : { k : n // k ≠ i0 },
              A.val x.1 x.1 •
                (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))) ii jj) = 0 := by
      classical
      let f : { k : n // k ≠ i0 } → Matrix n n R :=
        fun x =>
          A.val x.1 x.1 • (Matrix.single x.1 x.1 (1 : R) - Matrix.single i0 i0 (1 : R))
      have hrow : ((∑ x : { k : n // k ≠ i0 }, f x) ii) =
          ∑ x : { k : n // k ≠ i0 }, (f x) ii :=
        (Fintype.sum_apply (g := f) (a := ii))
      have hrow' : ((∑ x : { k : n // k ≠ i0 }, f x) ii) jj =
          (∑ x : { k : n // k ≠ i0 }, (f x) ii) jj :=
        congrArg (fun g : n → R => g jj) hrow
      have hcol : (∑ x : { k : n // k ≠ i0 }, (f x) ii) jj =
          ∑ x : { k : n // k ≠ i0 }, (f x) ii jj :=
        (Fintype.sum_apply (g := fun x : { k : n // k ≠ i0 } => (f x) ii) (a := jj))
      have hsum : (∑ x : { k : n // k ≠ i0 }, (f x) ii jj) = 0 := by
        refine Fintype.sum_eq_zero (f := fun x : { k : n // k ≠ i0 } => (f x) ii jj) ?_
        intro x
        have hx : (Matrix.single x.1 x.1 (1 : R) : Matrix n n R) ii jj = 0 := by
          have : ¬(x.1 = ii ∧ x.1 = jj) := by
            intro h
            exact hij (h.1.symm.trans h.2)
          simp [this]
        have hi0' : (Matrix.single i0 i0 (1 : R) : Matrix n n R) ii jj = 0 := by
          have : ¬(i0 = ii ∧ i0 = jj) := by
            intro h
            exact hij (h.1.symm.trans h.2)
          simp [this]
        simp [f, Matrix.sub_apply, hx, hi0']
      calc
        (∑ x : { k : n // k ≠ i0 }, f x) ii jj = ((∑ x : { k : n // k ≠ i0 }, f x) ii) jj := rfl
        _ = (∑ x : { k : n // k ≠ i0 }, (f x) ii) jj := hrow'
        _ = ∑ x : { k : n // k ≠ i0 }, (f x) ii jj := hcol
        _ = 0 := hsum
    simp [hsum_off, hsum_diag]


/-- The linear equivalence between `sl n R` and the coordinate function space
for the `i₀`-based basis. -/
noncomputable def slBasisEquiv (i0 : n) : sl n R ≃ₗ[R] (slBasisIndex (n := n) i0 → R) :=
  LinearEquiv.ofLinear
    (slBasisCoord (n := n) (R := R) i0)
    (slBasisRepr (n := n) (R := R) i0)
    (slBasisCoord_slBasisRepr (n := n) (R := R) i0)
    (slBasisRepr_slBasisCoord (n := n) (R := R) i0)

/-- The standard basis of `sl n R` relative to a chosen diagonal index `i₀`. -/
noncomputable def slBasis (i0 : n) : Module.Basis (slBasisIndex (n := n) i0) R (sl n R) :=
  Module.Basis.ofEquivFun (slBasisEquiv (n := n) (R := R) i0)

end Basis

theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [A, B, Matrix.single, Matrix.mul_apply, hij.symm] using congr_fun (congr_fun c' i) i

end SpecialLinear

namespace Symplectic

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [Fintype l] : LieSubalgebra R (Matrix (l ⊕ l) (l ⊕ l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)

end Symplectic

namespace Orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A := by
  rw [so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefiniteDiagonal : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p ⊕ q) (p ⊕ q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i

variable [Fintype p] [Fintype q]

theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, h, one_apply]
  · -- x : p, y : q
    simp [Pso]
  · -- x : q, y : p
    simp [Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, h, hi, one_apply]

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)

theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
noncomputable def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (p ⊕ q) (p ⊕ q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (p ⊕ q) (p ⊕ q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  grind [skewAdjointMatricesLieSubalgebraEquiv_apply]

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
def S :=
  indefiniteDiagonal l l R

theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl

theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, PD, s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp [two_smul]

theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp

instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
noncomputable def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 2 0 0 ]
   [ 0 0 1 ]
   [ 0 1 0 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)

/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 1 0  0 ]
   [ 0 1 -1 ]
   [ 0 1  1 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

variable [Fintype l]

theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟(PD l R)) = 1 := by
  rw [PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)

theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Unit ⊕ l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr, Sum.elim_inr, Sum.inl_injective.eq_iff,
      Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
noncomputable def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit ⊕ l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jb_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]

end Orthogonal

end LieAlgebra
