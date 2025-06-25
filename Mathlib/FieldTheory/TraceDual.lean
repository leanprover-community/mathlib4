/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Dual of a basis for the trace

## Main definition

* `Basis.traceDual`: The dual basis of a basis for the trace in a finite separable extension.

## Main results

* `Basis.traceDual_eq_iff`: A family of vectors `v` is the dual for the trace of the basis `b` iff
  `∀ i j, Tr(v i * b j) = δ_ij`.

* `Submodule.traceDual_span_of_basis`: If the module `I` is spanned by the basis `b`, then its dual
  module for the trace is spanned by `b.traceDual`.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι K L)

/--
The dual basis of a basis for the trace in a finite separable extension.
-/
noncomputable def Basis.traceDual :
    Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

theorem Basis.traceDual_def :
    b.traceDual = (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b := rfl

@[simp]
theorem Basis.traceDual_repr_apply (x : L) (i : ι) :
    (b.traceDual).repr x i = (Algebra.traceForm K L x) (b i) :=
  (Algebra.traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]
theorem Basis.trace_traceDual_mul (i j : ι) :
    Algebra.trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
theorem Basis.trace_mul_traceDual (i j : ι) :
    Algebra.trace K L ((b i) * (b.traceDual j)) = if i = j then 1 else 0 := by
  refine (Algebra.traceForm K L).apply_dualBasis_right _ (Algebra.traceForm_isSymm K) _ i j

@[simp]
theorem Basis.traceDual_traceDual :
    b.traceDual.traceDual = b :=
  (Algebra.traceForm K L).dualBasis_dualBasis _ (Algebra.traceForm_isSymm K) _

variable (K L)

theorem Basis.traceDual_involutive :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  fun b ↦ traceDual_traceDual b

theorem Basis.traceDual_injective :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceDual_involutive K L).injective

variable {K L}

theorem Basis.traceDual_inj (b' : Basis ι K L) :
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

/--
A family of vectors `v` is the dual for the trace of the basis `b` iff
`∀ i j, Tr(v i * b j) = δ_ij`.
-/
@[simp]
theorem Basis.traceDual_eq_iff {v : ι → L} :
    b.traceDual = v ↔
      ∀ i j, Algebra.traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

/--
If the module `I` is spanned by the basis `b`, then its dual module for the trace is spanned by
`b.traceDual`.
-/
theorem Submodule.traceDual_span_of_basis (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L)
    (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
  rw [restrictScalars_traceDual, hb]
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b
