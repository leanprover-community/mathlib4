/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Scalarization of vector-valued reproducing kernel Hilbert spaces

A vector-valued RKHS `H` of functions `X → V` can be seen as a scalar-valued RKHS of functions
`X × V → 𝕜` via `f ↦ ((x, v) ↦ ⟪v, f x⟫)`. Its kernel is the *scalarization*
`((x, v), (y, u)) ↦ ⟪v, K x y u⟫` of the kernel `K` of `H`.

## Main definitions

- `Matrix.scalarize`: the scalar kernel `((x, v), (y, u)) ↦ ⟪v, K x y u⟫` associated to
  an operator-valued kernel `K`.
- `RKHS.Scalarization`: a vector-valued RKHS `H` viewed as a scalar-valued RKHS.
- `RKHS.scalarizeEquiv`: the isometric equivalence between a vector-valued RKHS and any
  scalar-valued RKHS whose kernel is the scalarization of its kernel.

## Main results

- `RKHS.scalarize_kernel`: the scalarization of the kernel is the Gram matrix of the kernel
  functions.
- `Matrix.PosSemidef.scalarize`: the scalarization of a positive semidefinite kernel is positive
  semidefinite.
- `RKHS.Scalarization.scalarKernel_scalarization`: the scalar kernel of `Scalarization H` is the
  scalarization of the kernel of `H`.
-/

public noncomputable section

open ContinuousLinearMap InnerProductSpace

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [RKHS 𝕜 H X V] [CompleteSpace H]
variable {K : Matrix X X (V →L[𝕜] V)}

/-- The scalarization of an operator-valued kernel `K : Matrix X X (V →L[𝕜] V)` is the scalar
kernel on `X × V` with entries `((x, v), (y, u)) ↦ ⟪v, K x y u⟫`. -/
@[expose]
def _root_.Matrix.scalarize (K : Matrix X X (V →L[𝕜] V)) : Matrix (X × V) (X × V) 𝕜 :=
  .of fun (x, v) (y, u) ↦ ⟪v, K x y u⟫_𝕜

@[simp]
lemma _root_.Matrix.scalarize_apply (K : Matrix X X (V →L[𝕜] V)) (x y : X) (u v : V) :
    K.scalarize (x, v) (y, u) = ⟪v, K x y u⟫_𝕜 := rfl

lemma _root_.Matrix.scalarize_injective :
    Function.Injective (Matrix.scalarize : Matrix X X (V →L[𝕜] V) → _) := by
  intro _ _ h
  ext
  refine ext_inner_left 𝕜 fun v ↦ ?_
  rw [← Matrix.scalarize_apply, ← Matrix.scalarize_apply, h]

@[simp]
lemma _root_.Matrix.scalarize_inj_iff {K L : Matrix X X (V →L[𝕜] V)} :
    K.scalarize = L.scalarize ↔ K = L :=
  Matrix.scalarize_injective.eq_iff

variable [CompleteSpace V]

/-- The scalarization of a Hermitian kernel is Hermitian. -/
theorem _root_.Matrix.IsHermitian.scalarize (hK : K.IsHermitian) : K.scalarize.IsHermitian := by
  ext
  rw [Matrix.conjTranspose_apply, Matrix.scalarize_apply, Matrix.scalarize_apply,
    ← hK.apply, star_eq_adjoint, adjoint_inner_right, RCLike.star_def, inner_conj_symm]

/-- The scalarization of the kernel is the Gram matrix of the kernel functions. -/
lemma scalarize_kernel :
    (kernel H).scalarize = .gram 𝕜 fun (x, v) ↦ kerFun H x v := by
  ext
  rw [Matrix.scalarize_apply, Matrix.gram_apply, kerFun_inner, kerFun_apply]

open scoped ComplexOrder in
theorem _root_.Matrix.PosSemidef.scalarize {K : Matrix X X (V →L[𝕜] V)}
    (hK : K.PosSemidef) : K.scalarize.PosSemidef := by
  have : Fact K.PosSemidef := ⟨hK⟩
  rw [← OfKernel.kernel_ofKernel (K := K), scalarize_kernel]
  exact Matrix.posSemidef_gram 𝕜 _

open scoped ComplexOrder in
instance [Fact K.PosSemidef] : Fact K.scalarize.PosSemidef := ⟨(Fact.out : K.PosSemidef).scalarize⟩

variable (H) in
/-- Type synonym for viewing the vector-valued RKHS `H` of functions `X → V` as a scalar-valued
RKHS of functions `X × V → 𝕜` via `f ↦ ((x, v) ↦ ⟪v, f x⟫)`. -/
@[expose, nolint unusedArguments]
def Scalarization : Type _ := H

namespace Scalarization

instance : NormedAddCommGroup (Scalarization H) := inferInstanceAs (NormedAddCommGroup H)
instance : InnerProductSpace 𝕜 (Scalarization H) := inferInstanceAs (InnerProductSpace 𝕜 H)
instance : CompleteSpace (Scalarization H) := inferInstanceAs (CompleteSpace H)

variable (𝕜 H) in
/-- The identity map from `H` to its scalarization, as a linear isometric equivalence. -/
@[expose]
def toScalarization : H ≃ₗᵢ[𝕜] Scalarization H := .refl 𝕜 H

instance instRKHS : RKHS 𝕜 (Scalarization H) (X × V) 𝕜 where
  -- An element `f` coerces to `(x, v) ↦ ⟪v, f x⟫`.
  coeCLM := (.pi fun (x, v) ↦ innerSL 𝕜 v ∘L eval H x) ∘L
    (toScalarization 𝕜 H).symm.toLinearIsometry.toContinuousLinearMap
  coeCLM_injective := by
    simp only [coe_comp]
    refine Function.Injective.comp ?_ (toScalarization 𝕜 H).symm.injective
    intro _ _ h
    ext x
    exact ext_inner_left 𝕜 fun v ↦ congr_fun h (x, v)

omit [CompleteSpace H] [CompleteSpace V] in
@[simp]
lemma toScalarization_apply (f : H) (x : X) (v : V) :
    toScalarization 𝕜 H f (x, v) = ⟪v, f x⟫_𝕜 := by
  rfl

@[simp]
lemma kerFun_scalarization (x : X) (v : V) (c : 𝕜) :
    kerFun (Scalarization H) (x, v) c = toScalarization 𝕜 H (c • kerFun H x v) := by
  refine ext_inner_right 𝕜 fun f ↦ ?_
  obtain ⟨f, rfl⟩ := (toScalarization 𝕜 H).surjective f
  simp [inner_smul_left, mul_comm]

@[simp]
lemma scalarKernel_scalarization : scalarKernel (Scalarization H) = (kernel H).scalarize := by
  ext ⟨x, v⟩ ⟨y, u⟩
  simp [← kerFun_apply]

end Scalarization

open Scalarization

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] [CompleteSpace H']
variable [RKHS 𝕜 H' (X × V) 𝕜]

/-- A vector-valued RKHS `H` is isometrically isomorphic to any scalar-valued RKHS `H'`
whose (scalar) kernel is the scalarization of the kernel of `H`. -/
def scalarizeEquiv (h : (kernel H).scalarize = scalarKernel H') :
    H ≃ₗᵢ[𝕜] H' :=
  (toScalarization 𝕜 H).trans (equiv (scalarKernel_eq_iff.mp (scalarKernel_scalarization.trans h)))

@[simp]
theorem scalarizeEquiv_apply (h : (kernel H).scalarize = scalarKernel H') (f : H) (x : X) (v : V) :
    scalarizeEquiv h f (x, v) = ⟪v, f x⟫_𝕜 := by
  simp [scalarizeEquiv]

theorem scalarizeEquiv_kerFun (h : (kernel H).scalarize = scalarKernel H') (x : X) (v : V) :
    scalarizeEquiv h (kerFun H x v) = kerFun H' (x, v) 1 := by
  simp [scalarizeEquiv,
    ← equiv_kerFun (scalarKernel_eq_iff.mp (scalarKernel_scalarization.trans h))]

end RKHS
