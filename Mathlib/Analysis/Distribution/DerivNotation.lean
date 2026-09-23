/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-! # Type classes for derivatives and the Laplacian

In this file we define notation type classes for line derivatives, also known as partial
derivatives, and for the Laplacian.

Moreover, we provide type-classes that encode the linear structure.
We also define the iterated line derivative and prove elementary properties.
We define a Laplacian based on the sum of second derivatives formula and prove that the Laplacian
thus defined is independent of the choice of basis.

Currently, this type class is only used by Schwartz functions. Future uses include derivatives on
test functions, distributions, tempered distributions, and Sobolev spaces (and other generalized
function spaces).
-/

@[expose] public noncomputable section

universe u' u v w

variable {ι ι' 𝕜 R V E F V₁ V₂ V₃ : Type*}

/-! ## Line derivative -/

open Fin

/--
The notation typeclass for the line derivative.
-/
class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the line derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V → E → F

namespace LineDeriv

@[inherit_doc] scoped notation "∂_{" v "}" => LineDeriv.lineDerivOp v

variable {V E : Type*} [LineDeriv V E E]

/-- `∂^{m} f` is the iterated line derivative of `f`, where `m` is a finite number of (different)
directions. -/
def iteratedLineDerivOp {n : ℕ} : (Fin n → V) → E → E :=
  Nat.recOn n (fun _ ↦ id) (fun _ rec y ↦ LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]
theorem iteratedLineDerivOp_fin_zero (m : Fin 0 → V) (f : E) : ∂^{m} f = f :=
  rfl

@[simp]
theorem iteratedLineDerivOp_one (m : Fin 1 → V) (f : E) : ∂^{m} f = ∂_{m 0} f :=
  rfl

theorem iteratedLineDerivOp_succ_left {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂_{m 0} (∂^{tail m} f) :=
  rfl

theorem iteratedLineDerivOp_succ_right {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂^{init m} (∂_{m (last n)} f) := by
  induction n with
  | zero => rfl
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : init m 0 = m 0 := by simp only [init_def, castSucc_zero]
    have hmtail : tail m (last n) = m (last n.succ) := by
      simp only [tail_def, succ_last]
    calc
      _ = ∂_{m 0} (∂^{tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{init <| tail m} (∂_{tail m <| last n} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        rw [hmtail, iteratedLineDerivOp_succ_left, hmzero, tail_init_eq_init_tail]

@[simp]
theorem iteratedLineDerivOp_const_eq_iter_lineDerivOp (n : ℕ) (y : V) (f : E) :
    ∂^{fun (_ : Fin n) ↦ y} f = ∂_{y}^[n] f := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, Function.iterate_succ_apply']
    congr

end LineDeriv

open LineDeriv

/--
The line derivative is additive, `∂_{v} (x + y) = ∂_{v} x + ∂_{v} y` for all `x y : E`
and `∂_{v + w} x = ∂_{v} x + ∂_{w} y` for all `v w : V`.

Note that `lineDeriv` on functions is not additive.
-/
class LineDerivAdd (V : Type u) (E : Type v) (F : outParam (Type w))
    [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] where
  lineDerivOp_add (v : V) (x y : E) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
  lineDerivOp_left_add (v w : V) (x : E) : ∂_{v + w} x = ∂_{v} x + ∂_{w} x

/--
The line derivative commutes with scalar multiplication, `∂_{v} (r • x) = r • ∂_{v} x` for all
`r : R` and `x : E`.
-/
class LineDerivSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R E] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_smul (v : V) (r : R) (x : E) : ∂_{v} (r • x) = r • ∂_{v} x

/--
The line derivative commutes with scalar multiplication, `∂_{r • v} x = r • ∂_{v} x` for all
`r : R` and `v : V`.
-/
class LineDerivLeftSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R V] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_left_smul (r : R) (v : V) (x : E) : ∂_{r • v} x = r • ∂_{v} x

/--
The line derivative is continuous.
-/
class ContinuousLineDeriv (V : Type u) (E : Type v) (F : outParam (Type w))
    [TopologicalSpace E] [TopologicalSpace F] [LineDeriv V E F] where
  continuous_lineDerivOp (v : V) : Continuous (∂_{v} : E → F)

attribute [fun_prop] ContinuousLineDeriv.continuous_lineDerivOp

namespace LineDeriv

export LineDerivAdd (lineDerivOp_add)
export LineDerivAdd (lineDerivOp_left_add)
export LineDerivSMul (lineDerivOp_smul)
export LineDerivLeftSMul (lineDerivOp_left_smul)
export ContinuousLineDeriv (continuous_lineDerivOp)

section lineDerivOp

variable [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] [LineDerivAdd V E F]

@[simp]
theorem lineDerivOp_zero (v : V) : ∂_{v} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v))

@[simp]
theorem lineDerivOp_neg (v : V) (x : E) : ∂_{v} (-x) = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) x

@[simp]
theorem lineDerivOp_sum (v : V) (f : ι → E) (s : Finset ι) :
    ∂_{v} (∑ i ∈ s, f i) = ∑ i ∈ s, ∂_{v} (f i) :=
  map_sum (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) f s

@[simp]
theorem lineDerivOp_left_zero (x : E) : ∂_{(0 : V)} x = 0 :=
  map_zero (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x))

@[simp]
theorem lineDerivOp_left_neg (v : V) (x : E) : ∂_{-v} x = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) v

@[simp]
theorem lineDerivOp_left_sum (f : ι → V) (x : E) (s : Finset ι) :
    ∂_{∑ i ∈ s, f i} x = ∑ i ∈ s, ∂_{f i} x :=
  map_sum (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) f s

end lineDerivOp

section lineDerivOpCLM

variable [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] [AddCommGroup V]
  [LineDeriv V E F] [LineDerivAdd V E F] [LineDerivSMul R V E F] [ContinuousLineDeriv V E F]

variable (R E) in
/-- The line derivative as a continuous linear map. -/
def lineDerivOpCLM (m : V) : E →L[R] F where
  toFun := ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m
  cont := by fun_prop

@[simp]
theorem lineDerivOpCLM_apply (m : V) (x : E) :
    lineDerivOpCLM R E m x = ∂_{m} x := rfl

end lineDerivOpCLM

section iteratedLineDerivOp

variable [LineDeriv V E E]
variable {n : ℕ} (m : Fin n → V)

section add

variable [AddCommGroup V] [AddCommGroup E] [LineDerivAdd V E E]

theorem iteratedLineDerivOp_add (x y : E) :
    ∂^{m} (x + y) = ∂^{m} x + ∂^{m} y := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

@[simp]
theorem iteratedLineDerivOp_zero : ∂^{m} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m))

@[simp]
theorem iteratedLineDerivOp_neg (x : E) : ∂^{m} (-x) = - ∂^{m} x :=
  map_neg (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) x

@[simp]
theorem iteratedLineDerivOp_sum (f : ι → E) (s : Finset ι) :
    ∂^{m} (∑ i ∈ s, f i) = ∑ i ∈ s, ∂^{m} (f i) :=
  map_sum (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) f s

end add

theorem iteratedLineDerivOp_smul [SMul R E] [LineDerivSMul R V E E] (r : R) (x : E) :
    ∂^{m} (r • x) = r • ∂^{m} x := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_smul]

variable [TopologicalSpace E]

@[fun_prop]
theorem continuous_iteratedLineDerivOp [ContinuousLineDeriv V E E] {n : ℕ} (m : Fin n → V) :
    Continuous (∂^{m} : E → E) := by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

variable [Ring R] [AddCommGroup V] [AddCommGroup E] [Module R E]
  [LineDerivAdd V E E] [LineDerivSMul R V E E] [ContinuousLineDeriv V E E]

variable (R E) in
/-- The iterated line derivative as a continuous linear map. -/
def iteratedLineDerivOpCLM {n : ℕ} (m : Fin n → V) : E →L[R] E where
  toFun := ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m
  cont := by fun_prop

@[simp]
theorem iteratedLineDerivOpCLM_apply {n : ℕ} (m : Fin n → V) (x : E) :
    iteratedLineDerivOpCLM R E m x = ∂^{m} x := rfl

end iteratedLineDerivOp

end LineDeriv

/-! ## Laplacian -/

/--
The notation typeclass for the Laplace operator.
-/
class Laplacian (E : Type v) (F : outParam (Type w)) where
  /-- `Δ f` is the Laplacian of `f`. The meaning of this notation is type-dependent. -/
  laplacian : E → F

namespace Laplacian

@[inherit_doc] scoped notation "Δ" => Laplacian.laplacian

end Laplacian

namespace LineDeriv

variable [LineDeriv E V₁ V₂] [LineDeriv E V₂ V₃]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]

/-! ## Laplacian of `LineDeriv` -/

section TensorProduct

variable [CommRing R] [AddCommGroup E] [Module R E]
  [Module R V₂] [Module R V₃]
  [LineDerivAdd E V₂ V₃] [LineDerivAdd E V₁ V₂]
  [LineDerivSMul R E V₂ V₃] [LineDerivLeftSMul R E V₁ V₂] [LineDerivLeftSMul R E V₂ V₃]

open InnerProductSpace TensorProduct

variable (R) in
/-- The second derivative in terms `lineDerivOp` as a bilinear map.

Mainly used to give an abstract definition of the Laplacian. -/
def bilinearLineDerivTwo (f : V₁) : E →ₗ[R] E →ₗ[R] V₃ :=
  LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

variable (R) in
/-- The second derivative in terms `lineDerivOp` as a linear map from the tensor product.

Mainly used to give an abstract definition of the Laplacian. -/
def tensorLineDerivTwo (f : V₁) : E ⊗[R] E →ₗ[R] V₃ :=
  lift (bilinearLineDerivTwo R f)

lemma tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp (f : V₁) (v w : E) :
    tensorLineDerivTwo R f (v ⊗ₜ[R] w) = ∂_{v} (∂_{w} f) := lift.tmul _ _

end TensorProduct

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section LinearMap

variable [Module ℝ V₂] [Module ℝ V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivAdd E V₂ V₃]
  [LineDerivSMul ℝ E V₂ V₃] [LineDerivLeftSMul ℝ E V₁ V₂] [LineDerivLeftSMul ℝ E V₂ V₃]

open TensorProduct InnerProductSpace

theorem tensorLineDerivTwo_canonicalCovariantTensor_eq_sum [Fintype ι] (v : OrthonormalBasis ι ℝ E)
    (f : V₁) : tensorLineDerivTwo ℝ f (canonicalCovariantTensor E) = ∑ i, ∂_{v i} (∂_{v i} f) := by
  simp [InnerProductSpace.canonicalCovariantTensor_eq_sum E v,
    tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp]

end LinearMap

section ContinuousLinearMap

section definition

variable [CommRing R]
  [Module R V₁] [Module R V₂] [Module R V₃]
  [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace V₃] [IsTopologicalAddGroup V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivSMul R E V₁ V₂] [ContinuousLineDeriv E V₁ V₂]
  [LineDerivAdd E V₂ V₃] [LineDerivSMul R E V₂ V₃] [ContinuousLineDeriv E V₂ V₃]

variable (R E V₁) in
/-- The Laplacian defined by iterated `lineDerivOp` as a continuous linear map. -/
def laplacianCLM : V₁ →L[R] V₃ :=
  ∑ i, lineDerivOpCLM R V₂ (stdOrthonormalBasis ℝ E i) ∘L
    lineDerivOpCLM R V₁ (stdOrthonormalBasis ℝ E i)

end definition

variable [Module ℝ V₁] [Module ℝ V₂] [Module ℝ V₃]
  [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace V₃] [IsTopologicalAddGroup V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivSMul ℝ E V₁ V₂] [ContinuousLineDeriv E V₁ V₂]
  [LineDerivAdd E V₂ V₃] [LineDerivSMul ℝ E V₂ V₃] [ContinuousLineDeriv E V₂ V₃]
  [LineDerivLeftSMul ℝ E V₁ V₂] [LineDerivLeftSMul ℝ E V₂ V₃]

theorem laplacianCLM_eq_sum [Fintype ι] (v : OrthonormalBasis ι ℝ E) (f : V₁) :
    laplacianCLM ℝ E V₁ f = ∑ i, ∂_{v i} (∂_{v i} f) := by
  simp [laplacianCLM, ← tensorLineDerivTwo_canonicalCovariantTensor_eq_sum]

end ContinuousLinearMap

end InnerProductSpace

end LineDeriv
