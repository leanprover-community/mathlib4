/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.UniformSpace.ProdApproximation

/-!
# Abstract measures on topological spaces

We define an "abstract measure" on `X`, with values in a normed ring `R`, to be an `R`-linear
functional on continuous maps `X → R`. This is an important construction in p-adic analysis (where
the Iwasawa algebra is defined as the space of abstract measures on `ℤ_[p]` with values in `ℚ_[p]`).
-/

public section

open ContinuousMap

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Module R E] [ContinuousSMul R E]

section Defs

/-!
### Basic definitions
-/

variable (X R E) in
/--
The space of `E`-valued measures on `X`, i.e. continuous linear maps `C(X, R) → E`. (The case
`R = E` is the most important case.)

This is the same space `C(X, R) →L[R] E`, but we do not want it to inherit the default
(norm) topology, so we make a type synonym.
-/
@[expose] def AbstractMeasure := C(X, R) →L[R] E

@[inherit_doc]
scoped [AbstractMeasure] notation "D(" X ", " R ")" => AbstractMeasure X R R

end Defs

namespace AbstractMeasure

/-- Inherit `FunLike` structure from `C(X, R) →L[R] E`. -/
instance : FunLike (AbstractMeasure X R E) C(X, R) E :=
  inferInstanceAs (FunLike (C(X, R) →L[R] E) C(X, R) E)

/-- Inherit `ContinuousLinearMapClass` structure from `C(X, R) →L[R] E`. -/
instance : ContinuousLinearMapClass (AbstractMeasure X R E) R C(X, R) E :=
  inferInstanceAs (ContinuousLinearMapClass (C(X, R) →L[R] E) R C(X, R) E)

/-- Inherit `AddCommGroup` structure from `C(X, R) →L[R] E`. -/
instance : AddCommGroup (AbstractMeasure X R E) :=
  inferInstanceAs (AddCommGroup (C(X, R) →L[R] E))

/-- Inherit `R`-module structure from `C(X, R) →L[R] E`. -/
instance : Module R (AbstractMeasure X R E) :=
  inferInstanceAs (Module R (C(X, R) →L[R] E))

@[simp]
lemma smul_apply (r : R) (μ : AbstractMeasure X R E) (f : C(X, R)) : (r • μ) f = r • μ f :=
  rfl

omit [ContinuousSMul R E] in
@[simp] lemma add_apply (μ ν : AbstractMeasure X R E) (f : C(X, R)) :
    (μ + ν) f = μ f + ν f :=
  rfl

variable (R) in
/-- The Dirac measure, "evaluation at `x`". -/
def dirac (x : X) : D(X, R) :=
  ContinuousMap.evalCLM R x

@[simp] lemma dirac_apply (x : X) (f : C(X, R)) : dirac R x f = f x := (rfl)

section Map

/-- Measures can be pushed forward (R-linearly) along continuous maps. -/
def map (f : C(X, Y)) : AbstractMeasure X R E →ₗ[R] AbstractMeasure Y R E where
  toFun μ := μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma map_apply (f : C(X, Y)) (μ : AbstractMeasure X R E) (g : C(Y, R)) :
    map f μ g = μ (g.comp f) :=
  (rfl)

@[simp] lemma map_map {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (μ : AbstractMeasure X R E) :
    map g (map f μ) = map (g.comp f) μ :=
  (rfl)

@[simp]
lemma map_id (μ : AbstractMeasure X R E) :
    map (.id X) μ = μ :=
  (rfl)

@[simp] lemma map_dirac (f : C(X, Y)) (x : X) :
    map f (dirac R x) = dirac R (f x) :=
  (rfl)

end Map

section Prod

/-!
### Product structure
-/

-- note we define `contractSnd` first, because `f.curry` only works one way round

/-- Send a measure `ν` on `Y` and a function `f` on `X × Y` to the function on `X` given by
`x ↦ ν (f (x, ·))`, or more suggestively, `x ↦ ∫ f(x, y) dμ(y)`. -/
def contractSnd : D(Y, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(X, R) :=
  LinearMap.mk₂ R (fun ν f ↦ comp ν f.curry)
    (fun ν ν' f ↦ by ext; simp)
    (fun r ν f ↦ by ext; simp)
    (fun ν f f' ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, ContinuousMap.add_apply, ← map_add]
      rfl)
    (fun ν r f ↦ by
      ext x
      simp only [comp_apply, ContinuousMap.coe_coe, ContinuousMap.smul_apply, ← map_smul]
      rfl)

/-- Send a measure `μ` on `X` and a function `f` on `X × Y` to the function on `Y` given by
`y ↦ μ (f (·, y))`, or more suggestively, `y ↦ ∫ f(x, y) dμ(x)`. -/
def contractFst : D(X, R) →ₗ[R] C(X × Y, R) →ₗ[R] C(Y, R) :=
  ((prodSwap.compCLM R R).toLinearMap.lcomp R _).comp contractSnd

variable (μ : D(X, R)) (ν : D(Y, R))

@[simp] lemma contractFst_apply (f : C(X × Y, R)) (y : Y) :
    contractFst μ f y = μ ⟨fun x ↦ f (x, y), by continuity⟩ :=
  (rfl)

@[simp] lemma contractSnd_apply (f : C(X × Y, R)) (x : X) :
    contractSnd ν f x = ν ⟨fun y ↦ f (x, y), by continuity⟩ :=
  (rfl)

lemma contractFst_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractFst (dirac R x) f y = f (x, y) :=
  (rfl)

lemma contractSnd_dirac (x : X) (y : Y) (f : C(X × Y, R)) :
    contractSnd (dirac R y) f x = f (x, y) :=
  (rfl)

section LocallyCompact

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/-- `AbstractMeasure.contractSnd` bundled with continuity in the function argument. -/
private def contractSndCLM : D(Y, R) →ₗ[R] C(X × Y, R) →L[R] C(X, R) where
  toFun ν := ⟨contractSnd ν, by
    refine continuous_of_continuous_uncurry _ (ν.continuous.comp ?_)
    apply continuous_of_continuous_uncurry
    rw [← (Homeomorph.prodAssoc C(X × Y, R) X Y).symm.comp_continuous_iff']
    exact ContinuousEval.continuous_eval⟩
  map_add' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_add _ _
  map_smul' _ _ := ContinuousLinearMap.coe_injective.eq_iff.mp <| contractSnd.map_smul _ _

/-- `AbstractMeasure.contractFst` bundled with continuity in the function argument. -/
private def contractFstCLM : D(X, R) →ₗ[R] C(X × Y, R) →L[R] C(Y, R) :=
  ((ContinuousMap.prodSwap.compCLM R R).lcomp _).comp contractSndCLM

/-- "Left-handed" version of the natural product map on measures (acting on functions
as first integrating along `X`, and then integrating the result along `Y`). -/
def prodMk : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  (ContinuousLinearMap.llcomp _ _ _ R).comp contractFstCLM

@[simp] lemma prodMk_apply (f : C(X × Y, R)) :
  prodMk μ ν f = ν (μ.contractFst f) := (rfl)

/-- On functions of the form `(x, y) ↦ f x * g y`, the measure `prodMk μ ν` agrees with the
algebraic tensor product of `μ` and `ν`. -/
lemma prodMk_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [← smul_eq_mul, prodMk_apply, ← map_smul]
  congr 1 with y
  simp_rw [contractFst_apply, ContinuousMap.smul_apply, smul_eq_mul, mul_comm (μ f) (g y),
    ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (g y) (f x)]
  rfl

/-- "Right-handed" version of the natural product map on measures (acting on functions
as first integrating along `Y`, and then integrating the result along `X`). -/
def prodMk' : D(X, R) →ₗ[R] D(Y, R) →ₗ[R] D(X × Y, R) :=
  ((ContinuousLinearMap.llcomp R _ _ R).comp contractSndCLM).flip

@[simp]
lemma prodMk'_apply (f : C(X × Y, R)) : (μ.prodMk' ν) f = μ (ν.contractSnd f) := (rfl)

lemma prodMk'_flip (f : C(X × Y, R)) :
    (μ.prodMk' ν) f = (ν.prodMk μ) (f.comp ContinuousMap.prodSwap) := (rfl)

lemma prodMk'_prod_apply (f : C(X, R)) (g : C(Y, R)) :
    prodMk' μ ν ((f.comp .fst) * (g.comp .snd)) = μ f * ν g := by
  simp only [prodMk'_apply, mul_comm (μ f) (ν g), ← smul_eq_mul, ← map_smul]
  congr 1 with x
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul, mul_comm (ν g) (f x), contractSnd_apply,
    ← smul_eq_mul, ← map_smul]
  rfl

end LocallyCompact

section Profinite

variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y] [TotallyDisconnectedSpace X]
  [T0Space R]

/-- For profinite spaces, the two product structures on measures agree. -/
lemma prodMk_eq_prodMk' : prodMk μ ν = prodMk' μ ν := by
  apply DFunLike.coe_injective
  apply ContinuousMap.denseRange_tensorHom.equalizer (by fun_prop) (by fun_prop)
  ext h
  induction h with
  | zero => grind
  | add => grind
  | tmul f g => simp [tensorHom, prodMul_def, prodMk_prod_apply μ ν f g, prodMk'_prod_apply μ ν f g]

end Profinite

end Prod

end AbstractMeasure

end
