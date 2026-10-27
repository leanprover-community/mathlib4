/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!  # The unitization (over `R`) of `C₀(X, R)` is `C(OnePoint X, R)`

Given a topological space `X` and a topological ring `R` one can extend an element `C₀(X, R)`, the
continuous functions vanishing at infinity, to `C(OnePoint X, R)`, the continuous functions on the
one-point compactification of `X`, by taking the value `0` at `∞`. This can be lifted to an
equivalence between `Unitization R C₀(X, R)` and `C(OnePoint X, R)`.

## Main definitions

+ `ZeroAtInftyContinuousMap.toOnePoint : C₀(X, R) → C(OnePoint X, R)` : the extension of
  `f : C₀(X, R)` to the function which takes the value `0` at `∞`
+ `ContinuousMap.toZeroAtInfty: C(OnePoint X, R) → C₀(X, R)` : `f ↦ fun x ↦ g x - g ∞`
* `ZeroAtInftyContinuousMap.unitizationEquiv : Unitization R C₀(X, R) ≃ C(OnePoint X, R)` :
  lift `ZeroAtInftyContinuousMap.toOnePoint` to an equivalence from the `Unitization`, with
  inverse given by `f ↦ .mk (f ∞, f.toZeroAtInfty)`
* Various bundled versions of all of the above.

## Implementation notes

The simp normal form of each bundled morphism is the unbundled map, so the unbundled maps
have their own simp lemmas for various operatoins.
-/

@[expose] public section

open Filter Topology OnePoint ZeroAtInfty

variable {X R S : Type*} [TopologicalSpace X] [R1Space X]

namespace ZeroAtInftyContinuousMap

variable [TopologicalSpace R]

/-- Extension by zero of a continuous function vanishing at infinity, as a continuous function on
the one-point compactification. -/
def toOnePoint [Zero R] (f : C₀(X, R)) : C(OnePoint X, R) :=
  OnePoint.continuousMapMk f.toContinuousMap 0 <| by
    rw [coclosedCompact_eq_cocompact]
    exact zero_at_infty f

@[simp]
lemma toOnePoint_infty [Zero R] (f : C₀(X, R)) :
    f.toOnePoint ∞ = 0 := rfl

@[simp]
lemma toOnePoint_coe [Zero R] (f : C₀(X, R)) (x : X) :
    f.toOnePoint x = f x := rfl

lemma toOnePoint_injective [Zero R] :
    Function.Injective (toOnePoint (X := X) (R := R)) := fun _ _ h ↦
  ext fun x ↦ by simpa using congr($h (x : OnePoint X))

@[simp]
lemma toOnePoint_zero [Zero R] :
    (0 : C₀(X, R)).toOnePoint = 0 := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_add [AddZeroClass R] [ContinuousAdd R] (f g : C₀(X, R)) :
    (f + g).toOnePoint = f.toOnePoint + g.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_neg [AddGroup R] [IsTopologicalAddGroup R] (f : C₀(X, R)) :
    (-f).toOnePoint = -f.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_sub [AddGroup R] [IsTopologicalAddGroup R] (f g : C₀(X, R)) :
    (f - g).toOnePoint = f.toOnePoint - g.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_mul [MulZeroClass R] [ContinuousMul R] (f g : C₀(X, R)) :
    (f * g).toOnePoint = f.toOnePoint * g.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_smul [Zero R] [Zero S] [SMulWithZero S R] [ContinuousConstSMul S R]
    (s : S) (f : C₀(X, R)) :
    (s • f).toOnePoint = s • f.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma toOnePoint_star [AddMonoid R] [StarAddMonoid R] [ContinuousStar R]
    (f : C₀(X, R)) : (star f).toOnePoint = star f.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

variable (X R S)

/-- `ZeroAtInftyContinuousMap.toOnePoint` as an `AddMonoidHom`. -/
@[simps]
def toOnePointAddMonoidHom [AddMonoid R] [ContinuousAdd R] :
    C₀(X, R) →+ C(OnePoint X, R) where
  toFun := toOnePoint
  map_zero' := toOnePoint_zero
  map_add' := toOnePoint_add

/-- `ZeroAtInftyContinuousMap.toOnePoint` as a `LinearMap`. -/
@[simps]
def toOnePointLinearMap [Semiring S] [AddCommMonoid R] [ContinuousAdd R] [Module S R]
    [ContinuousConstSMul S R] : C₀(X, R) →ₗ[S] C(OnePoint X, R) where
  toFun := toOnePoint
  map_add' := toOnePoint_add
  map_smul' := toOnePoint_smul

@[simp]
lemma toAddMonoidHom_toOnePointLinearMap [Semiring S] [AddCommMonoid R] [ContinuousAdd R]
    [Module S R] [ContinuousConstSMul S R] :
    (toOnePointLinearMap X R S).toAddMonoidHom = toOnePointAddMonoidHom X R := rfl

/-- `ZeroAtInftyContinuousMap.toOnePoint` as a `NonUnitalRingHom`. -/
@[simps]
def toOnePointNonUnitalRingHom [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] : C₀(X, R) →ₙ+* C(OnePoint X, R) where
  __ := toOnePointAddMonoidHom X R
  toFun := toOnePoint
  map_mul' := toOnePoint_mul

@[simp]
lemma toAddMonoidHom_toOnePointNonUnitalRingHom [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] :
    (toOnePointNonUnitalRingHom X R).toAddMonoidHom = toOnePointAddMonoidHom X R := rfl

/-- `ZeroAtInftyContinuousMap.toOnePoint` as a `NonUnitalAlgHom`. -/
@[simps apply]
def toOnePointNonUnitalAlgHom [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R]
    [Semiring S] [Module S R] [ContinuousConstSMul S R] : C₀(X, R) →ₙₐ[S] C(OnePoint X, R) where
  __ := toOnePointNonUnitalRingHom X R
  toFun := toOnePoint
  map_smul' := toOnePoint_smul

/-- `ZeroAtInftyContinuousMap.toOnePoint` as a `NonUnitalStarAlgHom`. -/
@[simps apply]
def toOnePointNonUnitalStarAlgHom [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] [Semiring S] [Module S R] [ContinuousConstSMul S R] [StarRing R]
    [ContinuousStar R] : C₀(X, R) →⋆ₙₐ[S] C(OnePoint X, R) where
  __ := toOnePointNonUnitalAlgHom X R S
  toFun := toOnePoint
  map_star' := toOnePoint_star

@[simp]
lemma toNonUnitalAlgHom_toOnePointNonUnitalStarAlgHom [NonUnitalNonAssocSemiring R]
    [IsTopologicalSemiring R] [Semiring S] [Module S R] [ContinuousConstSMul S R] [StarRing R]
    [ContinuousStar R] :
    (toOnePointNonUnitalStarAlgHom X R S).toNonUnitalAlgHom = toOnePointNonUnitalAlgHom X R S :=
  rfl

end ZeroAtInftyContinuousMap

namespace ContinuousMap

variable [TopologicalSpace R] [AddCommGroup R] [IsTopologicalAddGroup R]

/-- The continuous function vanishing at infinity obtained by taking `g : C(OnePoint X, R)` and
restricting `g` to `X` and subtracting the constant `g ∞`. -/
def toZeroAtInfty (g : C(OnePoint X, R)) : C₀(X, R) where
  toFun x := g x - g ∞
  zero_at_infty' := by simpa [coclosedCompact_eq_cocompact] using
    g.continuous.tendsto (x := ∞) |>.comp tendsto_coe_infty |>.sub <| tendsto_const_nhds (x := g ∞)

@[simp]
lemma toZeroAtInfty_apply (g : C(OnePoint X, R)) (x : X) : g.toZeroAtInfty x = g x - g ∞ := rfl

@[simp]
lemma toZeroAtInfty_const (r : R) : (const (OnePoint X) r).toZeroAtInfty = 0 := by ext; simp

@[simp]
lemma toZeroAtInfty_zero : (0 : C(OnePoint X, R)).toZeroAtInfty = 0 := by ext; simp

@[simp]
lemma toZeroAtInfty_add (g h : C(OnePoint X, R)) :
    (g + h).toZeroAtInfty = g.toZeroAtInfty + h.toZeroAtInfty := by
  ext; simp; abel

@[simp]
lemma toZeroAtInfty_neg (g : C(OnePoint X, R)) :
    (-g).toZeroAtInfty = -g.toZeroAtInfty := by
  ext; simp; abel

@[simp]
lemma toZeroAtInfty_sub (g h : C(OnePoint X, R)) :
    (g - h).toZeroAtInfty = g.toZeroAtInfty - h.toZeroAtInfty := by
  ext; simp; abel

@[simp]
lemma toZeroAtInfty_smul [Semiring S] [Module S R] [ContinuousConstSMul S R]
    (s : S) (g : C(OnePoint X, R)) :
    (s • g).toZeroAtInfty = s • g.toZeroAtInfty := by
  ext; simp [smul_sub]

@[simp]
lemma toZeroAtInfty_star [StarAddMonoid R] [ContinuousStar R] (g : C(OnePoint X, R)) :
    (star g).toZeroAtInfty = star g.toZeroAtInfty := by
  ext; simp

variable (X R S)

/-- `ContinuousMap.toZeroAtInfty` as an `AddMonoidHom`. -/
@[simps]
def toZeroAtInftyAddMonoidHom : C(OnePoint X, R) →+ C₀(X, R) where
  toFun := toZeroAtInfty
  map_zero' := toZeroAtInfty_zero
  map_add' := toZeroAtInfty_add

/-- `ContinuousMap.toZeroAtInfty` as a `LinearMap`. -/
@[simps]
def toZeroAtInftyLinearMap [Semiring S] [Module S R] [ContinuousConstSMul S R] :
    C(OnePoint X, R) →ₗ[S] C₀(X, R) where
  toFun := toZeroAtInfty
  map_add' := toZeroAtInfty_add
  map_smul' := toZeroAtInfty_smul

@[simp]
lemma toAddMonoidHom_toZeroAtInftyLinearMap [Semiring S] [Module S R] [ContinuousConstSMul S R] :
    (toZeroAtInftyLinearMap X R S).toAddMonoidHom = toZeroAtInftyAddMonoidHom X R :=
  rfl

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open Unitization

variable [TopologicalSpace R]

section AddCommGroup

variable [AddCommGroup R] [IsTopologicalAddGroup R]

variable (X R) in
/-- The canonical equivalence `Unitization R C₀(X, R) ≃ C(OnePoint X, R)` mapping `(r, f)` to the
function taking the value `r` at `∞` and `r + f x` at `x : X`. Its inverse maps `g` to
`(g ∞, fun x ↦ g x - g ∞)`. This is the lift of `ZeroAtInftyContinuousMap.toOnePoint`.

Various bundlings are available including `unitizationAddEquiv`, `unitizationLinearEquiv`,
`unitizationRingEquiv`, `unitizationAlgEquiv`, `unitizationStarAlgEquiv`. -/
def unitizationEquiv : Unitization R C₀(X, R) ≃ C(OnePoint X, R) where
  toFun f := .const _ f.fst + f.snd.toOnePoint
  invFun g := .mk (g ∞, g.toZeroAtInfty)
  left_inv f := Unitization.ext (by simp) (by ext x; simp)
  right_inv g := by ext x; induction x using OnePoint.rec <;> simp

lemma unitizationEquiv_apply (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R f = .const _ f.fst + f.snd.toOnePoint := rfl

lemma unitizationEquiv_symm_apply (g : C(OnePoint X, R)) :
    (unitizationEquiv X R).symm g = .mk (g ∞, g.toZeroAtInfty) := rfl

@[simp]
lemma unitizationEquiv_apply_infty (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R f ∞ = f.fst := by
  simp [unitizationEquiv_apply]

@[simp]
lemma unitizationEquiv_apply_coe (f : Unitization R C₀(X, R)) (x : X) :
    unitizationEquiv X R f x = f.fst + f.snd x := by
  simp [unitizationEquiv_apply]

@[simp]
lemma unitizationEquiv_inl (r : R) : unitizationEquiv X R (inl r) = .const _ r := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma unitizationEquiv_inr (f : C₀(X, R)) : unitizationEquiv X R f = f.toOnePoint := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma unitizationEquiv_zero : unitizationEquiv X R 0 = 0 := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma unitizationEquiv_add (f g : Unitization R C₀(X, R)) :
    unitizationEquiv X R (f + g) = unitizationEquiv X R f + unitizationEquiv X R g := by
  ext x; induction x using OnePoint.rec <;> simp; abel

@[simp]
lemma unitizationEquiv_neg (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R (-f) = -unitizationEquiv X R f := by
  ext x; induction x using OnePoint.rec <;> simp; abel

@[simp]
lemma unitizationEquiv_sub (f g : Unitization R C₀(X, R)) :
    unitizationEquiv X R (f - g) = unitizationEquiv X R f - unitizationEquiv X R g := by
  simp [sub_eq_add_neg]

@[simp]
lemma unitizationEquiv_star [StarAddMonoid R] [ContinuousStar R] (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R (star f) = star (unitizationEquiv X R f) := by
  ext x; induction x using OnePoint.rec <;> simp

variable (X R) in
/-- `ZeroAtInftyContinuousMap.unitizationEquiv` as an `AddEquiv`. -/
def unitizationAddEquiv : Unitization R C₀(X, R) ≃+ C(OnePoint X, R) where
  toEquiv := unitizationEquiv X R
  map_add' := unitizationEquiv_add

@[simp]
lemma coe_unitizationAddEquiv : ⇑(unitizationAddEquiv X R) = unitizationEquiv X R := rfl

@[simp]
lemma coe_unitizationAddEquiv_symm :
    ⇑(unitizationAddEquiv X R).symm = (unitizationEquiv X R).symm := rfl

-- TODO: mark `@[simp]` once Mathlib removes coercions from morphism classes
lemma toEquiv_unitizationAddEquiv : (unitizationAddEquiv X R).toEquiv = unitizationEquiv X R := rfl

variable [Semiring S] [Module S R] [ContinuousConstSMul S R]

@[simp]
lemma unitizationEquiv_smul (s : S) (f : Unitization R C₀(X, R)) :
    unitizationEquiv X R (s • f) = s • unitizationEquiv X R f := by
  ext x; induction x using OnePoint.rec <;> simp

variable (X R S) in
/-- `ZeroAtInftyContinuousMap.unitizationEquiv` as a `LinearEquiv`. -/
def unitizationLinearEquiv : Unitization R C₀(X, R) ≃ₗ[S] C(OnePoint X, R) where
  __ := unitizationAddEquiv X R
  map_smul' := unitizationEquiv_smul

@[simp]
lemma coe_unitizationLinearEquiv : ⇑(unitizationLinearEquiv X R S) = unitizationEquiv X R := rfl

@[simp]
lemma coe_unitizationLinearEquiv_symm :
    ⇑(unitizationLinearEquiv X R S).symm = (unitizationEquiv X R).symm :=
  rfl

@[simp]
lemma toAddEquiv_unitizationLinearEquiv :
    (unitizationLinearEquiv X R S).toAddEquiv = unitizationAddEquiv X R :=
  rfl

end AddCommGroup

section CommRing

variable [CommRing R] [IsTopologicalRing R]

@[simp]
lemma unitizationEquiv_one : unitizationEquiv X R 1 = 1 := by
  ext x; induction x using OnePoint.rec <;> simp

@[simp]
lemma unitizationEquiv_mul (f g : Unitization R C₀(X, R)) :
    unitizationEquiv X R (f * g) = unitizationEquiv X R f * unitizationEquiv X R g := by
  ext x; induction x using OnePoint.rec <;> simp; ring

variable (X R) in
/-- `ZeroAtInftyContinuousMap.unitizationEquiv` as a `RingEquiv`. -/
def unitizationRingEquiv : Unitization R C₀(X, R) ≃+* C(OnePoint X, R) where
  toAddEquiv := unitizationAddEquiv X R
  map_mul' := unitizationEquiv_mul

@[simp]
lemma coe_unitizationRingEquiv : ⇑(unitizationRingEquiv X R) = unitizationEquiv X R := rfl

@[simp]
lemma coe_unitizationRingEquiv_symm :
    ⇑(unitizationRingEquiv X R).symm = (unitizationEquiv X R).symm := rfl

-- TODO: mark `@[simp]` once Mathlib removes coercions from morphism classes
lemma toAddEquiv_unitizationRingEquiv :
    (unitizationRingEquiv X R).toAddEquiv = unitizationAddEquiv X R := rfl

variable [CommSemiring S] [Algebra S R]

@[simp]
lemma unitizationEquiv_algebraMap (s : S) :
    unitizationEquiv X R (algebraMap _ _ s) = algebraMap _ _ s := by
  ext x; induction x using OnePoint.rec <;> simp [Algebra.algebraMap_eq_smul_one]

variable (X R S) in
/-- `ZeroAtInftyContinuousMap.unitizationEquiv` as an `AlgEquiv`. -/
def unitizationAlgEquiv : Unitization R C₀(X, R) ≃ₐ[S] C(OnePoint X, R) where
  toRingEquiv := unitizationRingEquiv X R
  commutes' := unitizationEquiv_algebraMap

@[simp]
lemma coe_unitizationAlgEquiv : ⇑(unitizationAlgEquiv X R S) = unitizationEquiv X R := rfl

@[simp]
lemma coe_unitizationAlgEquiv_symm :
    ⇑(unitizationAlgEquiv X R S).symm = (unitizationEquiv X R).symm :=
  rfl

@[simp]
lemma toRingEquiv_unitizationAlgEquiv :
    (unitizationAlgEquiv X R S).toRingEquiv = unitizationRingEquiv X R :=
  rfl

@[simp]
lemma toLinearEquiv_unitizationAlgEquiv :
    (unitizationAlgEquiv X R S).toLinearEquiv = unitizationLinearEquiv X R S :=
  rfl

variable [StarRing R] [ContinuousStar R]

variable (X R S) in
/-- `ZeroAtInftyContinuousMap.unitizationEquiv` as a `StarAlgEquiv`. -/
def unitizationStarAlgEquiv : Unitization R C₀(X, R) ≃⋆ₐ[S] C(OnePoint X, R) where
  toRingEquiv := unitizationRingEquiv X R
  map_smul' := unitizationEquiv_smul
  map_star' := unitizationEquiv_star

@[simp]
lemma coe_unitizationStarAlgEquiv : ⇑(unitizationStarAlgEquiv X R S) = unitizationEquiv X R := rfl

@[simp]
lemma coe_unitizationStarAlgEquiv_symm :
    ⇑(unitizationStarAlgEquiv X R S).symm = (unitizationEquiv X R).symm := rfl

@[simp]
lemma toAlgEquiv_unitizationStarAlgEquiv :
    (unitizationStarAlgEquiv X R S).toAlgEquiv = unitizationAlgEquiv X R S :=
  rfl

/-- `ZeroAtInftyContinuousMap.unitizationStarAlgEquiv` is the map obtained lifting
`ZeroAtInftyContinuousMap.toOnePoint` to the unitization. -/
lemma coe_starLift_toOnePointNonUnitalStarAlgHom :
    ⇑(starLift (toOnePointNonUnitalStarAlgHom X R R)) = unitizationEquiv X R :=
  rfl

end CommRing

end ZeroAtInftyContinuousMap
