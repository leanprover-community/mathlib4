/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Continuous linear equivalences

## Notation
Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.

## Main Definitions
* `piCongrLeft`: `Equiv.piCongrLeft` as a continuous linear equivalence.
* `sumPiEquivProdPi`: `Equiv.sumPiEquivProdPi` as a continuous linear equivalence.
* `piUnique`: `Equiv.piUnique` as a continuous linear equivalence.
* `sumPiEquivProdPi`: `Equiv.sumPiEquivProdPi` as a continuous linear equivalence.
* `Fin.consEquivL`: `Fin.consEquiv` as a continuous linear equivalence.
* `ContinuousLinearMap.finCons`: `Fin.cons` in the codomain of continuous linear maps.

## Main Results
-/

@[expose] public section

namespace ContinuousLinearMap

variable (R : Type*) [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} (φ : ι → Type*)
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, (proj i : (∀ i, φ i) →L[R] φ i).ker : Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      Continuous.comp (continuous_apply (A := φ) i) <| continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R]

section Pi

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.
This is `Equiv.piCongrLeft` as a `ContinuousLinearEquiv`.
-/
def piCongrLeft {ι ι' : Type*}
    (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃L[R] (i : ι) → φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

/-- The product over `S ⊕ T` of a family of topological modules
is isomorphic (topologically and algebraically) to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `ContinuousLinearEquiv`.
-/
def sumPiEquivProdPi (S T : Type*)
    (A : S ⊕ T → Type*) [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
    [∀ st, TopologicalSpace (A st)] :
    ((st : S ⊕ T) → A st) ≃L[R] ((s : S) → A (Sum.inl s)) × ((t : T) → A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

/-- The product `Π t : α, f t` of a family of topological modules is isomorphic
(both topologically and algebraically) to the space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `ContinuousLinearEquiv`.
-/
@[simps! -fullyApplied]
def piUnique {α : Type*} [Unique α] (f : α → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃L[R] f default where
  __ := LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

end Pi

section piCongrRight

variable {R} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)]
  [∀ i, Module R (N i)] (f : (i : ι) → M i ≃L[R] N i)

/-- Combine a family of continuous linear equivalences into a continuous linear equivalence of
pi-types. -/
def piCongrRight : ((i : ι) → M i) ≃L[R] (i : ι) → N i where
  __ := LinearEquiv.piCongrRight fun i ↦ (f i).toLinearEquiv

@[simp]
theorem piCongrRight_apply (m : (i : ι) → M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem piCongrRight_symm_apply (n : (i : ι) → N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

section Pi

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/-- Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`.
-/
@[simps! -fullyApplied apply symm_apply]
def piFinTwo (M : Fin 2 → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : ((i : _) → M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied apply symm_apply]
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

section
variable {n : ℕ} {R} {M : Fin n.succ → Type*} {N : Type*}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

set_option backward.defeqAttrib.useBackward true in
variable (R M) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps!]
def _root_.Fin.consEquivL : (M 0 × Π i, M (Fin.succ i)) ≃L[R] (Π i, M i) where
  __ := Fin.consLinearEquiv R M

/-- `Fin.cons` in the codomain of continuous linear maps. -/
abbrev _root_.ContinuousLinearMap.finCons
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : N →L[R] M 0) (fs : N →L[R] Π i, M (Fin.succ i)) :
    N →L[R] Π i, M i :=
  Fin.consEquivL R M ∘L f.prod fs

end

end Pi

end ContinuousLinearEquiv
