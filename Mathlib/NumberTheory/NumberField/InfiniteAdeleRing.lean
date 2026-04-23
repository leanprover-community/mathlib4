/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.NhdsWithin

/-!
# The infinite adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places.

## Main definitions

- `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
  the completions of `K` over its infinite places.
- `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` is the ring isomorphism between
  the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of `K`.

## Main results
- `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

@[expose] public section

noncomputable section

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

/-! ## The infinite adele ring

The infinite adele ring is the finite product of completions of a number field over its
infinite places. See `NumberField.InfinitePlace` for the definition of an infinite place and
`NumberField.InfinitePlace.Completion` for the associated completion.
-/

/-- The infinite adele ring of a number field. -/
def InfiniteAdeleRing (K : Type*) [Field K] := (v : InfinitePlace K) → v.Completion
deriving CommRing, Inhabited, TopologicalSpace, IsTopologicalRing, Algebra K

namespace InfiniteAdeleRing

variable (K : Type*) [Field K]

instance [NumberField K] : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstance : Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

@[simp]
theorem algebraMap_apply (x : K) (v : InfinitePlace K) :
    algebraMap K (InfiniteAdeleRing K) x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

open scoped Classical in
/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
abbrev ringEquiv_mixedSpace :
    InfiniteAdeleRing K ≃+* mixedEmbedding.mixedSpace K :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.Completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.ringEquivRealOfIsReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.ringEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem ringEquiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    ringEquiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => extensionEmbeddingOfIsReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => extensionEmbedding v.1 (x v)) := rfl

/-- Transfers the embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_algebraMap_comp {x : K} :
    mixedEmbedding K x = ringEquiv_mixedSpace K (algebraMap K _ x) := by
  ext v <;> simp

/--
*Weak approximation for the infinite adele ring*

The number field $K$ is dense in the infinite adele ring $\prod_v K_v$.
-/
theorem denseRange_algebraMap [NumberField K] : DenseRange <| algebraMap K (InfiniteAdeleRing K) :=
  (DenseRange.piMap fun _ => UniformSpace.Completion.denseRange_coe).comp
    (InfinitePlace.denseRange_algebraMap_pi K)
      (.piMap fun _ => UniformSpace.Completion.continuous_coe _)

/-- The norm on the infinite adele ring is given by the product of the normalized norms
across infinite places. The normalized norm is the real norm at real places and the
square of the complex norm at complex places. -/
instance [NumberField K] : Norm (InfiniteAdeleRing K) where
  norm x := ∏ v, ‖x v‖ ^ v.mult

variable {K}

theorem norm_def [NumberField K] (x : InfiniteAdeleRing K) :
    ‖x‖ = ∏ v, ‖x v‖ ^ v.mult := rfl

set_option backward.isDefEq.respectTransparency false in
theorem norm_eq_zero_of_not_isUnit [NumberField K] {x : InfiniteAdeleRing K} (hx : ¬IsUnit x) :
    ‖x‖ = 0 := by
  rw [Pi.isUnit_iff, not_forall] at hx
  obtain ⟨v, hv⟩ := hx
  exact Finset.prod_eq_zero_iff.2 ⟨v, Finset.mem_univ v, by simpa [isUnit_iff_ne_zero] using hv⟩

/-- The product formula for the infinite adele ring. This is the adelic version of
`NumberField.InfinitePlace.prod_eq_abs_norm`. -/
theorem coe_norm_eq_abs_norm [NumberField K] (x : K) :
    ‖algebraMap K (InfiniteAdeleRing K) x‖ = |Algebra.norm ℚ x| := by
  simpa [-Rat.cast_abs, norm_def] using InfinitePlace.prod_eq_abs_norm x

end InfiniteAdeleRing

end NumberField
