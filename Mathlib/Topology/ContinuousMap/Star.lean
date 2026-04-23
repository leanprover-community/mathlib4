/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Topology.Algebra.Star
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Star structures on continuous maps.

-/

@[expose] public section

namespace ContinuousMap

/-!
### Star structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/


section StarStructure

variable {R α β : Type*}
variable [TopologicalSpace α] [TopologicalSpace β]

section Star

variable [Star β] [ContinuousStar β]

instance : Star C(α, β) where star f := starContinuousMap.comp f

@[simp]
theorem coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

@[simp]
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl

instance instTrivialStar [TrivialStar β] : TrivialStar C(α, β) where
  star_trivial _ := ext fun _ => star_trivial _

end Star

instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β) where
  star_involutive _ := ext fun _ => star_star _

instance starAddMonoid [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where
  star_add _ _ := ext fun _ => star_add _ _

instance starMul [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β] :
    StarMul C(α, β) where
  star_mul _ _ := ext fun _ => star_mul _ _

instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }

instance [Star R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
    [ContinuousConstSMul R β] : StarModule R C(α, β) where
  star_smul _ _ := ext fun _ => star_smul _ _

end StarStructure

section Precomposition

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]

/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `ContinuousMap.compMonoidHom'` and
`ContinuousMap.compAddMonoidHom'`, `ContinuousMap.compRightAlgHom` for bundlings of
pre-composition into a `MonoidHom`, an `AddMonoidHom` and an `AlgHom`, respectively, under
suitable assumptions on `A`. -/
@[simps]
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- `ContinuousMap.compStarAlgHom'` sends the identity continuous map to the identity
`StarAlgHom` -/
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

/-- `ContinuousMap.compStarAlgHom'` is functorial. -/
theorem compStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compStarAlgHom' 𝕜 A (g.comp f) = (compStarAlgHom' 𝕜 A f).comp (compStarAlgHom' 𝕜 A g) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl

end Precomposition

section Postcomposition

variable (X : Type*) {𝕜 A B C : Type*} [TopologicalSpace X] [CommSemiring 𝕜]
variable [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]
variable [TopologicalSpace B] [Semiring B] [IsTopologicalSemiring B] [Star B]
variable [ContinuousStar B] [Algebra 𝕜 B]
variable [TopologicalSpace C] [Semiring C] [IsTopologicalSemiring C] [Star C]
variable [ContinuousStar C] [Algebra 𝕜 C]

/-- Post-composition with a continuous star algebra homomorphism is a star algebra homomorphism
between spaces of continuous maps. -/
@[simps]
def compStarAlgHom (φ : A →⋆ₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) →⋆ₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_star φ (f x)

/-- `ContinuousMap.compStarAlgHom` sends the identity `StarAlgHom` on `A` to the identity
`StarAlgHom` on `C(X, A)`. -/
lemma compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) := rfl

/-- `ContinuousMap.compStarAlgHom` is functorial. -/
lemma compStarAlgHom_comp (φ : A →⋆ₐ[𝕜] B) (ψ : B →⋆ₐ[𝕜] C) (hφ : Continuous φ)
    (hψ : Continuous ψ) : compStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compStarAlgHom X ψ hψ).comp (compStarAlgHom X φ hφ) :=
  rfl

end Postcomposition

end ContinuousMap

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [IsTopologicalSemiring A] [StarRing A]
variable [ContinuousStar A] [Algebra 𝕜 A]

/-- `ContinuousMap.compStarAlgHom'` as a `StarAlgEquiv` when the continuous map `f` is
actually a homeomorphism. -/
@[simps]
def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  { (f : C(X, Y)).compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_toContinuousMap, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul ((f : C(X, Y)).compStarAlgHom' 𝕜 A) k a }

end Homeomorph

/-! ### Evaluation as a bundled map -/

variable {X : Type*} (S R : Type*) [TopologicalSpace X] [CommSemiring S] [CommSemiring R]
variable [Algebra S R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Evaluation of continuous maps at a point, bundled as a star algebra homomorphism. -/
@[simps!]
def ContinuousMap.evalStarAlgHom [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) →⋆ₐ[S] R :=
  { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }
