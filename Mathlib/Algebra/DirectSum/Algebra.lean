/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Ring

#align_import algebra.direct_sum.algebra from "leanprover-community/mathlib"@"e5ba338e9ae4e7feae5027fd5198850971f0fa6a"

/-! # Additively-graded algebra structures on `⨁ i, A i`

This file provides `R`-algebra structures on external direct sums of `R`-modules.

Recall that if `A i` are a family of `AddCommMonoid`s indexed by an `AddMonoid`, then an instance
of `DirectSum.GMonoid A` is a multiplication `A i → A j → A (i + j)` giving `⨁ i, A i` the
structure of a semiring. In this file, we introduce the `DirectSum.GAlgebra R A` class for the case
where all `A i` are `R`-modules. This is the extra structure needed to promote `⨁ i, A i` to an
`R`-algebra.

## Main definitions

* `DirectSum.GAlgebra R A`, the typeclass.
* `DirectSum.toAlgebra` extends `DirectSum.toSemiring` to produce an `AlgHom`.

-/


universe uι uR uA uB

variable {ι : Type uι}

namespace DirectSum

open DirectSum

variable (R : Type uR) (A : ι → Type uA) {B : Type uB} [DecidableEq ι]

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

section

/-- A graded version of `Algebra`. An instance of `DirectSum.GAlgebra R A` endows `(⨁ i, A i)`
with an `R`-algebra structure. -/
class GAlgebra where
  toFun : R →+ A 0
  map_one : toFun 1 = GradedMonoid.GOne.one
  map_mul :
    ∀ r s, GradedMonoid.mk _ (toFun (r * s)) = ⟨_, GradedMonoid.GMul.mul (toFun r) (toFun s)⟩
  commutes : ∀ r x, GradedMonoid.mk _ (toFun r) * x = x * ⟨_, toFun r⟩
  smul_def : ∀ (r) (x : GradedMonoid A), GradedMonoid.mk x.1 (r • x.2) = ⟨_, toFun r⟩ * x
#align direct_sum.galgebra DirectSum.GAlgebra

end

variable [Semiring B] [GAlgebra R A] [Algebra R B]

instance : Algebra R (⨁ i, A i) where
  toFun := (DirectSum.of A 0).comp GAlgebra.toFun
  map_zero' := AddMonoidHom.map_zero _
  map_add' := AddMonoidHom.map_add _
  map_one' := (DirectSum.of A 0).congr_arg GAlgebra.map_one
  map_mul' a b := by
    simp only [AddMonoidHom.comp_apply]
    -- ⊢ ↑(of A 0) (↑GAlgebra.toFun (a * b)) = ↑(of A 0) (↑GAlgebra.toFun a) * ↑(of A …
    rw [of_mul_of]
    -- ⊢ ↑(of A 0) (↑GAlgebra.toFun (a * b)) = ↑(of A (0 + 0)) (GradedMonoid.GMul.mul …
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.map_mul a b)
    -- 🎉 no goals
  commutes' r x := by
    change AddMonoidHom.mul (DirectSum.of _ _ _) x = AddMonoidHom.mul.flip (DirectSum.of _ _ _) x
    -- ⊢ ↑(↑AddMonoidHom.mul (↑(of (fun i => A i) 0) (↑GAlgebra.toFun r))) x = ↑(↑(Ad …
    apply FunLike.congr_fun _ x
    -- ⊢ ↑AddMonoidHom.mul (↑(of (fun i => A i) 0) (↑GAlgebra.toFun r)) = ↑(AddMonoid …
    ext i xi : 2
    -- ⊢ ↑(AddMonoidHom.comp (↑AddMonoidHom.mul (↑(of (fun i => A i) 0) (↑GAlgebra.to …
    dsimp only [AddMonoidHom.comp_apply, AddMonoidHom.mul_apply, AddMonoidHom.flip_apply]
    -- ⊢ ↑(of (fun i => A i) 0) (↑GAlgebra.toFun r) * ↑(of (fun i => A i) i) xi = ↑(o …
    rw [of_mul_of, of_mul_of]
    -- ⊢ ↑(of (fun i => A i) (0 + i)) (GradedMonoid.GMul.mul (↑GAlgebra.toFun r) xi)  …
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.commutes r ⟨i, xi⟩)
    -- 🎉 no goals
  smul_def' r x := by
    change DistribMulAction.toAddMonoidHom _ r x = AddMonoidHom.mul (DirectSum.of _ _ _) x
    -- ⊢ ↑(DistribMulAction.toAddMonoidHom ((fun x => ⨁ (i : ι), A i) r) r) x = ↑(↑Ad …
    apply FunLike.congr_fun _ x
    -- ⊢ DistribMulAction.toAddMonoidHom ((fun x => ⨁ (i : ι), A i) r) r = ↑AddMonoid …
    ext i xi : 2
    -- ⊢ ↑(AddMonoidHom.comp (DistribMulAction.toAddMonoidHom ((fun x => ⨁ (i : ι), A …
    dsimp only [AddMonoidHom.comp_apply, DistribMulAction.toAddMonoidHom_apply,
      AddMonoidHom.mul_apply]
    rw [DirectSum.of_mul_of, ← of_smul]
    -- ⊢ ↑(of (fun i => A i) i) (r • xi) = ↑(of (fun i => A i) (0 + i)) (GradedMonoid …
    apply DFinsupp.single_eq_of_sigma_eq (GAlgebra.smul_def r ⟨i, xi⟩)
    -- 🎉 no goals

theorem algebraMap_apply (r : R) :
    algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (GAlgebra.toFun r) :=
  rfl
#align direct_sum.algebra_map_apply DirectSum.algebraMap_apply

theorem algebraMap_toAddMonoid_hom :
    ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 0).comp (GAlgebra.toFun : R →+ A 0) :=
  rfl
#align direct_sum.algebra_map_to_add_monoid_hom DirectSum.algebraMap_toAddMonoid_hom

/-- A family of `LinearMap`s preserving `DirectSum.GOne.one` and `DirectSum.GMul.mul`
describes an `AlgHom` on `⨁ i, A i`. This is a stronger version of `DirectSum.toSemiring`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `Submodule.subtype (A i)`, and the `[GMonoid A]` structure originates from
`DirectSum.GMonoid.ofAddSubmodules`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
def toAlgebra (f : ∀ i, A i →ₗ[R] B) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj)
    (hcommutes : ∀ r, (f 0) (GAlgebra.toFun r) = (algebraMap R B) r) : (⨁ i, A i) →ₐ[R] B :=
  { toSemiring (fun i => (f i).toAddMonoidHom) hone
      @hmul with
    toFun := toSemiring (fun i => (f i).toAddMonoidHom) hone @hmul
    commutes' := fun r => (DirectSum.toSemiring_of _ hone hmul _ _).trans (hcommutes r) }
#align direct_sum.to_algebra DirectSum.toAlgebra

/-- Two `AlgHom`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem algHom_ext' ⦃f g : (⨁ i, A i) →ₐ[R] B⦄
    (h : ∀ i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f = g :=
  AlgHom.toLinearMap_injective <| DirectSum.linearMap_ext _ h
#align direct_sum.alg_hom_ext' DirectSum.algHom_ext'

theorem algHom_ext ⦃f g : (⨁ i, A i) →ₐ[R] B⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) : f = g :=
  algHom_ext' R A fun i => LinearMap.ext <| h i
#align direct_sum.alg_hom_ext DirectSum.algHom_ext

end DirectSum

/-! ### Concrete instances -/


/-- A direct sum of copies of an `Algebra` inherits the algebra structure.

-/
@[simps]
instance Algebra.directSumGAlgebra {R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
    [Semiring A] [Algebra R A] : DirectSum.GAlgebra R fun _ : ι => A where
  toFun := (algebraMap R A).toAddMonoidHom
  map_one := (algebraMap R A).map_one
  map_mul a b := Sigma.ext (zero_add _).symm (heq_of_eq <| (algebraMap R A).map_mul a b)
  commutes := fun _ ⟨_, _⟩ =>
    Sigma.ext ((zero_add _).trans (add_zero _).symm) (heq_of_eq <| Algebra.commutes _ _)
  smul_def := fun _ ⟨_, _⟩ => Sigma.ext (zero_add _).symm (heq_of_eq <| Algebra.smul_def _ _)
#align algebra.direct_sum_galgebra Algebra.directSumGAlgebra
