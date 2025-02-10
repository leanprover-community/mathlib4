/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# MonoidAlgebra.mapDomain

-/

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single mapDomain

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

abbrev mapDomain {G' : Type*} (f : G → G') (v : MonoidAlgebra k G) : MonoidAlgebra k G' :=
  Finsupp.mapDomain f v

theorem mapDomain_sum {k' G' : Type*} [Semiring k'] {f : G → G'} {s : MonoidAlgebra k' G}
    {v : G → k' → MonoidAlgebra k G} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  Finsupp.mapDomain_sum

end


section MiscTheorems

variable [Semiring k]

section

/-- Like `Finsupp.mapDomain_zero`, but for the `1` we define in this file -/
@[simp]
theorem mapDomain_one {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [One α] [One α₂]
    {F : Type*} [FunLike F α α₂] [OneHomClass F α α₂] (f : F) :
    (mapDomain f (1 : MonoidAlgebra β α) : MonoidAlgebra β α₂) = (1 : MonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_one]

/-- Like `Finsupp.mapDomain_add`, but for the convolutive multiplication we define in this file -/
theorem mapDomain_mul {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Mul α] [Mul α₂]
    {F : Type*} [FunLike F α α₂] [MulHomClass F α α₂] (f : F) (x y : MonoidAlgebra β α) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp_rw [mul_def, mapDomain_sum, mapDomain_single, map_mul]
  rw [Finsupp.sum_mapDomain_index]
  · congr
    ext a b
    rw [Finsupp.sum_mapDomain_index]
    · simp
    · simp [mul_add]
  · simp
  · simp [add_mul]

end

end MiscTheorems

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[simps]
def mapDomainRingHom (k : Type*) {H F : Type*} [Semiring k] [Monoid G] [Monoid H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F) : MonoidAlgebra k G →+* MonoidAlgebra k H :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

abbrev mapDomain {G' : Type*} (f : G → G') (v : k[G]) : k[G'] :=
  Finsupp.mapDomain f v

theorem mapDomain_sum {k' G' : Type*} [Semiring k'] {f : G → G'} {s : AddMonoidAlgebra k' G}
    {v : G → k' → k[G]} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  Finsupp.mapDomain_sum

theorem mapDomain_single {G' : Type*} {f : G → G'} {a : G} {b : k} :
    mapDomain f (single a b) = single (f a) b :=
  Finsupp.mapDomain_single

end

section MiscTheorems

variable [Semiring k]

/-- Like `Finsupp.mapDomain_zero`, but for the `1` we define in this file -/
@[simp]
theorem mapDomain_one {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Zero α] [Zero α₂]
    {F : Type*} [FunLike F α α₂] [ZeroHomClass F α α₂] (f : F) :
    (mapDomain f (1 : AddMonoidAlgebra β α) : AddMonoidAlgebra β α₂) =
      (1 : AddMonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_zero]

/-- Like `Finsupp.mapDomain_add`, but for the convolutive multiplication we define in this file -/
theorem mapDomain_mul {α : Type*} {β : Type*} {α₂ : Type*} [Semiring β] [Add α] [Add α₂]
    {F : Type*} [FunLike F α α₂] [AddHomClass F α α₂] (f : F) (x y : AddMonoidAlgebra β α) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp_rw [mul_def, mapDomain_sum, mapDomain_single, map_add]
  rw [Finsupp.sum_mapDomain_index]
  · congr
    ext a b
    rw [Finsupp.sum_mapDomain_index]
    · simp
    · simp [mul_add]
  · simp
  · simp [add_mul]

/-- If `f : G → H` is an additive homomorphism between two additive monoids, then
`Finsupp.mapDomain f` is a ring homomorphism between their add monoid algebras. -/
@[simps]
def mapDomainRingHom (k : Type*) [Semiring k] {H F : Type*} [AddMonoid G] [AddMonoid H]
    [FunLike F G H] [AddMonoidHomClass F G H] (f : F) : k[G] →+* k[H] :=
  { (Finsupp.mapDomain.addMonoidHom f : MonoidAlgebra k G →+ MonoidAlgebra k H) with
    map_one' := mapDomain_one f
    map_mul' := fun x y => mapDomain_mul f x y }

end MiscTheorems

end AddMonoidAlgebra

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`

We have not defined `k[G] = MonoidAlgebra k (Multiplicative G)`
because historically this caused problems;
since the changes that have made `nsmul` definitional, this would be possible,
but for now we just construct the ring isomorphisms using `RingEquiv.refl _`.
-/


/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
protected def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) :=
  { Finsupp.domCongr
      Multiplicative.ofAdd with
    toFun := equivMapDomain Multiplicative.ofAdd
    map_mul' := fun x y => by
      -- Porting note: added `dsimp only`; `beta_reduce` alone is not sufficient
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Multiplicative.ofAdd]
      exact MonoidAlgebra.mapDomain_mul (α := Multiplicative G) (β := k)
        (MulHom.id (Multiplicative G)) x y }

/-- The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Additive` -/
protected def MonoidAlgebra.toAdditive [Semiring k] [Mul G] :
    MonoidAlgebra k G ≃+* AddMonoidAlgebra k (Additive G) :=
  { Finsupp.domCongr Additive.ofMul with
    toFun := equivMapDomain Additive.ofMul
    map_mul' := fun x y => by
      -- Porting note: added `dsimp only`; `beta_reduce` alone is not sufficient
      dsimp only
      repeat' rw [equivMapDomain_eq_mapDomain (M := k)]
      dsimp [Additive.ofMul]
      convert MonoidAlgebra.mapDomain_mul (β := k) (MulHom.id G) x y }
