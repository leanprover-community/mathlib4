/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Lifting monoid algebras

This file defines `liftNC`. For the definition of `MonoidAlgebra.lift`, see
`Mathlib/Algebra/MonoidAlgebra/Basic.lean`.

## Main results
* `MonoidAlgebra.liftNC`, `AddMonoidAlgebra.liftNC`: lift a homomorphism `f : k →+ R` and a
  function `g : G → R` to a homomorphism `MonoidAlgebra k G →+ R`.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/-- A non-commutative version of `MonoidAlgebra.lift`: given an additive homomorphism `f : k →+ R`
and a homomorphism `g : G → R`, returns the additive homomorphism from
`MonoidAlgebra k G` such that `liftNC f g (single a b) = f b * g a`. If `f` is a ring homomorphism
and the range of either `f` or `g` is in center of `R`, then the result is a ring homomorphism.  If
`R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra homomorphism called
`MonoidAlgebra.lift`. -/
def liftNC (f : k →+ R) (g : G → R) : MonoidAlgebra k G →+ R :=
  (liftAddHom fun x ↦ .comp (.mulRight (g x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
theorem liftNC_single (f : k →+ R) (g : G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g a :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Mul G] [Semiring R]

theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) (a b : MonoidAlgebra k G)
    (h_comm : ∀ {x y}, y ∈ a.coeff.support → Commute (f (b.coeff x)) (g y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [NonAssocSemiring R] [Semiring k] [One G]

@[simp]
theorem liftNC_one {g_hom : Type*} [FunLike g_hom G R] [OneHomClass g_hom G R]
    (f : k →+* R) (g : g_hom) :
    liftNC (f : k →+ R) g 1 = 1 := by simp [one_def]

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [Monoid G] [Semiring R] [Semiring S] [Semiring T] [Monoid M]

/-- `liftNC` as a `RingHom`, for when `f x` and `g y` commute -/
def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra k G →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
lemma liftNCRingHom_single (f : k →+* R) (g : G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings.

See also `RingEquiv.monoidAlgebraCongrLeft`. -/
noncomputable def mapRangeRingHom (f : R →+* S) : MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) fun x y ↦ by simp [commute_iff_eq]

@[simp]
lemma mapRangeRingHom_coeff_apply (f : R →+* S) (x : MonoidAlgebra R M) (m : M) :
    (mapRangeRingHom M f x).coeff m = f (x.coeff m) := by
  classical
  induction x using induction_linear
  · simp
  · simp [*]
  · simp [mapRangeRingHom, single_apply, apply_ite (f := f)]

@[simp]
lemma mapRangeRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom M f (single a b) = single a (f b) := by
  classical ext; simp [single_apply, apply_ite f]

@[simp] lemma mapRangeRingHom_id : mapRangeRingHom M (.id R) = .id (MonoidAlgebra R M) := by
  ext <;> simp

@[simp] lemma mapRangeRingHom_comp (f : S →+* T) (g : R →+* S) :
    mapRangeRingHom M (f.comp g) = (mapRangeRingHom M f).comp (mapRangeRingHom M g) := by
  ext <;> simp

end Semiring

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G}

section

variable [Semiring k] [NonUnitalNonAssocSemiring R]

/-- A non-commutative version of `AddMonoidAlgebra.lift`: given an additive homomorphism
`f : k →+ R` and a map `g : Multiplicative G → R`, returns the additive
homomorphism from `k[G]` such that `liftNC f g (single a b) = f b * g a`. If `f`
is a ring homomorphism and the range of either `f` or `g` is in center of `R`, then the result is a
ring homomorphism.  If `R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra
homomorphism called `AddMonoidAlgebra.lift`. -/
def liftNC (f : k →+ R) (g : Multiplicative G → R) : k[G] →+ R :=
  (liftAddHom fun x ↦ .comp (.mulRight (g <| .ofAdd x)) f).comp coeffAddEquiv.toAddMonoidHom

@[simp]
theorem liftNC_single (f : k →+ R) (g : Multiplicative G → R) (a : G) (b : k) :
    liftNC f g (single a b) = f b * g (Multiplicative.ofAdd a) :=
  liftAddHom_apply_single _ _ _

end

section Mul

variable [Semiring k] [Add G] [Semiring R]

theorem liftNC_mul {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [MulHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) (a b : k[G])
    (h_comm : ∀ {x y}, y ∈ a.coeff.support → Commute (f (b.coeff x)) (g <| .ofAdd y)) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_coeff_single a, ← sum_coeff_single b]
  simp_rw [mul_def, map_finsuppSum, liftNC_single, Finsupp.sum_mul, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x _hx => ?_
  simp [mul_assoc, (h_comm hy).left_comm]

end Mul

section One

variable [Semiring k] [Zero G] [NonAssocSemiring R]

@[simp]
theorem liftNC_one {g_hom : Type*}
    [FunLike g_hom (Multiplicative G) R] [OneHomClass g_hom (Multiplicative G) R]
    (f : k →+* R) (g : g_hom) : liftNC (f : k →+ R) g 1 = 1 :=
  MonoidAlgebra.liftNC_one f g

end One

/-! #### Semiring structure -/
section Semiring

variable [Semiring k] [AddMonoid G] [Semiring R] [Semiring S] [Semiring T] [AddMonoid M]

/-- `liftNC` as a `RingHom`, for when `f` and `g` commute -/
def liftNCRingHom (f : k →+* R) (g : Multiplicative G →* R) (h_comm : ∀ x y, Commute (f x) (g y)) :
    k[G] →+* R :=
  { liftNC (f : k →+ R) g with
    map_one' := liftNC_one _ _
    map_mul' := fun _a _b => liftNC_mul _ _ _ _ fun {_ _} _ => h_comm _ _ }

@[simp]
lemma liftNCRingHom_single (f : k →+* R) (g : Multiplicative G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g (.ofAdd a) :=
  liftNC_single _ _ _ _

variable (M) in
/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings.

See also `RingEquiv.addMonoidAlgebraCongrLeft`. -/
noncomputable def mapRangeRingHom (f : R →+* S) : R[M] →+* S[M] :=
  liftNCRingHom (singleZeroRingHom.comp f) (of S M) fun x y ↦ by simp [commute_iff_eq]

@[simp]
lemma mapRangeRingHom_coeff_apply (f : R →+* S) (x : R[M]) (m : M) :
    (mapRangeRingHom M f x).coeff m = f (x.coeff m) := by
  classical
  induction x using induction_linear
  · simp
  · simp [*]
  · simp [mapRangeRingHom, single_apply, apply_ite (f := f)]

@[simp]
lemma mapRangeRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom M f (single a b) = single a (f b) := by
  classical ext; simp [single_apply, apply_ite f]

@[simp] lemma mapRangeRingHom_id : mapRangeRingHom M (.id R) = .id (R[M]) := by
  ext <;> simp

@[simp] lemma mapRangeRingHom_comp (f : S →+* T) (g : R →+* S) :
    mapRangeRingHom M (f.comp g) = (mapRangeRingHom M f).comp (mapRangeRingHom M g) := by
  ext <;> simp

-- `MonoidAlgebra.of` doesn't translate with `to_additive`, so instead
-- we have to tag these declarations with `to_additive existing`
set_option linter.existingAttributeWarning false in
attribute [to_additive existing]
  MonoidAlgebra.mapRangeRingHom MonoidAlgebra.mapRangeRingHom_coeff_apply
  MonoidAlgebra.mapRangeRingHom_single MonoidAlgebra.mapRangeRingHom_id
  MonoidAlgebra.mapRangeRingHom_comp

end Semiring

end AddMonoidAlgebra
