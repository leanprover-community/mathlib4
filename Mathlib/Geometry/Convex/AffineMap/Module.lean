/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.AffineMap.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.Module

/-!
# The module of affine maps into a module

This file shows that the affine maps from a convex space `X` to a module `M` themselves form a
module, and that the convex space structure this induces is the pointwise one.

## Main declarations

* `Convexity.ConvexSpace.AffineMap.instModule`: The affine maps from a convex space to a module
  form a module.
* `Convexity.ConvexSpace.AffineMap.instIsModuleConvexSpace`: The pointwise convex space structure
  on the affine maps into a module is given by weighted sums.
-/

public noncomputable section

namespace Convexity
variable {R S X M : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

namespace ConvexSpace.AffineMap
variable [ConvexSpace R X]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M]

instance : Zero (ConvexSpace.AffineMap R X M) := ⟨.const 0⟩

omit [Module R M] [IsModuleConvexSpace R M] in
@[simp, norm_cast]
lemma coe_zero : ⇑(0 : ConvexSpace.AffineMap R X M) = 0 := rfl

omit [Module R M] [IsModuleConvexSpace R M] in
@[simp] lemma zero_apply (x : X) : (0 : ConvexSpace.AffineMap R X M) x = 0 := rfl

instance : Add (ConvexSpace.AffineMap R X M) where
  add f g := ⟨f + g, f.isAffineMap.add g.isAffineMap⟩

@[simp, norm_cast]
lemma coe_add (f g : ConvexSpace.AffineMap R X M) : ⇑(f + g) = ⇑f + ⇑g := rfl

@[simp]
lemma add_apply (f g : ConvexSpace.AffineMap R X M) (x : X) : (f + g) x = f x + g x := rfl

section SMul
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

instance : SMul S (ConvexSpace.AffineMap R X M) where smul s f := ⟨s • f, by fun_prop⟩

@[simp, norm_cast]
lemma coe_smul (s : S) (f : ConvexSpace.AffineMap R X M) : ⇑(s • f) = s • ⇑f := rfl

@[simp]
lemma smul_apply (s : S) (f : ConvexSpace.AffineMap R X M) (x : X) : (s • f) x = s • f x := rfl

end SMul

instance instAddCommMonoid : AddCommMonoid (ConvexSpace.AffineMap R X M) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ ↦ rfl

variable (R X M) in
/-- The coercion of a bundled affine map to a function, as an additive monoid hom. -/
@[expose, simps]
def coeAddMonoidHom : ConvexSpace.AffineMap R X M →+ (X → M) where
  toFun f := f
  map_zero' := coe_zero
  map_add' := coe_add

@[simp, norm_cast]
lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ConvexSpace.AffineMap R X M) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := map_sum (coeAddMonoidHom R X M) ..

@[simp]
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → ConvexSpace.AffineMap R X M) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by rw [coe_sum, Finset.sum_apply]

instance [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] :
    DistribMulAction S (ConvexSpace.AffineMap R X M) :=
  fast_instance% DFunLike.coe_injective.distribMulAction (coeAddMonoidHom R X M) fun _ _ ↦ rfl

instance instModule [Semiring S] [Module S M] [SMulCommClass R S M] :
    Module S (ConvexSpace.AffineMap R X M) :=
  fast_instance% DFunLike.coe_injective.module S (coeAddMonoidHom R X M) fun _ _ ↦ rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M]

instance : Neg (ConvexSpace.AffineMap R X M) where
  neg f := ⟨-f, f.isAffineMap.neg⟩

@[simp, norm_cast]
lemma coe_neg (f : ConvexSpace.AffineMap R X M) : ⇑(-f) = -⇑f := rfl

@[simp] lemma neg_apply (f : ConvexSpace.AffineMap R X M) (x : X) : (-f) x = -f x := rfl

instance : Sub (ConvexSpace.AffineMap R X M) where
  sub f g := ⟨f - g, f.isAffineMap.sub g.isAffineMap⟩

@[simp, norm_cast]
lemma coe_sub (f g : ConvexSpace.AffineMap R X M) : ⇑(f - g) = ⇑f - ⇑g := rfl

@[simp]
lemma sub_apply (f g : ConvexSpace.AffineMap R X M) (x : X) : (f - g) x = f x - g x := rfl

instance instAddCommGroup : AddCommGroup (ConvexSpace.AffineMap R X M) :=
  fast_instance% DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end AddCommGroup
end ConvexSpace.AffineMap

/-! ### Compatibility with the pointwise convex space structure -/

section CommSemiring
variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [AddCommMonoid M] [Module R M] [ConvexSpace R M] [IsModuleConvexSpace R M]

instance ConvexSpace.AffineMap.instIsModuleConvexSpace :
    IsModuleConvexSpace R (ConvexSpace.AffineMap R X M) where
  sConvexComb_eq_sum w := by ext x; simp [Finsupp.sum]

end CommSemiring
end Convexity
