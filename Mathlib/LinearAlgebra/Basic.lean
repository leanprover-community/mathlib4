/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Data.Set.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `Module`, `Submodule`, and `LinearMap`, are found in
`Algebra/Module`.

## Main definitions

* Many constructors for (semi)linear maps

See `LinearAlgebra.Span` for the span of a set (as a submodule),
and `LinearAlgebra.Quotient` for quotients by submodules.

## Main theorems

See `LinearAlgebra.Isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`LinearMap.prod`, `LinearMap.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/

open Function

open Pointwise

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} {R₄ : Type*}
variable {S : Type*}
variable {K : Type*} {K₂ : Type*}
variable {M : Type*} {M' : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} {M₄ : Type*}
variable {N : Type*} {N₂ : Type*}
variable {ι : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/

namespace IsLinearMap

theorem isLinearMap_add [Semiring R] [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel -- Porting Note: was cc
  · intro x y
    simp [smul_add]
#align is_linear_map.is_linear_map_add IsLinearMap.isLinearMap_add

theorem isLinearMap_sub {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · intro x y
    -- porting note (#10745): was `simp [add_comm, add_left_comm, sub_eq_add_neg]`
    rw [Prod.fst_add, Prod.snd_add]
    abel
  · intro x y
    simp [smul_sub]
#align is_linear_map.is_linear_map_sub IsLinearMap.isLinearMap_sub

end IsLinearMap

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoid

section Subsingleton

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

section Module

variable [Subsingleton M] [Subsingleton M₂]

/-- Between two zero modules, the zero map is an equivalence. -/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M →ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

-- Even though these are implied by `Subsingleton.elim` via the `Unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
@[simp]
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl
#align linear_equiv.zero_symm LinearEquiv.zero_symm

@[simp]
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align linear_equiv.coe_zero LinearEquiv.coe_zero

theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl
#align linear_equiv.zero_apply LinearEquiv.zero_apply

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0


end Module

instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance
#align linear_equiv.unique_of_subsingleton LinearEquiv.uniqueOfSubsingleton

end Subsingleton

#align linear_equiv.map_sum map_sumₓ

section Uncurry

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
protected def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ => by
      ext
      rfl
    map_smul' := fun _ _ => by
      ext
      rfl }
#align linear_equiv.curry LinearEquiv.curry

@[simp]
theorem coe_curry : ⇑(LinearEquiv.curry R V V₂) = curry :=
  rfl
#align linear_equiv.coe_curry LinearEquiv.coe_curry

@[simp]
theorem coe_curry_symm : ⇑(LinearEquiv.curry R V V₂).symm = uncurry :=
  rfl
#align linear_equiv.coe_curry_symm LinearEquiv.coe_curry_symm

end Uncurry

section

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ →+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃)
variable (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)
variable (p q : Submodule R M)

/-- Linear equivalence between two equal submodules. -/
def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equiv.Set.ofEq (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align linear_equiv.of_eq LinearEquiv.ofEq

variable {p q}

@[simp]
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x :=
  rfl
#align linear_equiv.coe_of_eq_apply LinearEquiv.coe_ofEq_apply

@[simp]
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl
#align linear_equiv.of_eq_symm LinearEquiv.ofEq_symm

@[simp]
theorem ofEq_rfl : ofEq p p rfl = LinearEquiv.refl R p := by ext; rfl
#align linear_equiv.of_eq_rfl LinearEquiv.ofEq_rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)
#align linear_equiv.of_submodules LinearEquiv.ofSubmodules

@[simp]
theorem ofSubmodules_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q) (x : p) :
    ↑(e.ofSubmodules p q h x) = e x :=
  rfl
#align linear_equiv.of_submodules_apply LinearEquiv.ofSubmodules_apply

@[simp]
theorem ofSubmodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q)
    (x : q) : ↑((e.ofSubmodules p q h).symm x) = e.symm x :=
  rfl
#align linear_equiv.of_submodules_symm_apply LinearEquiv.ofSubmodules_symm_apply

/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.

This is `LinearEquiv.ofSubmodule` but with `comap` on the left instead of `map` on the right. -/
def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ f.symm.map_eq_comap).symm
#align linear_equiv.of_submodule' LinearEquiv.ofSubmodule'

theorem ofSubmodule'_toLinearMap [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toLinearMap = (f.toLinearMap.domRestrict _).codRestrict _ Subtype.prop := by
  ext
  rfl
#align linear_equiv.of_submodule'_to_linear_map LinearEquiv.ofSubmodule'_toLinearMap

@[simp]
theorem ofSubmodule'_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) : (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl
#align linear_equiv.of_submodule'_apply LinearEquiv.ofSubmodule'_apply

@[simp]
theorem ofSubmodule'_symm_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) (x : U) : ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) :=
  rfl
#align linear_equiv.of_submodule'_symm_apply LinearEquiv.ofSubmodule'_symm_apply

variable (p)

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
#align linear_equiv.of_top LinearEquiv.ofTop

@[simp]
theorem ofTop_apply {h} (x : p) : ofTop p h x = x :=
  rfl
#align linear_equiv.of_top_apply LinearEquiv.ofTop_apply

@[simp]
theorem coe_ofTop_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x :=
  rfl
#align linear_equiv.coe_of_top_symm_apply LinearEquiv.coe_ofTop_symm_apply

theorem ofTop_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩ :=
  rfl
#align linear_equiv.of_top_symm_apply LinearEquiv.ofTop_symm_apply

/-- If a linear map has an inverse, it is a linear equivalence. -/
def ofLinear (h₁ : f.comp g = LinearMap.id) (h₂ : g.comp f = LinearMap.id) : M ≃ₛₗ[σ₁₂] M₂ :=
  { f with
    invFun := g
    left_inv := LinearMap.ext_iff.1 h₂
    right_inv := LinearMap.ext_iff.1 h₁ }
#align linear_equiv.of_linear LinearEquiv.ofLinear

@[simp]
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl
#align linear_equiv.of_linear_apply LinearEquiv.ofLinear_apply

@[simp]
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl
#align linear_equiv.of_linear_symm_apply LinearEquiv.ofLinear_symm_apply

@[simp]
theorem ofLinear_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[simp]
theorem ofLinear_symm_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g := rfl

@[simp]
protected theorem range : LinearMap.range (e : M →ₛₗ[σ₁₂] M₂) = ⊤ :=
  LinearMap.range_eq_top.2 e.toEquiv.surjective
#align linear_equiv.range LinearEquiv.range

@[simp]
protected theorem _root_.LinearEquivClass.range [Module R M] [Module R₂ M₂] {F : Type*}
    [EquivLike F M M₂] [SemilinearEquivClass F σ₁₂ M M₂] (e : F) : LinearMap.range e = ⊤ :=
  LinearMap.range_eq_top.2 (EquivLike.surjective e)
#align linear_equiv_class.range LinearEquivClass.range

theorem eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p = ⊥ := by
  refine bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 ?_)
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule
#align linear_equiv.eq_bot_of_equiv LinearEquiv.eq_bot_of_equiv

-- Porting note: `RingHomSurjective σ₁₂` is an unused argument.
@[simp]
theorem range_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] :
    LinearMap.range (h.comp (e : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = LinearMap.range h :=
  LinearMap.range_comp_of_range_eq_top _ e.range
#align linear_equiv.range_comp LinearEquiv.range_comp

variable {f g}

/-- A linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear
equivalence between `M` and `f.range`.

This is a computable alternative to `LinearEquiv.ofInjective`, and a bidirectional version of
`LinearMap.rangeRestrict`. -/
def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ → M}
    (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f) :=
  { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align linear_equiv.of_left_inverse LinearEquiv.ofLeftInverse

@[simp]
theorem ofLeftInverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : M) : ↑(ofLeftInverse h x) = f x :=
  rfl
#align linear_equiv.of_left_inverse_apply LinearEquiv.ofLeftInverse_apply

@[simp]
theorem ofLeftInverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : LinearMap.range f) : (ofLeftInverse h).symm x = g x :=
  rfl
#align linear_equiv.of_left_inverse_symm_apply LinearEquiv.ofLeftInverse_symm_apply

variable (f)

/-- An `Injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `LinearMap.ofLeftInverse`. -/
noncomputable def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] LinearMap.range f :=
  ofLeftInverse <| Classical.choose_spec h.hasLeftInverse
#align linear_equiv.of_injective LinearEquiv.ofInjective

@[simp]
theorem ofInjective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : M) : ↑(ofInjective f h x) = f x :=
  rfl
#align linear_equiv.of_injective_apply LinearEquiv.ofInjective_apply

/-- A bijective linear map is a linear equivalence. -/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans (ofTop _ <| LinearMap.range_eq_top.2 hf.surjective)
#align linear_equiv.of_bijective LinearEquiv.ofBijective

@[simp]
theorem ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) :
    ofBijective f hf x = f x :=
  rfl
#align linear_equiv.of_bijective_apply LinearEquiv.ofBijective_apply

@[simp]
theorem ofBijective_symm_apply_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) :
    (ofBijective f h).symm (f x) = x := by
  simp [LinearEquiv.symm_apply_eq]

end

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {module_M₃ : Module R₃ M₃} {module_M₄ : Module R₄ M₄}
variable {σ₁₂ : R →+* R₂} {σ₃₄ : R₃ →+* R₄}
variable {σ₂₁ : R₂ →+* R} {σ₄₃ : R₄ →+* R₃}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₃₄ : RingHomInvPair σ₃₄ σ₄₃} {re₄₃ : RingHomInvPair σ₄₃ σ₃₄}
variable (e e₁ : M ≃ₛₗ[σ₁₂] M₂) (e₂ : M₃ ≃ₛₗ[σ₃₄] M₄)

#align linear_equiv.map_neg map_negₓ
#align linear_equiv.map_sub map_subₓ

end AddCommGroup

section Neg

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

/-- `x ↦ -x` as a `LinearEquiv` -/
def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M →ₗ[R] M) with }
#align linear_equiv.neg LinearEquiv.neg

variable {R}

@[simp]
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl
#align linear_equiv.coe_neg LinearEquiv.coe_neg

theorem neg_apply (x : M) : neg R x = -x := by simp
#align linear_equiv.neg_apply LinearEquiv.neg_apply

@[simp]
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl
#align linear_equiv.symm_neg LinearEquiv.symm_neg

end Neg

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a
#align linear_equiv.smul_of_unit LinearEquiv.smulOfUnit

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrowCongr {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁]
    [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) : (M₁ →ₗ[R] M₂₁) ≃ₗ[R] M₂ →ₗ[R] M₂₂ where
  toFun := fun f : M₁ →ₗ[R] M₂₁ => (e₂ : M₂₁ →ₗ[R] M₂₂).comp <| f.comp (e₁.symm : M₂ →ₗ[R] M₁)
  invFun f := (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp <| f.comp (e₁ : M₁ →ₗ[R] M₂)
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]
  map_smul' c f := by
    ext x
    simp only [smul_apply, Function.comp_apply, coe_comp, map_smulₛₗ e₂, coe_coe]
#align linear_equiv.arrow_congr LinearEquiv.arrowCongr

@[simp]
theorem arrowCongr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁)
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl
#align linear_equiv.arrow_congr_apply LinearEquiv.arrowCongr_apply

@[simp]
theorem arrowCongr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂)
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl
#align linear_equiv.arrow_congr_symm_apply LinearEquiv.arrowCongr_symm_apply

theorem arrowCongr_comp {N N₂ N₃ : Sort _} [AddCommMonoid N] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N] [Module R N₂] [Module R N₃] (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃)
    (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]
#align linear_equiv.arrow_congr_comp LinearEquiv.arrowCongr_comp

theorem arrowCongr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort _} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N₁]
    [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃] [Module R N₃]
    (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
    (arrowCongr e₁ e₂).trans (arrowCongr e₃ e₄) = arrowCongr (e₁.trans e₃) (e₂.trans e₄) :=
  rfl
#align linear_equiv.arrow_congr_trans LinearEquiv.arrowCongr_trans

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f
#align linear_equiv.congr_right LinearEquiv.congrRight

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : Module.End R M ≃ₗ[R] Module.End R M₂ :=
  arrowCongr e e
#align linear_equiv.conj LinearEquiv.conj

theorem conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) :
    e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp (e.symm : M₂ →ₗ[R] M) :=
  rfl
#align linear_equiv.conj_apply LinearEquiv.conj_apply

theorem conj_apply_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) (x : M₂) :
    e.conj f x = e (f (e.symm x)) :=
  rfl
#align linear_equiv.conj_apply_apply LinearEquiv.conj_apply_apply

theorem symm_conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M₂) :
    e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp (e : M →ₗ[R] M₂) :=
  rfl
#align linear_equiv.symm_conj_apply LinearEquiv.symm_conj_apply

theorem conj_comp (e : M ≃ₗ[R] M₂) (f g : Module.End R M) :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g
#align linear_equiv.conj_comp LinearEquiv.conj_comp

theorem conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj := by
  ext f x
  rfl
#align linear_equiv.conj_trans LinearEquiv.conj_trans

@[simp]
theorem conj_id (e : M ≃ₗ[R] M₂) : e.conj LinearMap.id = LinearMap.id := by
  ext
  simp [conj_apply]
#align linear_equiv.conj_id LinearEquiv.conj_id

variable (M) in
/-- An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-linear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module and an
`S`-module and their actions commute. -/
def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.left_inv ·)
  right_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.right_inv ·)

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module K M] [Module K M₂] [Module K M₃]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha
#align linear_equiv.smul_of_ne_zero LinearEquiv.smulOfNeZero

end Field

end LinearEquiv

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equivSubtypeMap q`
is the natural `LinearEquiv` between `q` and `q.map p.subtype`. -/
def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.subtype :=
  { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption
    left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    right_inv := fun ⟨x, ⟨_, h⟩, _, rfl⟩ => by ext; rfl }
#align submodule.equiv_subtype_map Submodule.equivSubtypeMap

@[simp]
theorem equivSubtypeMap_apply {p : Submodule R M} {q : Submodule R p} (x : q) :
    (p.equivSubtypeMap q x : M) = p.subtype.domRestrict q x :=
  rfl
#align submodule.equiv_subtype_map_apply Submodule.equivSubtypeMap_apply

@[simp]
theorem equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := by
  cases x
  rfl
#align submodule.equiv_subtype_map_symm_apply Submodule.equivSubtypeMap_symm_apply

/-- A linear injection `M ↪ N` restricts to an equivalence `f⁻¹ p ≃ p` for any submodule `p`
contained in its range. -/
@[simps! apply]
noncomputable def comap_equiv_self_of_inj_of_le {f : M →ₗ[R] N} {p : Submodule R N}
    (hf : Injective f) (h : p ≤ LinearMap.range f) :
    p.comap f ≃ₗ[R] p :=
  LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨x, hx⟩ ↦ mem_comap.mp hx)
  (⟨fun x y hxy ↦ by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ ↦ by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

end Module

end Submodule


namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }
#align equiv.to_linear_equiv Equiv.toLinearEquiv

end Equiv

section FunLeft

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable {m n p : Type*}

namespace LinearMap

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.fun_left LinearMap.funLeft

@[simp]
theorem funLeft_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl
#align linear_map.fun_left_apply LinearMap.funLeft_apply

@[simp]
theorem funLeft_id (g : n → M) : funLeft R M _root_.id g = g :=
  rfl
#align linear_map.fun_left_id LinearMap.funLeft_id

theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl
#align linear_map.fun_left_comp LinearMap.funLeft_comp

theorem funLeft_surjective_of_injective (f : m → n) (hf : Injective f) :
    Surjective (funLeft R M f) := by
  classical
    intro g
    refine ⟨fun x => if h : ∃ y, f y = x then g h.choose else 0, ?_⟩
    ext
    dsimp only [funLeft_apply]
    split_ifs with w
    · congr
      exact hf w.choose_spec
    · simp only [not_true, exists_apply_eq_apply] at w
#align linear_map.fun_left_surjective_of_injective LinearMap.funLeft_surjective_of_injective

theorem funLeft_injective_of_surjective (f : m → n) (hf : Surjective f) :
    Injective (funLeft R M f) := by
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  suffices LeftInverse (funLeft R M g) (funLeft R M f) by exact this.injective
  intro x
  rw [← LinearMap.comp_apply, ← funLeft_comp, hg.id, funLeft_id]
#align linear_map.fun_left_injective_of_surjective LinearMap.funLeft_injective_of_surjective

end LinearMap

namespace LinearEquiv

open LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])
#align linear_equiv.fun_congr_left LinearEquiv.funCongrLeft

@[simp]
theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl
#align linear_equiv.fun_congr_left_apply LinearEquiv.funCongrLeft_apply

@[simp]
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n → M) :=
  rfl
#align linear_equiv.fun_congr_left_id LinearEquiv.funCongrLeft_id

@[simp]
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl
#align linear_equiv.fun_congr_left_comp LinearEquiv.funCongrLeft_comp

@[simp]
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl
#align linear_equiv.fun_congr_left_symm LinearEquiv.funCongrLeft_symm

end LinearEquiv

end FunLeft
