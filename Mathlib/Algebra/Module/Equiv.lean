/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module algebra.module.equiv
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Module.LinearMap

/-!
# (Semi)linear equivalences

In this file we define

* `LinearEquiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `RingHom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `RingHom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `starRingEnd`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Algebra/Ring/CompTypeclasses`.

The group structure on automorphisms, `LinearEquiv.automorphismGroup`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

open Function

universe u u' v w x y z

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}
variable {k : Type _} {S : Type _} {M : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _}
variable {N₁ : Type _} {N₂ : Type _} {N₃ : Type _} {N₄ : Type _} {ι : Type _}

section

/-- A linear equivalence is an invertible linear map. -/
--Porting note: TODO @[nolint has_nonempty_instance]
structure LinearEquiv {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) (M₂ : Type _)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂
#align linear_equiv LinearEquiv

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap
#align linear_equiv.to_linear_map LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toAddEquiv
#align linear_equiv.to_add_equiv LinearEquiv.toAddEquiv

/-- The backwards directed function underlying a linear equivalence. -/
add_decl_doc LinearEquiv.invFun

/-- `LinearEquiv.invFun` is a right inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.right_inv

/-- `LinearEquiv.invFun` is a left inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.left_inv

-- mathport name: «expr ≃ₛₗ[ ] »
/-- The notation `M ≃ₛₗ[σ] M₂` denotes the type of linear equivalences between `M` and `M₂` over a
ring homomorphism `σ`. -/
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

-- mathport name: «expr ≃ₗ[ ] »
/-- The notation `M ≃ₗ [R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

-- mathport name: «expr ≃ₗ⋆[ ] »
/-- The notation `M ≃ₗ⋆[R] M₂` denotes the type of star-linear equivalences between `M` and `M₂`
over the `⋆` endomorphism of the underlying starred ring `R`. -/
notation:50 M " ≃ₗ⋆[" R "] " M₂ => LinearEquiv (starRingEnd R) M M₂

/-- `SemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear equivs
`M → M₂`.

See also `LinearEquivClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearEquivClass (F : Type _) {R S : outParam (Type _)} [Semiring R] [Semiring S]
  (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M M₂ : outParam (Type _)) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
  AddEquivClass F M M₂ where
  /-- Applying a semilinear equivalence `f` over `σ` to `r • x ` equals `σ r • f x`. -/
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x
#align semilinear_equiv_class SemilinearEquivClass

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.

/-- `LinearEquivClass F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `M → M₂`.
This is an abbreviation for `SemilinearEquivClass F (RingHom.id R) M M₂`.
-/
abbrev LinearEquivClass (F : Type _) (R M M₂ : outParam (Type _)) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] :=
  SemilinearEquivClass F (RingHom.id R) M M₂
#align linear_equiv_class LinearEquivClass

end

namespace SemilinearEquivClass

variable (F : Type _) [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

@[infer_tc_goals_rl, nolint dangerousInstance]
instance (priority := 100) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [s : SemilinearEquivClass F σ M M₂] : SemilinearMapClass F σ M M₂ :=
  { s with
    coe := (s.coe : F → M → M₂)
    coe_injective' := @FunLike.coe_injective F _ _ _ }

end SemilinearEquivClass

namespace LinearEquiv

section AddCommMonoid

variable {M₄ : Type _}

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

instance : Coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := fun f => f.toAddEquiv.toEquiv
#align linear_equiv.to_equiv LinearEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
  fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h =>
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩
#align linear_equiv.to_equiv_injective LinearEquiv.toEquiv_injective

@[simp]
theorem toEquiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
#align linear_equiv.to_equiv_inj LinearEquiv.toEquiv_inj

theorem toLinearMap_injective : Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) → M →ₛₗ[σ] M₂) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| LinearMap.congr_fun H
#align linear_equiv.to_linear_map_injective LinearEquiv.toLinearMap_injective

@[simp] --Porting note: TODO @[norm_cast]
theorem toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  toLinearMap_injective.eq_iff
#align linear_equiv.to_linear_map_inj LinearEquiv.toLinearMap_inj

instance : SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂
    where
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (FunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv
  map_add := (·.map_add') --map_add' Porting note: TODO why did I need to change this?
  map_smulₛₗ := (·.map_smul') --map_smul' Porting note: TODO why did I need to change this?

-- Porting note: moved to a lower line since there is no shortcut `CoeFun` instance any more
@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv} :
    (⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) = to_fun := rfl
#align linear_equiv.coe_mk LinearEquiv.coe_mk

theorem coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M → M₂) CoeFun.coe :=
  FunLike.coe_injective
#align linear_equiv.coe_injective LinearEquiv.coe_injective

end

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid N₁] [AddCommMonoid N₂]

variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}

variable (e e' : M ≃ₛₗ[σ] M₂)

@[simp]  -- Porting note: TODO @[norm_cast]
theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e :=
  rfl
#align linear_equiv.coe_coe LinearEquiv.coe_coe

@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl
#align linear_equiv.coe_to_equiv LinearEquiv.coe_toEquiv

@[simp]
theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl
#align linear_equiv.coe_to_linear_map LinearEquiv.coe_toLinearMap

-- porting note: no longer a `simp`
theorem toFun_eq_coe : e.toFun = e := rfl
#align linear_equiv.to_fun_eq_coe LinearEquiv.toFun_eq_coe

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  FunLike.ext _ _ h
#align linear_equiv.ext LinearEquiv.ext

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  FunLike.ext_iff
#align linear_equiv.ext_iff LinearEquiv.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  FunLike.congr_arg e
#align linear_equiv.congr_arg LinearEquiv.congr_arg

protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  FunLike.congr_fun h x
#align linear_equiv.congr_fun LinearEquiv.congr_fun

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [Module R M] : M ≃ₗ[R] M :=
  { LinearMap.id, Equiv.refl M with }
#align linear_equiv.refl LinearEquiv.refl

end

@[simp]
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl
#align linear_equiv.refl_apply LinearEquiv.refl_apply

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' := fun r x => by dsimp only; rw [map_smulₛₗ] }
#align linear_equiv.symm LinearEquiv.symm

/-- See Note [custom simps projection] -/
def Simps.symmApply {R : Type _} {S : Type _} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type _} {M₂ : Type _} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M₂ → M :=
  e.symm
#align linear_equiv.simps.symm_apply LinearEquiv.Simps.symmApply

initialize_simps_projections LinearEquiv (toLinearMap → apply, invFun → symmApply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl
#align linear_equiv.inv_fun_eq_symm LinearEquiv.invFun_eq_symm

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl
#align linear_equiv.coe_to_equiv_symm LinearEquiv.coe_toEquiv_symm

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}

variable [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]

variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

-- Note: The linter thinks the `RingHomCompTriple` argument is doubled -- it is not.
/-- Linear equivalences are transitive. -/
@[trans, nolint unusedArguments]
def trans : M₁ ≃ₛₗ[σ₁₃] M₃ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }
#align linear_equiv.trans LinearEquiv.trans

-- mathport name: «expr ≪≫ₗ »
set_option quotPrecheck false in
/-- The notation `e₁ ≪≫ₗ e₂` denotes the composition of the linear equivalences `e₁` and `e₂`. -/
infixl:80 " ≪≫ₗ " =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids

variable {e₁₂} {e₂₃}

@[simp]
theorem coe_toAddEquiv : e.toAddEquiv = e :=
  rfl
#align linear_equiv.coe_to_add_equiv LinearEquiv.coe_toAddEquiv

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
theorem toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl
#align linear_equiv.to_add_monoid_hom_commutes LinearEquiv.toAddMonoidHom_commutes

@[simp]
theorem trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) :=
  rfl
#align linear_equiv.trans_apply LinearEquiv.trans_apply

theorem coe_trans :
    (e₁₂.trans e₂₃ : M₁ →ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ →ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl
#align linear_equiv.coe_trans LinearEquiv.coe_trans

@[simp]
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c
#align linear_equiv.apply_symm_apply LinearEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (b : M) : e.symm (e b) = b :=
  e.left_inv b
#align linear_equiv.symm_apply_apply LinearEquiv.symm_apply_apply

@[simp]
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl
#align linear_equiv.trans_symm LinearEquiv.trans_symm

theorem symm_trans_apply (c : M₃) :
    (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl
#align linear_equiv.symm_trans_apply LinearEquiv.symm_trans_apply

@[simp]
theorem trans_refl : e.trans (refl S M₂) = e :=
  toEquiv_injective e.toEquiv.trans_refl
#align linear_equiv.trans_refl LinearEquiv.trans_refl

@[simp]
theorem refl_trans : (refl R M).trans e = e :=
  toEquiv_injective e.toEquiv.refl_trans
#align linear_equiv.refl_trans LinearEquiv.refl_trans

theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align linear_equiv.symm_apply_eq LinearEquiv.symm_apply_eq

theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
#align linear_equiv.eq_symm_apply LinearEquiv.eq_symm_apply

theorem eq_comp_symm {α : Type _} (f : M₂ → α) (g : M₁ → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g
#align linear_equiv.eq_comp_symm LinearEquiv.eq_comp_symm

theorem comp_symm_eq {α : Type _} (f : M₂ → α) (g : M₁ → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g
#align linear_equiv.comp_symm_eq LinearEquiv.comp_symm_eq

theorem eq_symm_comp {α : Type _} (f : α → M₁) (g : α → M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g
#align linear_equiv.eq_symm_comp LinearEquiv.eq_symm_comp

theorem symm_comp_eq {α : Type _} (f : α → M₁) (g : α → M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g
#align linear_equiv.symm_comp_eq LinearEquiv.symm_comp_eq

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

theorem eq_comp_toLinearMap_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.toEquiv.eq_comp_symm f g]
  · simp [← H, ← e₁₂.toEquiv.eq_comp_symm f g]
#align linear_equiv.eq_comp_to_linear_map_symm LinearEquiv.eq_comp_toLinearMap_symm

theorem comp_toLinearMap_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.toEquiv.comp_symm_eq f g]
  · simp [H, e₁₂.toEquiv.comp_symm_eq f g]
#align linear_equiv.comp_to_linear_map_symm_eq LinearEquiv.comp_toLinearMap_symm_eq

theorem eq_toLinearMap_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.toEquiv.eq_symm_comp f g]
  · simp [← H, ← e₁₂.toEquiv.eq_symm_comp f g]
#align linear_equiv.eq_to_linear_map_symm_comp LinearEquiv.eq_toLinearMap_symm_comp

theorem toLinearMap_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.toEquiv.symm_comp_eq f g]
  · simp [H, e₁₂.toEquiv.symm_comp_eq f g]
#align linear_equiv.to_linear_map_symm_comp_eq LinearEquiv.toLinearMap_symm_comp_eq

@[simp]
theorem refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M :=
  rfl
#align linear_equiv.refl_symm LinearEquiv.refl_symm

@[simp]
theorem self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R₁ M₁ := by
  ext x
  simp
#align linear_equiv.self_trans_symm LinearEquiv.self_trans_symm

@[simp]
theorem symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.symm.trans f = LinearEquiv.refl R₂ M₂ := by
  ext x
  simp
#align linear_equiv.symm_trans_self LinearEquiv.symm_trans_self

@[simp]  -- Porting note: norm_cast
theorem refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M →ₗ[R] M) = LinearMap.id :=
  rfl
#align linear_equiv.refl_to_linear_map LinearEquiv.refl_toLinearMap

@[simp]  -- Porting note: norm_cast
theorem comp_coe [Module R M] [Module R M₂] [Module R M₃] (f : M ≃ₗ[R] M₂) (f' : M₂ ≃ₗ[R] M₃) :
    (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
  rfl
#align linear_equiv.comp_coe LinearEquiv.comp_coe

@[simp]
theorem mk_coe (f h₁ h₂) : (LinearEquiv.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e :=
  ext fun _ => rfl
#align linear_equiv.mk_coe LinearEquiv.mk_coe

protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b
#align linear_equiv.map_add LinearEquiv.map_add

protected theorem map_zero : e 0 = 0 :=
  map_zero e
#align linear_equiv.map_zero LinearEquiv.map_zero

protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ : R → S) c • e x :=
  e.map_smul' c x
#align linear_equiv.map_smulₛₗ LinearEquiv.map_smulₛₗ

theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x :=
  map_smulₛₗ e c x
#align linear_equiv.map_smul LinearEquiv.map_smul

theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff
#align linear_equiv.map_eq_zero_iff LinearEquiv.map_eq_zero_iff

theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff
#align linear_equiv.map_ne_zero_iff LinearEquiv.map_ne_zero_iff

@[simp]
theorem symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e := by
  cases e
  rfl
#align linear_equiv.symm_symm LinearEquiv.symm_symm

theorem symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ'] :
    Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M) :=
  Equiv.bijective
    ⟨(symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M), (symm : (M₂ ≃ₛₗ[σ'] M) → M ≃ₛₗ[σ] M₂), symm_symm,
      symm_symm⟩
#align linear_equiv.symm_bijective LinearEquiv.symm_bijective

@[simp]
theorem mk_coe' (f h₁ h₂ h₃ h₄) :
    (LinearEquiv.mk ⟨⟨f, h₁⟩, h₂⟩ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
#align linear_equiv.mk_coe' LinearEquiv.mk_coe'

@[simp]
theorem symm_mk (f h₁ h₂ h₃ h₄) :
    (⟨⟨⟨e, h₁⟩, h₂⟩, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
      {
        (⟨⟨⟨e, h₁⟩, h₂⟩, f, h₃, h₄⟩ : M ≃ₛₗ[σ]
              M₂).symm with
        toFun := f
        invFun := e } :=
  rfl
#align linear_equiv.symm_mk LinearEquiv.symm_mk

@[simp]
theorem coe_symm_mk [Module R M] [Module R M₂]
    {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl
#align linear_equiv.coe_symm_mk LinearEquiv.coe_symm_mk

protected theorem bijective : Function.Bijective e :=
  e.toEquiv.bijective
#align linear_equiv.bijective LinearEquiv.bijective

protected theorem injective : Function.Injective e :=
  e.toEquiv.injective
#align linear_equiv.injective LinearEquiv.injective

protected theorem surjective : Function.Surjective e :=
  e.toEquiv.surjective
#align linear_equiv.surjective LinearEquiv.surjective

protected theorem image_eq_preimage (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align linear_equiv.image_eq_preimage LinearEquiv.image_eq_preimage

protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage s
#align linear_equiv.image_symm_eq_preimage LinearEquiv.image_symm_eq_preimage

end

/-- Interpret a `RingEquiv` `f` as an `f`-semilinear equiv. -/
@[simps]
def _root_.RingEquiv.toSemilinearEquiv (f : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
    R ≃ₛₗ[(↑f : R →+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }
#align ring_equiv.to_semilinear_equiv RingEquiv.toSemilinearEquiv
#align ring_equiv.to_semilinear_equiv_symm_apply RingEquiv.toSemilinearEquiv_symmApply

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

/-- An involutive linear map is a linear equivalence. -/
def ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }
#align linear_equiv.of_involutive LinearEquiv.ofInvolutive

@[simp]
theorem coe_ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl
#align linear_equiv.coe_of_involutive LinearEquiv.coe_ofInvolutive

section RestrictScalars

variable (R)
variable [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `LinearMap.restrictScalars`. -/
@[simps]
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
  { f.toLinearMap.restrictScalars R with
    toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv }
#align linear_equiv.restrict_scalars LinearEquiv.restrictScalars
#align linear_equiv.restrict_scalars_symm_apply LinearEquiv.restrictScalars_symmApply

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun _ _ h =>
  ext (LinearEquiv.congr_fun h : _)
#align linear_equiv.restrict_scalars_injective LinearEquiv.restrictScalars_injective

@[simp]
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff
#align linear_equiv.restrict_scalars_inj LinearEquiv.restrictScalars_inj

end RestrictScalars

section Automorphisms

variable [Module R M]

instance automorphismGroup : Group (M ≃ₗ[R] M)
    where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := ext fun x => rfl
  one_mul f := ext fun x => rfl
  mul_left_inv f := ext <| f.left_inv
#align linear_equiv.automorphism_group LinearEquiv.automorphismGroup

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M
    where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
#align linear_equiv.automorphism_group.to_linear_map_monoid_hom LinearEquiv.automorphismGroup.toLinearMapMonoidHom
#align linear_equiv.automorphism_group.to_linear_map_monoid_hom_apply LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M
    where
  smul := (· <| ·)
  smul_zero := LinearEquiv.map_zero
  smul_add := LinearEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align linear_equiv.apply_distrib_mul_action LinearEquiv.applyDistribMulAction

@[simp]
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl
#align linear_equiv.smul_def LinearEquiv.smul_def

/-- `LinearEquiv.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨@fun _ _ => LinearEquiv.ext⟩
#align linear_equiv.apply_has_faithful_smul LinearEquiv.apply_faithfulSMul

instance apply_sMulCommClass : SMulCommClass R (M ≃ₗ[R] M) M
    where smul_comm r e m := (e.map_smul r m).symm
#align linear_equiv.apply_smul_comm_class LinearEquiv.apply_sMulCommClass

instance apply_sMulCommClass' : SMulCommClass (M ≃ₗ[R] M) R M
    where smul_comm := LinearEquiv.map_smul
#align linear_equiv.apply_smul_comm_class' LinearEquiv.apply_sMulCommClass'

end Automorphisms

section OfSubsingleton

variable (M M₂)
variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M →ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }
#align linear_equiv.of_subsingleton LinearEquiv.ofSubsingleton
#align linear_equiv.of_subsingleton_symm_apply LinearEquiv.ofSubsingleton_symmApply

@[simp]
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by
  ext
  simp
#align linear_equiv.of_subsingleton_self LinearEquiv.ofSubsingleton_self

end OfSubsingleton

end AddCommMonoid

end LinearEquiv

namespace Module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
def compHom.toLinearEquiv {R S : Type _} [Semiring R] [Semiring S] (g : R ≃+* S) :
    haveI := compHom S (↑g : R →+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R →+* S)
  { g with
    toFun := (g : R → S)
    invFun := (g.symm : S → R)
    map_smul' := g.map_mul }
#align module.comp_hom.to_linear_equiv Module.compHom.toLinearEquiv
#align module.comp_hom.to_linear_equiv_symm_apply Module.compHom.toLinearEquiv_symmApply

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`. -/
@[simps]
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, toLinearMap R M s with }
#align distrib_mul_action.to_linear_equiv DistribMulAction.toLinearEquiv
#align distrib_mul_action.to_linear_equiv_apply DistribMulAction.toLinearEquiv_apply
#align distrib_mul_action.to_linear_equiv_symm_apply DistribMulAction.toLinearEquiv_symmApply

/-- Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`. -/
@[simps]
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' _ _ := LinearEquiv.ext <| mul_smul _ _
#align distrib_mul_action.to_module_aut DistribMulAction.toModuleAut
#align distrib_mul_action.to_module_aut_apply DistribMulAction.toModuleAut_apply

end DistribMulAction

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂]

variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }
#align add_equiv.to_linear_equiv AddEquiv.toLinearEquiv

@[simp]
theorem coe_toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl
#align add_equiv.coe_to_linear_equiv AddEquiv.coe_toLinearEquiv

@[simp]
theorem coe_toLinearEquiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl
#align add_equiv.coe_to_linear_equiv_symm AddEquiv.coe_toLinearEquiv_symm

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a => by
    erw [e.toAddMonoidHom.map_nsmul]
    rfl
#align add_equiv.to_nat_linear_equiv AddEquiv.toNatLinearEquiv

@[simp]
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_nat_linear_equiv AddEquiv.coe_toNatLinearEquiv

@[simp]
theorem toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e := by
  ext
  rfl
#align add_equiv.to_nat_linear_equiv_to_add_equiv AddEquiv.toNatLinearEquiv_toAddEquiv

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e :=
  FunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_nat_linear_equiv LinearEquiv.toAddEquiv_toNatLinearEquiv

@[simp]
theorem toNatLinearEquiv_symm : e.toNatLinearEquiv.symm = e.symm.toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_symm AddEquiv.toNatLinearEquiv_symm

@[simp]
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl
#align add_equiv.to_nat_linear_equiv_refl AddEquiv.toNatLinearEquiv_refl

@[simp]
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toNatLinearEquiv.trans e₂.toNatLinearEquiv = (e.trans e₂).toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_trans AddEquiv.toNatLinearEquiv_trans

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ :=
  e.toLinearEquiv fun c a => e.toAddMonoidHom.map_zsmul a c
#align add_equiv.to_int_linear_equiv AddEquiv.toIntLinearEquiv

@[simp]
theorem coe_toIntLinearEquiv : ⇑e.toIntLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_int_linear_equiv AddEquiv.coe_toIntLinearEquiv

@[simp]
theorem toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e := by
  ext
  rfl
#align add_equiv.to_int_linear_equiv_to_add_equiv AddEquiv.toIntLinearEquiv_toAddEquiv

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[ℤ] M₂) :
    AddEquiv.toIntLinearEquiv (e : M ≃+ M₂) = e :=
  FunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_int_linear_equiv LinearEquiv.toAddEquiv_toIntLinearEquiv

@[simp]
theorem toIntLinearEquiv_symm : e.toIntLinearEquiv.symm = e.symm.toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_symm AddEquiv.toIntLinearEquiv_symm

@[simp]
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl
#align add_equiv.to_int_linear_equiv_refl AddEquiv.toIntLinearEquiv_refl

@[simp]
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toIntLinearEquiv.trans e₂.toIntLinearEquiv = (e.trans e₂).toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_trans AddEquiv.toIntLinearEquiv_trans

end AddCommGroup

end AddEquiv
