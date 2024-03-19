import Mathlib.RingTheory.Coalgebra.Hom

set_option autoImplicit true

open BigOperators

universe u v w u₁ v₁

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {k : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

open Coalgebra
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure CoalgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [Coalgebra R A] [Coalgebra R B] extends A →c[R] B, A ≃ₗ[R] B where

attribute [coe] CoalgEquiv.toCoalgHom

/-- The notation `M ≃ₗ [R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃c[" R "] " M₂ => CoalgEquiv R M M₂

class CoalgEquivClass (F : Type*) (R M M₂ : outParam (Type*)) [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] [Coalgebra R M] [Coalgebra R M₂]
    [EquivLike F M M₂]
    extends CoalgHomClass F R M M₂, SemilinearEquivClass F (RingHom.id R) M M₂ : Prop

namespace CoalgEquivClass

variable (F : Type*) [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [Coalgebra R M] [Coalgebra R M₂]

instance (priority := 100)
  [EquivLike F M M₂] [s : CoalgEquivClass F R M M₂] : CoalgHomClass F R M M₂ :=
  { s with }

end CoalgEquivClass

namespace CoalgEquiv

section AddCommMonoid

variable {M₄ : Type*}

variable [CommSemiring R]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [Coalgebra R M] [Coalgebra R M₂]

instance : Coe (M ≃c[R] M₂) (M →c[R] M₂) :=
  ⟨toCoalgHom⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (M ≃c[R] M₂) → M ≃ M₂ := fun f => f.toLinearEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃c[R] M₂) → M ≃ M₂) :=
  sorry

@[simp]
theorem toEquiv_inj {e₁ e₂ : M ≃c[R] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toCoalgHom_injective : Function.Injective (toCoalgHom : (M ≃c[R] M₂) → M →c[R] M₂) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| CoalgHom.congr_fun H

@[simp, norm_cast]
theorem toCoalgHom_inj {e₁ e₂ : M ≃c[R] M₂} : (↑e₁ : M →c[R] M₂) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

instance : EquivLike (M ≃c[R] M₂) M M₂ where
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

instance : FunLike (M ≃c[R] M₂) M M₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

instance : CoalgEquivClass (M ≃c[R] M₂) R M M₂ where
  map_add := (·.map_add') --map_add' Porting note: TODO why did I need to change this?
  map_smulₛₗ := (·.map_smul') --map_smul' Porting note: TODO why did I need to change this?
  counit_comp := sorry
  map_comp_comul := sorry

-- Porting note: moved to a lower line since there is no shortcut `CoeFun` instance any more
@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul ugh ugh2 left_inv right_inv} :
    (⟨⟨⟨⟨to_fun, map_add⟩, map_smul⟩, ugh, ugh2⟩, inv_fun, left_inv, right_inv⟩ : M ≃c[R] M₂) = to_fun := rfl

theorem coe_injective : @Function.Injective (M ≃c[R] M₂) (M → M₂) CoeFun.coe :=
  DFunLike.coe_injective

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [module_M : Module R M] [module_R_M₂ : Module R M₂] {wtf : Coalgebra R M} {wtf2 : Coalgebra R M₂}

variable (e e' : M ≃c[R] M₂)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : M →c[R] M₂) = e :=
  rfl

@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
theorem coe_toCoalgHom : ⇑e.toLinearMap = e :=
  rfl

-- porting note: no longer a `simp`
theorem toFun_eq_coe : e.toFun = e := rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  DFunLike.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [Module R M] [Coalgebra R M] : M ≃c[R] M :=
  { CoalgHom.id R M, LinearEquiv.refl R M with }

end

@[simp]
theorem refl_apply [Module R M] [Coalgebra R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃c[R] M₂) : M₂ ≃c[R] M :=
  { e.toLinearEquiv.symm with
    counit_comp := sorry
    map_comp_comul := sorry }

def Simps.apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [Coalgebra R M] [Coalgebra R M₂]
    (e : M ≃c[R] M₂) : M → M₂ :=
  e

def Simps.symm_apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [Coalgebra R M] [Coalgebra R M₂]
    (e : M ≃c[R] M₂) : M₂ → M :=
  e.symm

-- can't get it to work idk why
--initialize_simps_projections CoalgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl


variable [module_saM : Module R M₁] {wtf : Coalgebra R M₁}

variable [module_M₃ : Module R M₃] {ffs3 : Coalgebra R M₃}

variable [module_N₁ : Module R N₁] [module_N₂ : Module R N₂] {ffs : Coalgebra R N₁} {ffs2 : Coalgebra R N₂}

variable (e₁₂ : M₁ ≃c[R] M₂) (e₂₃ : M₂ ≃c[R] M₃)

-- Porting note: Lean 4 aggressively removes unused variables declared using `variables`, so
-- we have to list all the variables explicitly here in order to match the Lean 3 signature.
set_option linter.unusedVariables false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `CoalgEquiv.self_trans_symm`.
@[trans, nolint unusedArguments]
def trans
    (e₁₂ : M₁ ≃c[R] M₂) (e₂₃ : M₂ ≃c[R] M₃) : M₁ ≃c[R] M₃ :=
  { e₂₃.toCoalgHom.comp e₁₂.toCoalgHom, e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv with }

variable {e₁₂} {e₂₃}

/-@[simp]
theorem coe_toLinearEquiv : e.toLinearEquiv = e :=
  rfl-/

end
end AddCommMonoid
end CoalgEquiv
