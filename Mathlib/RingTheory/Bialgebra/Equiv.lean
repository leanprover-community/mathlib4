import Mathlib.RingTheory.Coalgebra.Equiv
import Mathlib.RingTheory.Bialgebra.Hom

set_option autoImplicit true

open BigOperators

universe u v w u₁ v₁

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {k : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

open Coalgebra
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure BialgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
    [Semiring A] [Semiring B]
    [Bialgebra R A] [Bialgebra R B] extends A ≃c[R] B where
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [coe] BialgEquiv.toCoalgEquiv -- idk

/-- The notation `M ≃c [R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃b[" R "] " M₂ => BialgEquiv R M M₂

class BialgEquivClass (F : Type*) (R M M₂ : outParam (Type*)) [CommSemiring R] [Semiring M]
    [Semiring M₂]
    [Bialgebra R M] [Bialgebra R M₂]
    [EquivLike F M M₂] extends BialgHomClass F R M M₂, CoalgEquivClass F R M M₂ : Prop

namespace BialgEquivClass

variable (F : Type*) [CommSemiring R]

variable [Semiring M] [Semiring M₁] [Semiring M₂]

variable [Bialgebra R M] [Bialgebra R M₂]

instance (priority := 100)
  [EquivLike F M M₂] [s : BialgEquivClass F R M M₂] : BialgHomClass F R M M₂ :=
  { s with }

end BialgEquivClass

namespace BialgEquiv

section AddCommMonoid

variable {M₄ : Type*}

variable [CommSemiring R]

section

variable [Semiring M] [Semiring M₁] [Semiring M₂]

variable [Bialgebra R M] [Bialgebra R M₂]

@[simps! toCoalgHom] def toBialgHom (e : M ≃b[R] M₂) : M →b[R] M₂ :=
{ e.toCoalgEquiv.toCoalgHom with
  map_mul' := e.map_mul'
  map_one' := sorry
  commutes' := e.commutes' }

instance : Coe (M ≃b[R] M₂) (M →b[R] M₂) :=
  ⟨toBialgHom⟩

-- This exists for compatibility, previously `≃c[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (M ≃b[R] M₂) → M ≃ M₂ := fun f => f.toCoalgEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃b[R] M₂) → M ≃ M₂) :=
  sorry

@[simp]
theorem toEquiv_inj {e₁ e₂ : M ≃b[R] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toBialgHom_injective : Function.Injective (toBialgHom : (M ≃b[R] M₂) → M →b[R] M₂) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| BialgHom.congr_fun H

@[simp]
theorem toBialgHom_inj {e₁ e₂ : M ≃b[R] M₂} : (↑e₁ : M →b[R] M₂) = e₂ ↔ e₁ = e₂ :=
  toBialgHom_injective.eq_iff

instance : EquivLike (M ≃b[R] M₂) M M₂ where
  inv := fun f => f.invFun
  coe_injective' _ _ h _ := toBialgHom_injective (DFunLike.coe_injective h)
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv

instance : FunLike (M ≃b[R] M₂) M M₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

-- idk...
@[simps toEquiv] def toAlgEquiv (e : M ≃b[R] M₂) : M ≃ₐ[R] M₂ :=
{ e.toEquiv with
  map_mul' := e.map_mul'
  map_add' := e.map_add
  commutes' := e.commutes' }

instance : BialgEquivClass (M ≃b[R] M₂) R M M₂ where
  map_mul := (·.map_mul')
  map_one := fun f => f.toAlgEquiv.map_one
  map_zero := fun f => f.toAlgEquiv.map_zero
  commutes := (·.commutes')
  map_add := (·.map_add') --map_add' Porting note: TODO why did I need to change this?
  map_smulₛₗ := (·.map_smul') --map_smul' Porting note: TODO why did I need to change this?
  counit_comp := fun f => f.toCoalgEquiv.counit_comp
  map_comp_comul := fun f => f.toCoalgEquiv.map_comp_comul

/-
-- Porting note: moved to a lower line since there is no shortcut `CoeFun` instance any more
@[simp]
theorem coe_mk {to_fun a b c d e inv_fun left_inv right_inv} :
    (⟨⟨⟨⟨to_fun, a⟩, b, c⟩, e, d⟩, inv_fun, left_inv, right_inv⟩ : M ≃b[R] M₂) = to_fun := rfl
-/
theorem coe_injective : @Function.Injective (M ≃b[R] M₂) (M → M₂) CoeFun.coe :=
  DFunLike.coe_injective

end

section

variable [Semiring M] [Semiring M₁] [Semiring M₂]

variable [Semiring M₃] [Semiring M₄]

variable [Semiring N₁] [Semiring N₂]

variable {wtf : Bialgebra R M} {wtf2 : Bialgebra R M₂}

variable (e e' : M ≃b[R] M₂)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : M →b[R] M₂) = e :=
  rfl

@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
theorem coe_toBialgHom : ⇑e.toLinearMap = e :=
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
def refl  [Bialgebra R M] : M ≃b[R] M :=
  { BialgHom.id R M, CoalgEquiv.refl R M with }

end

@[simp]
theorem refl_apply  [Bialgebra R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃b[R] M₂) : M₂ ≃b[R] M :=
  { e.toCoalgEquiv.symm, e.toAlgEquiv.symm with }

def Simps.apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [Semiring M] [Semiring M₂]
    [Bialgebra R M] [Bialgebra R M₂]
    (e : M ≃b[R] M₂) : M → M₂ :=
  e

def Simps.symm_apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [Semiring M] [Semiring M₂]
    [Bialgebra R M] [Bialgebra R M₂]
    (e : M ≃b[R] M₂) : M₂ → M :=
  e.symm

-- can't get it to work idk why
--initialize_simps_projections BialgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl


variable {wtf : Bialgebra R M₁}

variable {ffs3 : Bialgebra R M₃}

variable {ffs : Bialgebra R N₁} {ffs2 : Bialgebra R N₂}

variable (e₁₂ : M₁ ≃b[R] M₂) (e₂₃ : M₂ ≃b[R] M₃)

-- Porting note: Lean 4 aggressively removes unused variables declared using `variables`, so
-- we have to list all the variables explicitly here in order to match the Lean 3 signature.
set_option linter.unusedVariables false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `BialgEquiv.self_trans_symm`.
@[trans, nolint unusedArguments]
def trans
    (e₁₂ : M₁ ≃b[R] M₂) (e₂₃ : M₂ ≃b[R] M₃) : M₁ ≃b[R] M₃ :=
  { e₁₂.toCoalgEquiv.trans e₂₃.toCoalgEquiv, e₁₂.toAlgEquiv.trans e₂₃.toAlgEquiv with }

variable {e₁₂} {e₂₃}
