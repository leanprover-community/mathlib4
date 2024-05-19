/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.RepresentationTheory.Basic

/-!
# Homomorphisms of `k`-linear `G`-representations

This file defines bundled homomorphisms of monoid representations. We largely mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `RepresentationHom ρ τ`: given `k`-linear `G`-representations `ρ, τ` of `k`-modules
`V, W` respectively, this is the type of `k`-linear maps `V → W` compatible with
the representations.

## Notations

* `ρ →ₑₗ τ`: representation homomorphism from `(V, ρ)` to `(W, τ)`.

-/


/-- should they be semilinear??? I'll need them semi-G-linear later,
but also sorta contravariantly semi-G-linear too. -/
structure RepresentationHom {k G V W : Type*}
    [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    extends V →ₗ[k] W where
  comm : ∀ g, toLinearMap ∘ₗ (ρ g) = τ g ∘ₗ toLinearMap

/- I'd like to use something like `→[k, G]` but I can't get it to work.
So for now it's `ₑₗ` for (G-)equivariant and (k-)linear. -/
@[inherit_doc]
notation:25 ρ " →ₑₗ " τ => RepresentationHom ρ τ

class RepresentationHomClass (F : Type*) {k G V W : outParam Type*}
    [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : outParam (Representation k G V)) (τ : outParam (Representation k G W)) [FunLike F V W]
    extends SemilinearMapClass F (RingHom.id k) V W : Prop where
  comm : ∀ (f : F) (g : G), f ∘ₗ (ρ g) = τ g ∘ₗ f

attribute [simp] RepresentationHomClass.comm

namespace RepresentationHomClass

variable {k G V W F : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] {ρ : Representation k G V} {τ : Representation k G W}
  [FunLike F V W] [RepresentationHomClass F ρ τ]

/-- Turn an element of a type `F` satisfying `RepresentationHomClass F ρ τ` into an actual
`RepresentationHom`. This is declared as the default coercion from `F` to `ρ →ₑₗ τ`. -/
@[coe]
def toRepresentationHom (f : F) : ρ →ₑₗ τ :=
  { (f : V →ₗ[k] W) with
    comm := RepresentationHomClass.comm f }

instance instCoeToRepresentationHom : CoeHead F (ρ →ₑₗ τ) :=
  ⟨RepresentationHomClass.toRepresentationHom⟩

@[simp]
theorem comm_apply (f : F) (g : G) (x : V) :
    f (ρ g x) = τ g (f x) :=
  LinearMap.congr_fun (comm f g) x

end RepresentationHomClass

namespace RepresentationHom

variable {k G V W X Y Z U : Type*}

section

variable [CommSemiring k] [Monoid G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
  {ρ : Representation k G V} {τ : Representation k G W}
  {η : Representation k G X} {μ : Representation k G Y}

instance funLike : FunLike (ρ →ₑₗ τ) V W where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr

instance representationHomClass : RepresentationHomClass (ρ →ₑₗ τ) ρ τ where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  comm := fun f => f.comm

/-- See Note [custom simps projection] -/
def Simps.apply (f : ρ →ₑₗ τ) : V → W := f

/-- See Note [custom simps projection] -/
def Simps.toLinearMap (f : ρ →ₑₗ τ) : V →ₗ[k] W := f

initialize_simps_projections RepresentationHom (toFun → apply, toLinearMap → toLinearMap)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F V W] [RepresentationHomClass F ρ τ] (f : F) :
    ⇑(f : ρ →ₑₗ τ) = f :=
  rfl

@[simp]
theorem coe_mk {f : V →ₗ[k] W} (h) : ((⟨f, h⟩ : ρ →ₑₗ τ) : V → W) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : V → W} (h₁ h₂ h₃) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : ρ →ₑₗ τ) = f :=
  rfl

@[simp, norm_cast]
theorem coe_linearMap_mk {f : V →ₗ[k] W} (h) : ((⟨f, h⟩ : ρ →ₑₗ τ) : V →ₗ[k] W) = f :=
  rfl

@[simp]
theorem toLinearMap_eq_coe (f : ρ →ₑₗ τ) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : ρ →ₑₗ τ) : ⇑(f : V →ₗ[k] W) = f :=
  rfl

@[norm_cast]
theorem coe_toAddMonoidHom (f : ρ →ₑₗ τ) : ⇑(f : V →+ W) = f :=
  rfl

theorem coe_fn_injective : @Function.Injective (ρ →ₑₗ τ) (V → W) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : ρ →ₑₗ τ} : (φ₁ : V → W) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_linearMap_injective : Function.Injective ((↑) : (ρ →ₑₗ τ) → V →ₗ[k] W) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : V →ₗ[k] W) : V → W) = ((φ₂ : V →ₗ[k] W) : V → W) from congr_arg _ H

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (ρ →ₑₗ τ) → V →+ W) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

protected theorem congr_fun {φ₁ φ₂ : ρ →ₑₗ τ} (H : φ₁ = φ₂) (x : V) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : ρ →ₑₗ τ) {x y : V} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : ρ →ₑₗ τ} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : ρ →ₑₗ τ} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff

@[ext high]
theorem ext_of_ring {ρ : Representation k G k} {τ : Representation k G V}
    {f g : ρ →ₑₗ τ} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
theorem mk_coe {f : ρ →ₑₗ τ} (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : ρ →ₑₗ τ) = f :=
  ext fun _ => rfl

/-- Copy of a `RepresentationHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[simps! apply toLinearMap]
protected def copy (f : ρ →ₑₗ τ) (f' : V → W) (h : f' = ⇑f) : ρ →ₑₗ τ :=
  { toLinearMap := (f : V →ₗ[k] W).copy f' h
    comm := fun g => by ext; simp_all }

theorem copy_eq (f : ρ →ₑₗ τ) (f' : V → W) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (ρ) in
/-- Identity map as a `RepresentationHom`. -/
@[simps! apply toLinearMap] protected def id : ρ →ₑₗ ρ :=
  { LinearMap.id with
    comm := fun _ => rfl }

/-- Composition of coalgebra homomorphisms. -/
@[simps! apply toLinearMap] def comp (φ₁ : τ →ₑₗ η) (φ₂ : ρ →ₑₗ τ) : ρ →ₑₗ η :=
  { (φ₁ : W →ₗ[k] X) ∘ₗ (φ₂ : V →ₗ[k] W) with
    comm := fun _ => by ext; simp }

variable (φ : ρ →ₑₗ τ)

@[simp]
theorem comp_id : φ.comp (RepresentationHom.id ρ) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (RepresentationHom.id τ).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : η →ₑₗ μ) (φ₂ : τ →ₑₗ η) (φ₃ : ρ →ₑₗ τ) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

theorem map_smul_of_tower {k₁} [SMul k₁ V] [SMul k₁ W]
    [LinearMap.CompatibleSMul V W k₁ k] (r : k₁)
    (x : V) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (ρ →ₑₗ ρ) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := RepresentationHom.id ρ
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl

@[simp]
theorem one_apply (x : V) : (1 : ρ →ₑₗ ρ) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : ρ →ₑₗ ρ) (x : V) : (φ * ψ) x = φ (ψ x) :=
  rfl

end
section CommMonoid

variable {k G : Type*} [CommSemiring k] [CommMonoid G] {V : Type*} [AddCommMonoid V]
  [Module k V] (ρ : Representation k G V)

@[simps! toLinearMap]
def ofComm (g : G) :
    ρ →ₑₗ ρ :=
  { ρ g with
    comm := fun _ => by
      ext
      dsimp
      rw [← LinearMap.mul_apply, ← map_mul, mul_comm, map_mul]
      rfl }

@[simp]
theorem ofComm_apply (g : G) (x : V) :
    ofComm ρ g x = ρ g x := rfl

end CommMonoid

/-! ### Arithmetic on the codomain -/

section Arithmetic

variable {k₁ k₂ : Type*}
variable [CommSemiring k] [Monoid G] [Monoid k₁] [CommRing k₂]
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
variable [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup U]
variable [Module k V] [Module k W] [Module k Y] [Module k U] [Module k₂ X] [Module k₂ Z]
variable [DistribMulAction k₁ W] [SMulCommClass k k₁ W] [SMul k₁ k] [IsScalarTower k₁ k W]
/- will check if these^ are the right combination when I'm not torturing myself with really loud
nightcore -/
variable (ρ : Representation k G V) (τ : Representation k G W)
variable (η : Representation k G Y) (β : Representation k G U)
variable (μ : Representation k₂ G X) (ν : Representation k₂ G Z)

@[simps! smul_toLinearMap smul_apply]
instance : SMul k₁ (ρ →ₑₗ τ) :=
  ⟨fun a f ↦
    { (a • f : V →ₗ[k] W) with
      comm := fun g => by ext; simp }⟩

@[simps! zero_toLinearMap zero_apply]
instance : Zero (ρ →ₑₗ τ) :=
  ⟨{ (0 : V →ₗ[k] W) with
     comm := by simp }⟩

@[simp]
theorem comp_zero (g : τ →ₑₗ η) : g.comp (0 : ρ →ₑₗ τ) = 0 :=
  ext fun _ ↦ by simp

@[simp]
theorem zero_comp (f : ρ →ₑₗ τ) : (0 : τ →ₑₗ η).comp f = 0 :=
  rfl

instance : Inhabited (ρ →ₑₗ τ) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : ρ →ₑₗ τ) = 0 :=
  rfl

instance uniqueOfLeft [Subsingleton V] : Unique (ρ →ₑₗ τ) :=
  { inferInstanceAs (Inhabited (ρ →ₑₗ τ)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }

instance uniqueOfRight [Subsingleton W] : Unique (ρ →ₑₗ τ) :=
  DFunLike.coe_injective.unique

@[simps! add_toLinearMap add_apply]
instance : Add (ρ →ₑₗ τ) :=
  ⟨fun f g ↦
    { (f + g : V →ₗ[k] W) with
      comm := fun _ => by ext; simp }⟩

theorem add_comp (f  : ρ →ₑₗ τ) (h g : τ →ₑₗ η) :
    (h + g).comp f = h.comp f + g.comp f :=
  rfl

theorem comp_add (f g : ρ →ₑₗ τ) (h : τ →ₑₗ η) :
    h.comp (f + g) = h.comp f + h.comp g :=
  ext fun _ ↦ h.map_add _ _

instance addCommMonoid : AddCommMonoid (ρ →ₑₗ τ) :=
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

@[simps! neg_toLinearMap neg_apply]
instance : Neg (ρ →ₑₗ η) :=
  ⟨fun f ↦
    { (-f : V →ₗ[k] Y) with
      comm := fun _ => by simp }⟩

theorem neg_comp (f : ρ →ₑₗ τ) (g : τ →ₑₗ η) :
    (-g).comp f = -g.comp f := by
  rfl

theorem comp_neg (f : ρ →ₑₗ η) (g : η →ₑₗ β) :
    g.comp (-f) = -g.comp f := by
  ext; simp

@[simps! sub_toLinearMap sub_apply]
instance : Sub (ρ →ₑₗ η) :=
  ⟨fun f g ↦
    { (f - g : V →ₗ[k] Y) with
      comm := fun _ => by ext; simp }⟩

theorem sub_comp (f : ρ →ₑₗ τ) (g h : τ →ₑₗ η) :
    (h - g).comp f = h.comp f - g.comp f := rfl

theorem comp_sub (f g : ρ →ₑₗ η) (h : η →ₑₗ β) :
    h.comp (f - g) = h.comp f - h.comp g := by
  ext; simp

/-- The type of linear maps is an additive group. -/
instance addCommGroup : AddCommGroup (μ →ₑₗ ν) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end Arithmetic

section Actions

variable {k₁ : Type*}
variable [CommSemiring k] [Monoid G] [Monoid k₁]
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
variable [AddCommGroup Y] [AddCommGroup Z]
variable [Module k V] [Module k W] [Module k Y]
variable [DistribMulAction k₁ W] [SMulCommClass k k₁ W] [SMul k₁ k] [IsScalarTower k₁ k W]
variable (ρ : Representation k G V) (τ : Representation k G W) (η : Representation k G Y)

instance : DistribMulAction k₁ (ρ →ₑₗ τ)
    where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _

/-
theorem smul_comp (a : k₁) (g : ρ →) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f :=
  rfl

-- TODO: generalize this to semilinear maps
theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f :=
  ext fun _ ↦ g.map_smul_of_tower _ _
#align linear_map.comp_smul LinearMap.comp_smul

instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) where
  one_smul _ := ext fun _ ↦ congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ ↦ congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ ↦ rfl
  smul_zero _ := ext fun _ ↦ rfl
-/

section Module

variable {R : Type*} [CommSemiring R]
variable [Module R W] [SMulCommClass k R W] [SMul R k] [IsScalarTower R k W]

instance module : Module R (ρ →ₑₗ τ) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul _ _
/-
instance [NoZeroSMulDivisors S M₂] : NoZeroSMulDivisors S (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by erw [DomMulAct.smul_linearMap_apply, zero_smul, map_zero]; rfl
-/

@[simps]
def eval (x : V) : (ρ →ₑₗ τ) →ₗ[k] W where
  toFun := fun f => f x
  map_add' := fun _ _=> rfl
  map_smul' := fun _ _ => rfl

end Module
end Actions

section Defs
open Representation
section

variable [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρ : Representation k G V) (τ : Representation k G W)

@[simps! toLinearMap]
noncomputable def leftRegularHom (x : V) : leftRegular k G →ₑₗ ρ :=
  { Finsupp.lift _ _ _ (fun g => ρ g x) with
    comm := fun _ => Finsupp.lhom_ext' fun y => LinearMap.ext_ring <| by simp }

@[simp]
theorem leftRegularHom_apply (x : V) (f : G →₀ k) :
    leftRegularHom ρ x f = Finsupp.lift _ _ _ (fun g => ρ g x) f := rfl

@[simps! apply]
noncomputable def leftRegularHomEquiv : (leftRegular k G →ₑₗ ρ) ≃ₗ[k] V :=
{ eval _ _ (Finsupp.single 1 1) with
  invFun := leftRegularHom ρ
  left_inv := fun _ => RepresentationHom.coe_linearMap_injective <| by
    ext; simp [← RepresentationHomClass.comm_apply]
  right_inv := fun _ => by simp }

@[simp]
theorem leftRegularHomEquiv_toLinearMap :
    leftRegularHomEquiv ρ = eval (leftRegular k G) ρ (Finsupp.single 1 1) := rfl

@[simp]
theorem leftRegularHomEquiv_symm_toLinearMap:
    (leftRegularHomEquiv ρ).symm = leftRegularHom ρ := rfl

@[simp]
theorem leftRegularHomEquiv_symm_apply_apply (x : V) :
    (leftRegularHomEquiv ρ).symm x = leftRegularHom ρ x := rfl

end

section

variable [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
variable {ρ : Representation k G V} {τ : Representation k G W}
variable {η : Representation k G X} {β : Representation k G Y}

@[simps! toLinearMap]
noncomputable def tprodMap (f : ρ →ₑₗ τ) (g : η →ₑₗ β) : ρ.tprod η →ₑₗ τ.tprod β :=
  { TensorProduct.map f g with
    comm := fun _ => by ext; simp }

@[simp]
theorem tprodMap_tmul (f : ρ →ₑₗ τ) (g : η →ₑₗ β) (x : V) (y : X) :
    tprodMap f g (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

variable (η) in
@[simps! toLinearMap]
noncomputable def lTensor (f : ρ →ₑₗ τ) : η.tprod ρ →ₑₗ η.tprod τ :=
  { LinearMap.lTensor X f with
    comm := fun g => by ext; simp }

@[simp]
theorem lTensor_tmul (f : ρ →ₑₗ τ) (x : X) (y : V) :
    lTensor η f (x ⊗ₜ y) = x ⊗ₜ f y := rfl

variable (η) in
@[simps! toLinearMap]
noncomputable def rTensor (f : ρ →ₑₗ τ) : ρ.tprod η →ₑₗ τ.tprod η :=
  { LinearMap.rTensor X f with
    comm := fun g => by ext; simp }

end

section

variable [CommSemiring k] [Group G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
variable {ρ : Representation k G V} {τ : Representation k G W}
variable {η : Representation k G X} {β : Representation k G Y}

variable (η) in
@[simps! toLinearMap]
def linHomMapLeft (f : ρ →ₑₗ τ) : linHom τ η →ₑₗ linHom ρ η :=
  { (f : V →ₗ[k] W).lcomp k X with
    comm := fun g => by ext; simp }

@[simp]
theorem linHomMapLeft_apply (f : ρ →ₑₗ τ) (g : W →ₗ[k] X) :
    linHomMapLeft η f g = (f : V →ₗ[k] W).lcomp k X g := rfl

variable (η) in
@[simps! toLinearMap apply]
def linHomMapRight (f : ρ →ₑₗ τ) : linHom η ρ →ₑₗ linHom η τ :=
  { LinearMap.llcomp k X V W f with
    comm := fun g => by ext; simp }

variable (ρ τ η) in
@[simps!]
noncomputable def curry : (ρ.tprod τ →ₑₗ η) →ₗ[k] (ρ →ₑₗ linHom τ η) where
  toFun := fun f =>
  { toLinearMap := TensorProduct.curry f
    comm := fun g => by ext; simp [← RepresentationHomClass.comm_apply] }
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

open scoped TensorProduct

@[simp]
theorem curry_apply_toLinearMap (f : ρ.tprod τ →ₑₗ η) :
    curry ρ τ η f = TensorProduct.curry (f : V ⊗[k] W →ₗ[k] X) := rfl

variable (ρ τ η) in
noncomputable def uncurry : (ρ →ₑₗ linHom τ η) →ₗ[k] (ρ.tprod τ →ₑₗ η) where
  toFun := fun f =>
  { toLinearMap := TensorProduct.uncurry k V W X f
    comm := fun g => by ext; simp }
  map_add' := fun _ _ => coe_linearMap_injective <| by simp
  map_smul' := fun _ _ => coe_linearMap_injective <| by simp

@[simp]
theorem uncurry_apply_toLinearMap (f : ρ →ₑₗ linHom τ η) :
    uncurry ρ τ η f = TensorProduct.uncurry k V W X f := rfl

@[simp]
theorem uncurry_apply_tmul (f : ρ →ₑₗ linHom τ η) (x : V) (y : W) :
    uncurry ρ τ η f (x ⊗ₜ y) = f x y := rfl

variable (ρ τ η) in
noncomputable def tprodLiftLEquiv : (ρ.tprod τ →ₑₗ η) ≃ₗ[k] (ρ →ₑₗ linHom τ η) :=
  { curry ρ τ η with
    invFun := uncurry ρ τ η,
    left_inv := fun _ => coe_linearMap_injective <| by ext; simp
    right_inv := fun _ => coe_linearMap_injective <| by ext; simp }

@[simp]
theorem tprodLiftLEquiv_toLinearMap :
    tprodLiftLEquiv ρ τ η = curry ρ τ η := rfl

@[simp]
theorem tprodLiftLEquiv_symm_toLinearMap :
    (tprodLiftLEquiv ρ τ η).symm = uncurry ρ τ η := rfl

@[simp]
theorem tprodLiftLEquiv_apply (f : ρ.tprod τ →ₑₗ η) :
    tprodLiftLEquiv ρ τ η f = curry ρ τ η f := rfl

@[simp]
theorem tprodLiftLEquiv_symm_apply (f : ρ →ₑₗ linHom τ η) :
    (tprodLiftLEquiv ρ τ η).symm f = uncurry ρ τ η f := rfl

end

end Defs

end RepresentationHom

open Representation

namespace LinearMap

variable {k V W : Type*} (G : Type*)

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- A linear map as a representation morphism of trivial representations. -/
@[simps! toLinearMap]
def toRepresentationHom (f : V →ₗ[k] W) :
    trivial k G V →ₑₗ trivial k G W :=
  { f with
    comm := fun _ => rfl }

@[simp]
theorem toReprsentaionHom_apply (f : V →ₗ[k] W) (x : V) :
    toRepresentationHom G f x = f x := rfl

end LinearMap
namespace MulActionHom

variable (k : Type*) {G H H' : Type*}

variable [CommSemiring k] [Monoid G] [MulAction G H] [MulAction G H']

@[simps! apply toLinearMap]
noncomputable def toRepresentationHom (f : H →[G] H') :
    ofMulAction k G H →ₑₗ ofMulAction k G H' :=
  { Finsupp.lmapDomain k k f with
    comm := fun g => Finsupp.lhom_ext fun x y => by simp }

end MulActionHom
namespace DistribMulActionHom

variable {k G V W : Type*} [CommSemiring k] [Monoid G]

section
variable [AddCommMonoid V] [AddCommMonoid W] [DistribMulAction G V] [DistribMulAction G W]

@[simps! toLinearMap apply]
def toNatRepresentationHom (f : V →+[G] W) :
    ofDistribMulAction ℕ G V →ₑₗ ofDistribMulAction ℕ G W :=
  { (f : V →+ W).toNatLinearMap with
    comm := fun g => by ext; simp [AddMonoidHom.toNatLinearMap] }

end
section
variable [AddCommGroup V] [AddCommGroup W] [DistribMulAction G V] [DistribMulAction G W]

@[simps! toLinearMap apply]
def toIntRepresentationHom (f : V →+[G] W) :
    ofDistribMulAction ℤ G V →ₑₗ ofDistribMulAction ℤ G W :=
  { (f : V →+ W).toIntLinearMap with
    comm := fun g => by ext; simp }

end
end DistribMulActionHom
