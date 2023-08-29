/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct

#align_import representation_theory.basic from "leanprover-community/mathlib"@"c04bc6e93e23aa0182aba53661a2211e80b6feac"

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * Representation.Representation
  * Representation.character
  * Representation.tprod
  * Representation.linHom
  * Representation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V
#align representation Representation

end

namespace Representation

section trivial

variable (k : Type*) {G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1
#align representation.trivial Representation.trivial

-- Porting note: why is `V` implicit
@[simp]
theorem trivial_def (g : G) (v : V) : trivial k (V := V) g v = v :=
  rfl
#align representation.trivial_def Representation.trivial_def

end trivial

section MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `MonoidAlgebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : MonoidAlgebra k G →ₐ[k] Module.End k V :=
  (lift k G _) ρ
#align representation.as_algebra_hom Representation.asAlgebraHom

theorem asAlgebraHom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl
#align representation.as_algebra_hom_def Representation.asAlgebraHom_def

@[simp]
theorem asAlgebraHom_single (g : G) (r : k) : asAlgebraHom ρ (Finsupp.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]
  -- 🎉 no goals
#align representation.as_algebra_hom_single Representation.asAlgebraHom_single

theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by simp
                                                                                          -- 🎉 no goals
#align representation.as_algebra_hom_single_one Representation.asAlgebraHom_single_one

theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]
  -- 🎉 no goals
#align representation.as_algebra_hom_of Representation.asAlgebraHom_of

/-- If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module (MonoidAlgebra k G) ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
@[nolint unusedArguments]
def asModule (_ : Representation k G V) :=
  V
#align representation.as_module Representation.asModule

-- Porting note: no derive handler
instance : AddCommMonoid (ρ.asModule) := inferInstanceAs <| AddCommMonoid V

instance : Inhabited ρ.asModule where
  default := 0

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `MonoidAlgebra k G`.
-/
noncomputable instance asModuleModule : Module (MonoidAlgebra k G) ρ.asModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom
#align representation.as_module_module Representation.asModuleModule

-- Porting note: ρ.asModule doesn't unfold now
instance : Module k ρ.asModule := inferInstanceAs <| Module k V

/-- The additive equivalence from the `Module (MonoidAlgebra k G)` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
def asModuleEquiv : ρ.asModule ≃+ V :=
  AddEquiv.refl _
#align representation.as_module_equiv Representation.asModuleEquiv

@[simp]
theorem asModuleEquiv_map_smul (r : MonoidAlgebra k G) (x : ρ.asModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl
#align representation.as_module_equiv_map_smul Representation.asModuleEquiv_map_smul

@[simp]
theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k (MonoidAlgebra k G) r • ρ.asModuleEquiv.symm x := by
  apply_fun ρ.asModuleEquiv
  -- ⊢ ↑(asModuleEquiv ρ) (↑(AddEquiv.symm (asModuleEquiv ρ)) (r • x)) = ↑(asModule …
  simp
  -- 🎉 no goals
#align representation.as_module_equiv_symm_map_smul Representation.asModuleEquiv_symm_map_smul

@[simp]
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  apply_fun ρ.asModuleEquiv
  -- ⊢ ↑(asModuleEquiv ρ) (↑(AddEquiv.symm (asModuleEquiv ρ)) (↑(↑ρ g) x)) = ↑(asMo …
  simp
  -- 🎉 no goals
#align representation.as_module_equiv_symm_map_rho Representation.asModuleEquiv_symm_map_rho

/-- Build a `Representation k G M` from a `[Module (MonoidAlgebra k G) M]`.

This version is not always what we want, as it relies on an existing `[Module k M]`
instance, along with a `[IsScalarTower k (MonoidAlgebra k G) M]` instance.

We remedy this below in `ofModule`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable def ofModule' (M : Type*) [AddCommMonoid M] [Module k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M] : Representation k G M :=
  (MonoidAlgebra.lift k G (M →ₗ[k] M)).symm (Algebra.lsmul k k M)
#align representation.of_module' Representation.ofModule'

section

variable (M : Type*) [AddCommMonoid M] [Module (MonoidAlgebra k G) M]

/-- Build a `Representation` from a `[Module (MonoidAlgebra k G) M]`.

Note that the representation is built on `restrictScalars k (MonoidAlgebra k G) M`,
rather than on `M` itself.
-/
noncomputable def ofModule : Representation k G (RestrictScalars k (MonoidAlgebra k G) M) :=
  (MonoidAlgebra.lift k G
        (RestrictScalars k (MonoidAlgebra k G) M →ₗ[k]
          RestrictScalars k (MonoidAlgebra k G) M)).symm
    (RestrictScalars.lsmul k (MonoidAlgebra k G) M)
#align representation.of_module Representation.ofModule

/-!
## `ofModule` and `asModule` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalenceModuleMonoidAlgebra` for the full statement.

Starting with `ρ : Representation k G V`, converting to a module and back again
we have a `Representation k G (restrictScalars k (MonoidAlgebra k G) ρ.asModule)`.
To compare these, we use the composition of `restrictScalarsAddEquiv` and `ρ.asModuleEquiv`.

Similarly, starting with `Module (MonoidAlgebra k G) M`,
after we convert to a representation and back to a module,
we have `Module (MonoidAlgebra k G) (restrictScalars k (MonoidAlgebra k G) M)`.
-/


@[simp]
theorem ofModule_asAlgebraHom_apply_apply (r : MonoidAlgebra k G)
    (m : RestrictScalars k (MonoidAlgebra k G) M) :
    ((ofModule M).asAlgebraHom r) m =
      (RestrictScalars.addEquiv _ _ _).symm (r • RestrictScalars.addEquiv _ _ _ m) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    -- ⊢ ↑(↑(asAlgebraHom (ofModule M)) (↑(of k G) g)) m = ↑(AddEquiv.symm (RestrictS …
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule, AddEquiv.apply_eq_iff_eq,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    -- ⊢ ↑(↑(asAlgebraHom (ofModule M)) (f + g)) m = ↑(AddEquiv.symm (RestrictScalars …
    simp only [fw, gw, map_add, add_smul, LinearMap.add_apply]
    -- 🎉 no goals
  · intro r f w
    -- ⊢ ↑(↑(asAlgebraHom (ofModule M)) (r • f)) m = ↑(AddEquiv.symm (RestrictScalars …
    simp only [w, AlgHom.map_smul, LinearMap.smul_apply,
      RestrictScalars.addEquiv_symm_map_smul_smul]
#align representation.of_module_as_algebra_hom_apply_apply Representation.ofModule_asAlgebraHom_apply_apply

@[simp]
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k (MonoidAlgebra k G) ρ.asModule) :
    ofModule (k := k) (G := G) ρ.asModule g x = -- Porting note: more help with implicit
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  apply_fun RestrictScalars.addEquiv _ _ ρ.asModule using
    (RestrictScalars.addEquiv _ _ ρ.asModule).injective
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  -- ⊢ ↑(RestrictScalars.addEquiv k (MonoidAlgebra k G) (asModule ρ)) (↑(AddEquiv.s …
  simp
  -- 🎉 no goals
#align representation.of_module_as_module_act Representation.ofModule_asModule_act

theorem smul_ofModule_asModule (r : MonoidAlgebra k G) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  -- ⊢ ↑(RestrictScalars.addEquiv k (MonoidAlgebra k G) M) (↑(↑(asAlgebraHom (ofMod …
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]
  -- 🎉 no goals
#align representation.smul_of_module_as_module Representation.smul_ofModule_asModule

end

end MonoidAlgebra

section AddCommGroup

variable {k G V : Type*} [CommRing k] [Monoid G] [I : AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

instance : AddCommGroup ρ.asModule :=
  I

end AddCommGroup

section MulAction

variable (k : Type*) [CommSemiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def ofMulAction : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k ((· • ·) g)
  map_one' := by
    ext x y
    -- ⊢ ↑(↑(comp ((fun g => Finsupp.lmapDomain k k ((fun x x_1 => x • x_1) g)) 1) (F …
    dsimp
    -- ⊢ ↑(Finsupp.mapDomain (fun x => 1 • x) (Finsupp.single x 1)) y = ↑(Finsupp.sin …
    simp
    -- 🎉 no goals
  map_mul' x y := by
    ext z w
    -- ⊢ ↑(↑(comp (OneHom.toFun { toFun := fun g => Finsupp.lmapDomain k k ((fun x x_ …
    simp [mul_smul]
    -- 🎉 no goals
#align representation.of_mul_action Representation.ofMulAction

variable {k G H}

theorem ofMulAction_def (g : G) : ofMulAction k G H g = Finsupp.lmapDomain k k ((· • ·) g) :=
  rfl
#align representation.of_mul_action_def Representation.ofMulAction_def

theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single
#align representation.of_mul_action_single Representation.ofMulAction_single

end MulAction

section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

@[simp]
theorem ofMulAction_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulAction k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  -- ⊢ ↑(↑(↑(ofMulAction k G H) g) f) (g • g⁻¹ • h) = ↑f (g⁻¹ • h)
  let h' := g⁻¹ • h
  -- ⊢ ↑(↑(↑(ofMulAction k G H) g) f) (g • g⁻¹ • h) = ↑f (g⁻¹ • h)
  change ofMulAction k G H g f (g • h') = f h'
  -- ⊢ ↑(↑(↑(ofMulAction k G H) g) f) (g • h') = ↑f h'
  have hg : Function.Injective ((· • ·) g : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulAction_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]
  -- 🎉 no goals
#align representation.of_mul_action_apply Representation.ofMulAction_apply

-- Porting note: did not need this in ML3; noncomputable because IR check complains
noncomputable instance :
    HMul (MonoidAlgebra k G) ((ofMulAction k G G).asModule) (MonoidAlgebra k G) :=
  inferInstanceAs <| HMul (MonoidAlgebra k G) (MonoidAlgebra k G) (MonoidAlgebra k G)

theorem ofMulAction_self_smul_eq_mul (x : MonoidAlgebra k G) (y : (ofMulAction k G G).asModule) :
    x • y = (x * y : MonoidAlgebra k G) := -- by
  -- Porting note: trouble figuring out the motive
  x.induction_on (p := fun z => z • y = z * y)
    (fun g => by
      show asAlgebraHom (ofMulAction k G G) _ _ = _; ext;
      -- ⊢ ↑(↑(asAlgebraHom (ofMulAction k G G)) (↑(of k G) g)) y = ↑(of k G) g * y
                                                     -- ⊢ ↑(↑(↑(asAlgebraHom (ofMulAction k G G)) (↑(of k G) g)) y) a✝ = ↑(↑(of k G) g …
      simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul,
        ofMulAction_apply, smul_eq_mul]
      -- Porting note : single_mul_apply not firing in simp
      rw [MonoidAlgebra.single_mul_apply, one_mul]
      -- 🎉 no goals
    )
    (fun x y hx hy => by simp only [hx, hy, add_mul, add_smul]) fun r x hx => by
                         -- 🎉 no goals
    show asAlgebraHom (ofMulAction k G G) _ _ = _  -- Porting note: was simpa [← hx]
    -- ⊢ ↑(↑(asAlgebraHom (ofMulAction k G G)) (r • x)) y = r • x * y
    simp only [map_smul, smul_apply, Algebra.smul_mul_assoc]
    -- ⊢ r • ↑(↑(asAlgebraHom (ofMulAction k G G)) x) y = r • (x * y)
    rw [←hx]
    -- ⊢ r • ↑(↑(asAlgebraHom (ofMulAction k G G)) x) y = r • x • y
    rfl
    -- 🎉 no goals
#align representation.of_mul_action_self_smul_eq_mul Representation.ofMulAction_self_smul_eq_mul

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
noncomputable def ofMulActionSelfAsModuleEquiv :
    (ofMulAction k G G).asModule ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G :=
  { asModuleEquiv _ with map_smul' := ofMulAction_self_smul_eq_mul }
#align representation.of_mul_action_self_as_module_equiv Representation.ofMulActionSelfAsModuleEquiv

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ
#align representation.as_group_hom Representation.asGroupHom

theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]
  -- 🎉 no goals
#align representation.as_group_hom_apply Representation.asGroupHom_apply

end Group

section TensorProduct

variable {k G V W : Type*} [CommSemiring k] [Monoid G]

variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : Representation k G (V ⊗[k] W) where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [_root_.map_one, TensorProduct.map_one]
                 -- 🎉 no goals
  map_mul' g h := by simp only [_root_.map_mul, TensorProduct.map_mul]
                     -- 🎉 no goals
#align representation.tprod Representation.tprod

local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl
#align representation.tprod_apply Representation.tprod_apply

theorem smul_tprod_one_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let x' : ρV.asModule := x
    let z : (ρV.tprod 1).asModule := x ⊗ₜ y
    r • z = (r • x') ⊗ₜ y := by
  show asAlgebraHom (ρV ⊗ 1) _ _ = asAlgebraHom ρV _ _ ⊗ₜ _
  -- ⊢ ↑(↑(asAlgebraHom (ρV ⊗ 1)) r) (x ⊗ₜ[k] y) = ↑(↑(asAlgebraHom ρV) r) x ⊗ₜ[k] y
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  -- ⊢ (Finset.sum r.support fun x_1 => ↑r x_1 • ↑(↑ρV x_1) x ⊗ₜ[k] y) = Finset.sum …
  rfl
  -- 🎉 no goals
#align representation.smul_tprod_one_as_module Representation.smul_tprod_one_asModule

theorem smul_one_tprod_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let y' : ρW.asModule := y
    let z : (1 ⊗ ρW).asModule := x ⊗ₜ y
    r • z = x ⊗ₜ (r • y') := by
  show asAlgebraHom (1 ⊗ ρW) _ _ = _ ⊗ₜ asAlgebraHom ρW _ _
  -- ⊢ ↑(↑(asAlgebraHom (1 ⊗ ρW)) r) (x ⊗ₜ[k] y) = x ⊗ₜ[k] ↑(↑(asAlgebraHom ρW) r) y
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  -- 🎉 no goals
#align representation.smul_one_tprod_as_module Representation.smul_one_tprod_asModule

end TensorProduct

section LinearHom

variable {k G V W : Type*} [CommSemiring k] [Group G]

variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W) where
  toFun g :=
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
                                  -- 🎉 no goals
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
                                 -- 🎉 no goals
  map_one' :=
    LinearMap.ext fun x => by
      dsimp -- Porting note: now needed
      -- ⊢ comp (↑ρW 1) (comp x (↑ρV 1⁻¹)) = x
      simp_rw [inv_one, map_one, one_eq_id, comp_id, id_comp]
      -- 🎉 no goals
  map_mul' g h :=
    LinearMap.ext fun x => by
      dsimp -- Porting note: now needed
      -- ⊢ comp (↑ρW (g * h)) (comp x (↑ρV (g * h)⁻¹)) = comp (↑ρW g) (comp (comp (↑ρW  …
      simp_rw [mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]
      -- 🎉 no goals
#align representation.lin_hom Representation.linHom

@[simp]
theorem linHom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl
#align representation.lin_hom_apply Representation.linHom_apply

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : Module.Dual k V`.
-/
def dual : Representation k G (Module.Dual k V) where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
                                  -- 🎉 no goals
      map_smul' := fun r f => by
        ext
        -- ⊢ ↑(AddHom.toFun { toFun := fun f => comp f (↑ρV g⁻¹), map_add' := (_ : ∀ (f₁  …
        simp only [coe_comp, Function.comp_apply, smul_apply, RingHom.id_apply] }
        -- 🎉 no goals
  map_one' := by
    ext
    -- ⊢ ↑(↑((fun g => { toAddHom := { toFun := fun f => comp f (↑ρV g⁻¹), map_add' : …
    dsimp -- Porting note: now needed
    -- ⊢ ↑x✝¹ (↑(↑ρV 1⁻¹) x✝) = ↑x✝¹ x✝
    simp only [coe_comp, Function.comp_apply, map_one, inv_one, coe_mk, one_apply]
    -- 🎉 no goals
  map_mul' g h := by
    ext
    -- ⊢ ↑(↑(OneHom.toFun { toFun := fun g => { toAddHom := { toFun := fun f => comp  …
    dsimp -- Porting note: now needed
    -- ⊢ ↑x✝¹ (↑(↑ρV (g * h)⁻¹) x✝) = ↑x✝¹ (↑(↑ρV h⁻¹) (↑(↑ρV g⁻¹) x✝))
    simp only [coe_comp, Function.comp_apply, mul_inv_rev, map_mul, coe_mk, mul_apply]
    -- 🎉 no goals
#align representation.dual Representation.dual

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl
#align representation.dual_apply Representation.dual_apply

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `LinearAlgebra.Contraction.dualTensorHom`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W :=
  by ext; simp [Module.Dual.transpose_apply]
     -- ⊢ ↑(↑(↑(TensorProduct.AlgebraTensorModule.curry (comp (dualTensorHom k V W) (T …
          -- 🎉 no goals
#align representation.dual_tensor_hom_comm Representation.dualTensorHom_comm

end LinearHom

end Representation
