/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle

! This file was ported from Lean 3 source module representation_theory.basic
! leanprover-community/mathlib commit c04bc6e93e23aa0182aba53661a2211e80b6feac
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.Contraction
import Mathbin.RingTheory.TensorProduct

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type _) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V
#align representation Representation

end

namespace Representation

section trivial

variable (k : Type _) {G V : Type _} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1
#align representation.trivial Representation.trivial

@[simp]
theorem trivial_def (g : G) (v : V) : trivial k g v = v :=
  rfl
#align representation.trivial_def Representation.trivial_def

end trivial

section MonoidAlgebra

variable {k G V : Type _} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : MonoidAlgebra k G →ₐ[k] Module.End k V :=
  (lift k G _) ρ
#align representation.as_algebra_hom Representation.asAlgebraHom

theorem asAlgebraHom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl
#align representation.as_algebra_hom_def Representation.asAlgebraHom_def

@[simp]
theorem asAlgebraHom_single (g : G) (r : k) : asAlgebraHom ρ (Finsupp.single g r) = r • ρ g := by
  simp only [as_algebra_hom_def, MonoidAlgebra.lift_single]
#align representation.as_algebra_hom_single Representation.asAlgebraHom_single

theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by simp
#align representation.as_algebra_hom_single_one Representation.asAlgebraHom_single_one

theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, as_algebra_hom_single, one_smul]
#align representation.as_algebra_hom_of Representation.asAlgebraHom_of

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] (module.End[module.End] k V) -/
/-- If `ρ : representation k G V`, then `ρ.as_module` is a type synonym for `V`,
which we equip with an instance `module (monoid_algebra k G) ρ.as_module`.

You should use `as_module_equiv : ρ.as_module ≃+ V` to translate terms.
-/
@[nolint unused_arguments]
def AsModule (ρ : Representation k G V) :=
  V deriving AddCommMonoid,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler module[module] (module.End[module.End] k V)»
#align representation.as_module Representation.AsModule

instance : Inhabited ρ.AsModule :=
  ⟨0⟩

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable instance asModuleModule : Module (MonoidAlgebra k G) ρ.AsModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom
#align representation.as_module_module Representation.asModuleModule

/-- The additive equivalence from the `module (monoid_algebra k G)` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
def asModuleEquiv : ρ.AsModule ≃+ V :=
  AddEquiv.refl _
#align representation.as_module_equiv Representation.asModuleEquiv

@[simp]
theorem asModuleEquiv_map_smul (r : MonoidAlgebra k G) (x : ρ.AsModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl
#align representation.as_module_equiv_map_smul Representation.asModuleEquiv_map_smul

@[simp]
theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k (MonoidAlgebra k G) r • ρ.asModuleEquiv.symm x :=
  by
  apply_fun ρ.as_module_equiv
  simp
#align representation.as_module_equiv_symm_map_smul Representation.asModuleEquiv_symm_map_smul

@[simp]
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x :=
  by
  apply_fun ρ.as_module_equiv
  simp
#align representation.as_module_equiv_symm_map_rho Representation.asModuleEquiv_symm_map_rho

/-- Build a `representation k G M` from a `[module (monoid_algebra k G) M]`.

This version is not always what we want, as it relies on an existing `[module k M]`
instance, along with a `[is_scalar_tower k (monoid_algebra k G) M]` instance.

We remedy this below in `of_module`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable def ofModule' (M : Type _) [AddCommMonoid M] [Module k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M] : Representation k G M :=
  (MonoidAlgebra.lift k G (M →ₗ[k] M)).symm (Algebra.lsmul k M)
#align representation.of_module' Representation.ofModule'

section

variable (k G) (M : Type _) [AddCommMonoid M] [Module (MonoidAlgebra k G) M]

/-- Build a `representation` from a `[module (monoid_algebra k G) M]`.

Note that the representation is built on `restrict_scalars k (monoid_algebra k G) M`,
rather than on `M` itself.
-/
noncomputable def ofModule : Representation k G (RestrictScalars k (MonoidAlgebra k G) M) :=
  (MonoidAlgebra.lift k G
        (RestrictScalars k (MonoidAlgebra k G) M →ₗ[k]
          RestrictScalars k (MonoidAlgebra k G) M)).symm
    (RestrictScalars.lsmul k (MonoidAlgebra k G) M)
#align representation.of_module Representation.ofModule

/-!
## `of_module` and `as_module` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalence_Module_monoid_algebra` for the full statement.

Starting with `ρ : representation k G V`, converting to a module and back again
we have a `representation k G (restrict_scalars k (monoid_algebra k G) ρ.as_module)`.
To compare these, we use the composition of `restrict_scalars_add_equiv` and `ρ.as_module_equiv`.

Similarly, starting with `module (monoid_algebra k G) M`,
after we convert to a representation and back to a module,
we have `module (monoid_algebra k G) (restrict_scalars k (monoid_algebra k G) M)`.
-/


@[simp]
theorem ofModule_asAlgebraHom_apply_apply (r : MonoidAlgebra k G)
    (m : RestrictScalars k (MonoidAlgebra k G) M) :
    ((ofModule k G M).asAlgebraHom r) m =
      (RestrictScalars.addEquiv _ _ _).symm (r • RestrictScalars.addEquiv _ _ _ m) :=
  by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule, AddEquiv.apply_eq_iff_eq,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul, LinearMap.add_apply]
  · intro r f w
    simp only [w, AlgHom.map_smul, LinearMap.smul_apply,
      RestrictScalars.addEquiv_symm_map_smul_smul]
#align representation.of_module_as_algebra_hom_apply_apply Representation.ofModule_asAlgebraHom_apply_apply

@[simp]
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k (MonoidAlgebra k G) ρ.AsModule) :
    ofModule k G ρ.AsModule g x =
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) :=
  by
  apply_fun RestrictScalars.addEquiv _ _ ρ.as_module using
    (RestrictScalars.addEquiv _ _ _).Injective
  dsimp [of_module, RestrictScalars.lsmul_apply_apply]
  simp
#align representation.of_module_as_module_act Representation.ofModule_asModule_act

theorem smul_ofModule_asModule (r : MonoidAlgebra k G) (m : (ofModule k G M).AsModule) :
    (RestrictScalars.addEquiv _ _ _) ((ofModule k G M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv _ _ _) ((ofModule k G M).asModuleEquiv m) :=
  by
  dsimp
  simp only [AddEquiv.apply_symm_apply, of_module_as_algebra_hom_apply_apply]
#align representation.smul_of_module_as_module Representation.smul_ofModule_asModule

end

end MonoidAlgebra

section AddCommGroup

variable {k G V : Type _} [CommRing k] [Monoid G] [I : AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

instance : AddCommGroup ρ.AsModule :=
  I

end AddCommGroup

section MulAction

variable (k : Type _) [CommSemiring k] (G : Type _) [Monoid G] (H : Type _) [MulAction G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def ofMulAction : Representation k G (H →₀ k)
    where
  toFun g := Finsupp.lmapDomain k k ((· • ·) g)
  map_one' := by
    ext (x y)
    dsimp
    simp
  map_mul' x y := by
    ext (z w)
    simp [mul_smul]
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

variable {k G V : Type _} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

@[simp]
theorem ofMulAction_apply {H : Type _} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulAction k G H g f h = f (g⁻¹ • h) :=
  by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change of_mul_action k G H g f (g • h') = f h'
  have hg : Function.Injective ((· • ·) g : H → H) :=
    by
    intro h₁ h₂
    simp
  simp only [of_mul_action_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]
#align representation.of_mul_action_apply Representation.ofMulAction_apply

theorem ofMulAction_self_smul_eq_mul (x : MonoidAlgebra k G) (y : (ofMulAction k G G).AsModule) :
    x • y = (x * y : MonoidAlgebra k G) :=
  x.inductionOn (fun g => by show as_algebra_hom _ _ _ = _ <;> ext <;> simp)
    (fun x y hx hy => by simp only [hx, hy, add_mul, add_smul]) fun r x hx => by
    show as_algebra_hom _ _ _ = _ <;> simpa [← hx]
#align representation.of_mul_action_self_smul_eq_mul Representation.ofMulAction_self_smul_eq_mul

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
noncomputable def ofMulActionSelfAsModuleEquiv :
    (ofMulAction k G G).AsModule ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G :=
  { asModuleEquiv _ with map_smul' := ofMulAction_self_smul_eq_mul }
#align representation.of_mul_action_self_as_module_equiv Representation.ofMulActionSelfAsModuleEquiv

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ
#align representation.as_group_hom Representation.asGroupHom

theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [as_group_hom, MonoidHom.coe_toHomUnits]
#align representation.as_group_hom_apply Representation.asGroupHom_apply

end Group

section TensorProduct

variable {k G V W : Type _} [CommSemiring k] [Monoid G]

variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : Representation k G (V ⊗[k] W)
    where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]
#align representation.tprod Representation.tprod

-- mathport name: «expr ⊗ »
local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl
#align representation.tprod_apply Representation.tprod_apply

theorem smul_tprod_one_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    (r • x ⊗ₜ y : (ρV.tprod 1).AsModule) = (r • x : ρV.AsModule) ⊗ₜ y :=
  by
  show as_algebra_hom _ _ _ = as_algebra_hom _ _ _ ⊗ₜ _
  simp only [as_algebra_hom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  rfl
#align representation.smul_tprod_one_as_module Representation.smul_tprod_one_asModule

theorem smul_one_tprod_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    (r • x ⊗ₜ y : ((1 : Representation k G V).tprod ρW).AsModule) = x ⊗ₜ (r • y : ρW.AsModule) :=
  by
  show as_algebra_hom _ _ _ = _ ⊗ₜ as_algebra_hom _ _ _
  simp only [as_algebra_hom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
#align representation.smul_one_tprod_as_module Representation.smul_one_tprod_asModule

end TensorProduct

section LinearHom

variable {k G V W : Type _} [CommSemiring k] [Group G]

variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W)
    where
  toFun g :=
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' :=
    LinearMap.ext fun x => by
      simp_rw [coe_mk, inv_one, map_one, one_apply, one_eq_id, comp_id, id_comp]
  map_mul' g h :=
    LinearMap.ext fun x => by
      simp_rw [coe_mul, coe_mk, Function.comp_apply, mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]
#align representation.lin_hom Representation.linHom

@[simp]
theorem linHom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl
#align representation.lin_hom_apply Representation.linHom_apply

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : Representation k G (Module.Dual k V)
    where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' := fun r f => by
        ext
        simp only [coe_comp, Function.comp_apply, smul_apply, RingHom.id_apply] }
  map_one' := by
    ext
    simp only [coe_comp, Function.comp_apply, map_one, inv_one, coe_mk, one_apply]
  map_mul' g h := by
    ext
    simp only [coe_comp, Function.comp_apply, mul_inv_rev, map_mul, coe_mk, mul_apply]
#align representation.dual Representation.dual

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (ρV g⁻¹) :=
  rfl
#align representation.dual_apply Representation.dual_apply

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `linear_algebra.contraction.dual_tensor_hom`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on  $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W :=
  by ext; simp [Module.Dual.transpose_apply]
#align representation.dual_tensor_hom_comm Representation.dualTensorHom_comm

end LinearHom

end Representation

