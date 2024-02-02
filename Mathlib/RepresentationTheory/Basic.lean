/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
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
section Hom

structure Hom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V]
    [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    extends V →ₗ[k] W where
  comm_apply' : ∀ g x, toFun (ρ g x) = τ g (toFun x)

end Hom
namespace Hom

variable {k G V W Z : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
  (ρ : Representation k G V) (τ : Representation k G W) (η : Representation k G Z)

@[ext] lemma ext {f g : ρ.Hom τ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases' f; simp_all only

variable {ρ τ η}

instance : LinearMapClass (Hom ρ τ) k V W where
  coe := fun f => f.1
  coe_injective' := fun f g hfg => by ext; exact Function.funext_iff.1 hfg _
  map_add := fun f x y => f.1.map_add _ _
  map_smulₛₗ := fun f r x => f.1.map_smul _ _

def Simps.apply (e : ρ.Hom τ) : V → W := e

initialize_simps_projections Hom (toFun → apply)

@[simp]
theorem toFun_eq_coe (f : ρ.Hom τ) : f.toFun = f :=
  rfl

attribute [coe] Hom.toLinearMap

instance coeOutLinearMap : CoeOut (ρ.Hom τ) (V →ₗ[k] W) :=
  ⟨Hom.toLinearMap⟩

@[coe]
def toAddMonoidHom' (f : ρ.Hom τ) : V →+ W := (f : V →ₗ[k] W)

instance coeOutAddMonoidHom : CoeOut (ρ.Hom τ) (V →+ W) :=
  ⟨Hom.toAddMonoidHom'⟩

@[simp] theorem coe_mk {f : V →ₗ[k] W} (h) : ((⟨f, h⟩ : ρ.Hom τ) : V → W) = f := rfl

@[norm_cast]
theorem coe_mks {f : V → W} (h₁ h₂ h₃) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : ρ.Hom τ) = f := rfl

@[simp, norm_cast]
theorem coe_linearMap_mk {f : V →ₗ[k] W} (h) : ((⟨f, h⟩ : ρ.Hom τ) : V →ₗ[k] W) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem toLinearMap_eq_coe (f : ρ.Hom τ) : f.toLinearMap = f := rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : ρ.Hom τ) : ⇑(f : V →ₗ[k] W) = f := rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : ρ.Hom τ) : ⇑(f : V →+ W) = f := rfl

@[simp] lemma comm_apply (f : ρ.Hom τ) (g : G) (x : V) :
    f (ρ g x) = τ g (f x) := f.comm_apply' g x

@[simp] theorem comm (f : ρ.Hom τ) (g : G) : (f : V →ₗ[k] W) ∘ₗ ρ g = τ g ∘ₗ (f : V →ₗ[k] W) := by
  ext; exact f.comm_apply' g _

@[simps! apply] def comp (f : ρ.Hom τ) (g : τ.Hom η) : ρ.Hom η where
  toLinearMap := g.1.comp f.1
  comm_apply' := fun _ _ => by simp only [AddHom.toFun_eq_coe, coe_toAddHom, coe_comp,
    coe_toLinearMap, Function.comp_apply, comm_apply]

variable (ρ)

@[simps! apply] def id : ρ.Hom ρ where
  toLinearMap := LinearMap.id
  comm_apply' := fun _ _ => by simp only [AddHom.toFun_eq_coe, coe_toAddHom, id_coe, id_eq]

instance : AddCommMonoid (Hom ρ τ) where
  add := fun f g => {
    toLinearMap := f.1 + g.1
    comm_apply' := sorry
  }
  add_assoc := sorry
  zero := {
    toLinearMap := 0
    comm_apply' := sorry
  }
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry

instance : Module k (Hom ρ τ) where
  smul := fun r x => {
    toLinearMap := r • x.1
    comm_apply' := sorry
  }
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

end Hom
section Iso

structure Iso {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V]
    [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (τ : Representation k G W)
    extends V ≃ W, V ≃+ W, V ≃ₗ[k] W where
  protected comm_apply' : ∀ g x, toFun (ρ g x) = τ g (toFun x)

end Iso
namespace Iso

variable {k G V W Z : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
  {ρ : Representation k G V} {τ : Representation k G W} {η : Representation k G Z}

instance : EquivLike (ρ.Iso τ) V W where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f,_⟩,_⟩ := f
    obtain ⟨⟨g,_⟩,_⟩ := g
    congr

def Simps.apply (e : ρ.Iso τ) : V → W := e

def Simps.toEquiv (e : ρ.Iso τ) : V ≃ W := e

@[ext] lemma ext {f g : ρ.Iso τ} (h : ∀ x, f x = g x) : f = g := by
    cases' f with f _ _ _
    cases' g with g _ _ _
    simpa only [mk.injEq, Equiv.ext_iff] using h

instance : LinearEquivClass (Iso ρ τ) k V W where
  coe := fun f => f.1
  inv := fun f => f.1.2
  left_inv := fun f => f.1.3
  right_inv := fun f => f.1.4
  coe_injective' := fun f g hfg _ => by ext; exact congr_fun hfg _
  map_add := fun f => f.2
  map_smulₛₗ := fun f => f.3

@[simp] lemma comm_apply (f : ρ.Iso τ) (g : G) (x : V) :
    f (ρ g x) = τ g (f x) := f.comm_apply' _ _

instance hasCoeToLinearEquiv : CoeOut (ρ.Iso τ) (V ≃ₗ[k] W) :=
  ⟨Iso.toLinearEquiv⟩

@[simp]
theorem coe_mk {toFun invFun left_inv right_inv map_add map_smul comm_apply'} :
    ⇑(⟨⟨toFun, invFun, left_inv, right_inv⟩, map_add, map_smul, comm_apply'⟩ : ρ.Iso τ) = toFun :=
  rfl

variable (e : ρ.Iso τ)

@[simp]
theorem mk_coe (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : ρ.Iso τ) = e := by
  ext; rfl

@[simp] theorem toEquiv_eq_coe : e.toEquiv = e := rfl

@[simp] theorem toRingEquiv_eq_coe : e.toLinearEquiv = e := rfl

@[simp]
lemma toLinearEquiv_toLinearMAp : ((e : V ≃ₗ[k] W) : V →ₗ[k] W) = e :=
  rfl

@[simp]
theorem coe_linearEquiv : ((e : V ≃ₗ[k] W) : V → W) = e := rfl

theorem coe_linearEquiv' : (e.toLinearEquiv : V → W) = e := rfl

theorem coe_linearEquiv_injective : Function.Injective ((↑) : ρ.Iso τ → V ≃ₗ[k] W) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h

protected theorem map_add : ∀ x y, e (x + y) = e x + e y := map_add e
protected theorem map_zero : e 0 = 0 := map_zero e
protected theorem map_smul : ∀ (r : k) x, e (r • x) = r • e x := map_smul e

open BigOperators
@[deprecated map_sum]
nonrec theorem map_sum {ι : Type*} (f : ι → V) (s : Finset ι) :
    e (∑ x in s, f x) = ∑ x in s, e (f x) := map_sum e f s

theorem map_finsupp_sum {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → V) :
    e (f.sum g) = f.sum fun i b => e (g i b) := e.map_sum _ _

@[coe] def toHom : ρ.Hom τ :=
  { e with
    comm_apply' := e.comm_apply' }

--@[simp] theorem toHom_eq_coe : e = e :=

@[simp, norm_cast]
theorem coe_hom : DFunLike.coe (e.toHom) = DFunLike.coe e := rfl

-- the coe doesn't work ?
@[simp, norm_cast]
lemma toHom_toLinearMap : (e.toHom : V →ₗ[k] W) = e := rfl

theorem coe_linearMap_commutes : (e.toHom : V →ₗ[k] W) = ((e : V ≃ₗ[k] W) : V →ₗ[k] W) :=
  rfl

variable (ρ)

@[refl]
def refl : ρ.Iso ρ :=
  { (1 : V ≃ₗ[k] V) with comm_apply' := fun _ _ => rfl }

instance : Inhabited (ρ.Iso ρ) := ⟨refl ρ⟩

@[simp]
theorem refl_toHom : (refl ρ).toHom = Hom.id ρ := rfl

@[simp]
theorem coe_refl : ⇑(refl ρ) = _root_.id := rfl

@[symm]
def symm : τ.Iso ρ :=
  { e.toLinearEquiv.symm with
    comm_apply' := fun g x => by sorry }

/-- See Note [custom simps projection] -/
def Simps.symm_apply : W → V := e.symm

initialize_simps_projections Iso (toFun → apply, invFun → symm_apply)

end Iso
section trivial

variable (k : Type*) {G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1
#align representation.trivial Representation.trivial

-- Porting note: why is `V` implicit
theorem trivial_def (g : G) (v : V) : trivial k (V := V) g v = v :=
  rfl
#align representation.trivial_def Representation.trivial_def

variable {k}

/-- A predicate for representations that fix every element. -/
class IsTrivial (ρ : Representation k G V) : Prop where
  out : ∀ g x, ρ g x = x := by aesop

instance : IsTrivial (trivial k (G := G) (V := V)) where

@[simp] theorem apply_eq_self
    (ρ : Representation k G V) (g : G) (x : V) [h : IsTrivial ρ] :
    ρ g x = x := h.out g x

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
#align representation.as_algebra_hom_single Representation.asAlgebraHom_single

theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by simp
#align representation.as_algebra_hom_single_one Representation.asAlgebraHom_single_one

theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]
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
  simp
#align representation.as_module_equiv_symm_map_smul Representation.asModuleEquiv_symm_map_smul

@[simp]
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  apply_fun ρ.asModuleEquiv
  simp
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
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k (MonoidAlgebra k G) ρ.asModule) :
    ofModule (k := k) (G := G) ρ.asModule g x = -- Porting note: more help with implicit
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  apply_fun RestrictScalars.addEquiv _ _ ρ.asModule using
    (RestrictScalars.addEquiv _ _ ρ.asModule).injective
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp
#align representation.of_module_as_module_act Representation.ofModule_asModule_act

theorem smul_ofModule_asModule (r : MonoidAlgebra k G) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]
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
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    dsimp
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]
#align representation.of_mul_action Representation.ofMulAction

variable {k G H}

theorem ofMulAction_def (g : G) : ofMulAction k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl
#align representation.of_mul_action_def Representation.ofMulAction_def

@[simp] theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single
#align representation.of_mul_action_single Representation.ofMulAction_single

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
noncomputable def leftRegular : Representation k G (G →₀ k) :=
  ofMulAction k G G

section

variable {A : Type*} [AddCommMonoid A] [Module k A] (ρ : Representation k G A)
#exit
@[simps! toLinearMap] noncomputable def leftRegularHom (x : A) :
    (Representation.ofMulAction k G G).Hom ρ where
  toLinearMap := Finsupp.lift _ _ _ fun g => ρ g x
  comm := fun g => Finsupp.lhom_ext' fun y =>
    LinearMap.ext_ring <| by
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
        Finsupp.lift_apply, Representation.ofMulAction_single (G := G),
        Finsupp.sum_single_index, zero_smul, one_smul, smul_eq_mul, ρ.map_mul]
      rfl

theorem leftRegularHom_Hom_single (x : A) :
    (leftRegularHom ρ x).1 (Finsupp.single 1 1) = x := by
  simp only [leftRegularHom_toLinearMap, Finsupp.lift_apply, map_one, one_apply, zero_smul,
    Finsupp.sum_single_index, one_smul]

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv : (ofMulAction k G G).Hom ρ ≃ₗ[k] A where
  toFun f := f.1 (Finsupp.single 1 1)
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun x := leftRegularHom ρ x
  left_inv f := Hom.ext _ _ <| Finsupp.lhom_ext' fun x : G => LinearMap.ext_ring <| by
    simp only [leftRegularHom_toLinearMap, ← Hom.comm_apply, ofMulAction_single, smul_eq_mul, mul_one,
      coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Finsupp.lift_apply, zero_smul,
      Finsupp.sum_single_index, one_smul]
  right_inv x := leftRegularHom_Hom_single _ x


end
/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
noncomputable def diagonal (n : ℕ) : Representation k G ((Fin n → G) →₀ k) :=
  ofMulAction k G (Fin n → G)

end MulAction
section DistribMulAction

variable (k G A : Type*) [CommSemiring k] [Monoid G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Representation k G A where
  toFun := fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

variable {k G A}

@[simp] theorem ofDistribMulAction_apply_apply (g : G) (a : A) :
    ofDistribMulAction k G A g a = g • a := rfl

end DistribMulAction
section MulDistribMulAction
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Representation ℤ M (Additive G) :=
  (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) →* _).comp
    ((monoidEndToAdditive G : _ →* _).comp (MulDistribMulAction.toMonoidEnd M G))

@[simp] theorem ofMulDistribMulAction_apply_apply (g : M) (a : G) :
    ofMulDistribMulAction M G g a = g • a := rfl

end MulDistribMulAction
section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

@[simp]
theorem ofMulAction_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulAction k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulAction k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulAction_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]
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
      simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul,
        ofMulAction_apply, smul_eq_mul]
      -- Porting note : single_mul_apply not firing in simp
      rw [MonoidAlgebra.single_mul_apply, one_mul])
    (fun x y hx hy => by simp only [hx, hy, add_mul, add_smul]) fun r x hx => by
    show asAlgebraHom (ofMulAction k G G) _ _ = _  -- Porting note: was simpa [← hx]
    simp only [map_smul, smul_apply, Algebra.smul_mul_assoc]
    rw [← hx]
    rfl
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
noncomputable def tprod : Representation k G (V ⊗[k] W) where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [_root_.map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [_root_.map_mul, TensorProduct.map_mul]
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
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  rfl
#align representation.smul_tprod_one_as_module Representation.smul_tprod_one_asModule

theorem smul_one_tprod_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let y' : ρW.asModule := y
    let z : (1 ⊗ ρW).asModule := x ⊗ₜ y
    r • z = x ⊗ₜ (r • y') := by
  show asAlgebraHom (1 ⊗ ρW) _ _ = _ ⊗ₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
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
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' :=
    LinearMap.ext fun x => by
      dsimp -- Porting note: now needed
      simp_rw [inv_one, map_one, one_eq_id, comp_id, id_comp]
  map_mul' g h :=
    LinearMap.ext fun x => by
      dsimp -- Porting note: now needed
      simp_rw [mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]
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
      map_smul' := fun r f => by
        ext
        simp only [coe_comp, Function.comp_apply, smul_apply, RingHom.id_apply] }
  map_one' := by
    ext
    dsimp -- Porting note: now needed
    simp only [coe_comp, Function.comp_apply, map_one, inv_one, coe_mk, one_apply]
  map_mul' g h := by
    ext
    dsimp -- Porting note: now needed
    simp only [coe_comp, Function.comp_apply, mul_inv_rev, map_mul, coe_mk, mul_apply]
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
#align representation.dual_tensor_hom_comm Representation.dualTensorHom_comm

end LinearHom
end Representation

@[simp] lemma Finsupp.finsuppProdLEquiv_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α × β) (m : M) :
  Finsupp.finsuppProdLEquiv R (Finsupp.single a m) = Finsupp.single a.1 (Finsupp.single a.2 m) := by
  show Finsupp.curry _ = _
  simp only [Finsupp.curry, single_zero, sum_single_index]

@[simp] lemma Finsupp.finsuppProdLEquiv_symm_single_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α) (b : β) (m : M) :
  (Finsupp.finsuppProdLEquiv R).symm (Finsupp.single a (Finsupp.single b m))
    = Finsupp.single (a, b) m := by
  show Finsupp.uncurry _ = _
  simp only [Finsupp.uncurry, sum_zero_index, sum_single_index, single_zero]

@[simp] lemma Finsupp.finsuppTensorFinsupp'_symm_single {S : Type*} [CommRing S] {α β : Type*}
    (x : α × β) (r : S) :
  (finsuppTensorFinsupp' S α β).symm (Finsupp.single x r)
    = r • TensorProduct.tmul S (Finsupp.single x.1 1) (Finsupp.single x.2 1) := by
  rw [finsuppTensorFinsupp']
  simp only [LinearEquiv.trans_symm, Finsupp.lcongr_symm, Equiv.refl_symm, LinearEquiv.trans_apply,
    Finsupp.lcongr_single, Equiv.refl_apply, TensorProduct.lid_symm_apply,
    finsuppTensorFinsupp_symm_single]
  rw [← Finsupp.smul_single_one x.2, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

namespace Representation
noncomputable section

variable {k G : Type*} [CommRing k] [Group G] {α A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)
-- maybe no one care.
/-def Representation.dfinsupp [DecidableEq α] (F : α → Rep k G) :
    Representation k G (DFinsupp (fun a => F a)) where
      toFun := fun g => DFinsupp.lsum k fun i => (DFinsupp.lsingle i).comp ((F i).ρ g)
      map_one' := by
        refine DFinsupp.lhom_ext (fun i x => ?_)
        simp only [MonCat.one_of, map_one, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_single,
          LinearMap.toAddMonoidHom_coe, End.one_def]
        rfl
      map_mul' := fun g h => by
        refine DFinsupp.lhom_ext (fun i x => ?_)
        simp only [map_mul, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_single,
          LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mul_apply, DFinsupp.lsingle_apply]-/

@[simps] def finsupp (α : Type*) :
    Representation k G (α →₀ A) where
      toFun := fun g => Finsupp.lsum k fun i => (Finsupp.lsingle i).comp (ρ g)
      map_one' := Finsupp.lhom_ext (fun i x => by simp)
      map_mul' := fun g h => Finsupp.lhom_ext (fun i x => by simp)

lemma finsupp_single (g : G) (x : α) (a : A) :
    ρ.finsupp α g (Finsupp.single x a) = Finsupp.single x (ρ g a) := by
  simp only [finsupp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Function.comp_apply, map_zero,
    Finsupp.sum_single_index, Finsupp.lsingle_apply]

@[simps! toLinearMap] def lsingle {α : Type*} (a : α) :
  ρ.Hom (ρ.finsupp α) where
    toLinearMap := Finsupp.lsingle a
    comm := fun g => by simp only [finsupp_apply, Finsupp.lsum_comp_lsingle]

def free (k G : Type*) [CommRing k] [Group G] (α : Type*) :
    Representation k G (α →₀ G →₀ k) :=
  finsupp (ofMulAction k G G) α

@[simps! toLinearMap] def finsuppHom {β : Type*} (f : α → β) :
    (finsupp ρ α).Hom (finsupp ρ β) where
  toLinearMap := Finsupp.lmapDomain A k f
  comm := fun g => Finsupp.lhom_ext fun i x => by
    simp only [finsupp_apply, LinearMap.coe_comp, Finsupp.coe_lsum, Function.comp_apply, map_zero,
      Finsupp.sum_single_index, Finsupp.lsingle_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

def freeHom {β : Type*} (f : α → β) :
    (free k G α).Hom (free k G β) := finsuppHom _ f

@[simp] lemma free_ρ_single_single (g h : G) (i : α) (r : k) :
    free k G α g (Finsupp.single i (Finsupp.single h r)) =
      Finsupp.single i (Finsupp.single (g * h) r) := by
  unfold free
  rw [finsupp_single]
  simp only [leftRegular, ofMulAction_single, smul_eq_mul]

@[simps! toLinearMap] def freeLift (f : α → A) :
    (free k G α).Hom ρ where
  toLinearMap := Finsupp.total (α × G) A k
    (fun x => ρ x.2 (f x.1)) ∘ₗ (Finsupp.finsuppProdLEquiv
      (α := α) (β := G) k (M := k)).symm.toLinearMap
  comm := fun g =>
    Finsupp.lhom_ext' fun i => Finsupp.lhom_ext fun j y => by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Finsupp.lsingle_apply, free_ρ_single_single, Finsupp.finsuppProdLEquiv_symm_single_single,
        Finsupp.total_single, map_mul, LinearMap.mul_apply, map_smul]

lemma freeLift_Hom_single_single (f : α → A) (i : α)
    (g : G) (r : k) :
    (freeLift ρ f).1 (Finsupp.single i (Finsupp.single g r)) = r • ρ g (f i) := by
  simp only [freeLift_toLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.total_single]

@[simps] def freeLiftEquiv (α : Type*) :
    ((free k G α).Hom ρ) ≃ₗ[k] (α → A) where
      toFun := fun f i => f.1 (Finsupp.single i (Finsupp.single 1 1))
      invFun := freeLift ρ
      left_inv := fun x => Hom.ext _ _ <| Finsupp.lhom_ext' fun i =>
        Finsupp.lhom_ext fun j y => by
        simp_rw [freeLift_toLinearMap, ← Hom.comm_apply, free_ρ_single_single, mul_one,
          LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.lsingle_apply,
          Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.total_single,
          ← Finsupp.smul_single_one j y, ← Finsupp.smul_single, map_smul]
      right_inv := fun x => by
        ext i
        simp_rw [freeLift_Hom_single_single, one_smul, map_one]
        rfl
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl

lemma free_ext (f g : (free k G α).Hom ρ)
  (h : ∀ i : α, f.1 (Finsupp.single i (Finsupp.single 1 1))
    = g.1 (Finsupp.single i (Finsupp.single 1 1))) : f = g :=
  (freeLiftEquiv ρ α).injective (Function.funext_iff.2 h)

-- ugh this isn't a sustainable approach
lemma freeLiftEquiv_naturality {β : Type*}
    (f : α → β) (g : β → A) :
    (freeLiftEquiv ρ α).symm (g ∘ f) = (freeHom f).comp ((freeLiftEquiv ρ β).symm g) :=
  free_ext ρ _ _ fun i => by
    simp only [freeLiftEquiv_symm_apply, freeLift_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.total_single,
      map_one, LinearMap.one_apply, one_smul, freeHom, Hom.comp_toLinearMap, finsuppHom_toLinearMap,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable (k G α)

def tprodIsoFree :
    ((ofMulAction k G G).tprod (trivial k (G := G) (V := α →₀ k))).Iso (free k G α) :=
  Iso.mk' (finsuppTensorFinsupp' k G α
      ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
      Finsupp.finsuppProdLEquiv k) fun g => TensorProduct.ext <| Finsupp.lhom_ext fun i x =>
    Finsupp.lhom_ext fun j y => by
      simp only [tprod_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul, ofMulAction_single,
        smul_eq_mul, apply_eq_self, LinearEquiv.trans_apply,
        finsuppTensorFinsupp'_single_tmul_single, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single, Equiv.prodComm_apply, Prod.swap_prod_mk,
        Finsupp.finsuppProdLEquiv_single, free_ρ_single_single]

lemma tprodIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
    (tprodIsoFree k G α).symm.1 (Finsupp.single i (Finsupp.single g r)) =
      TensorProduct.tmul k (Finsupp.single g r) (Finsupp.single i 1) := by
  simp? [tprodIsoFree, Iso.symm_mk']
  /-simp? [tprodIsoFree]
  simp only [tprodIsoFree, Iso.mk', LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm,
    Finsupp.domLCongr_symm, Equiv.prodComm_symm, LinearEquiv.mk_coe, LinearEquiv.trans_apply,
    Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Finsupp.finsuppTensorFinsupp'_symm_single, TensorProduct.smul_tmul', Finsupp.smul_single_one]-/

@[simp] lemma tprodIsoFree_Hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
    (tprodIsoFree k G α).toLinearEquiv (Finsupp.single g r ⊗ₜ Finsupp.single i s)
      = Finsupp.single i (Finsupp.single g (r * s)) := by
  sorry
  /-simp only [tprodIsoFree, Iso.mk', LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm,
    Finsupp.domLCongr_symm, Equiv.prodComm_symm, LinearEquiv.mk_coe, LinearEquiv.trans_apply,
    finsuppTensorFinsupp'_single_tmul_single, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Finsupp.finsuppProdLEquiv_single]-/

variable {k G}
variable {C : Type*} [AddCommGroup C] [Module k C] (η : Representation k G C)

def homEquiv : (ρ.tprod τ).Hom η ≃ τ.Hom (ρ.linHom η) where
  toFun f :=
    { toLinearMap := (TensorProduct.curry f.toLinearMap).flip
      comm := fun g => by
        refine' LinearMap.ext fun x => LinearMap.ext fun y => _
        simp only [coe_comp, Function.comp_apply, flip_apply, TensorProduct.curry_apply,
          linHom_apply, ← Hom.comm_apply, tprod_apply, TensorProduct.map_tmul, ← mul_apply, ←
          map_mul, mul_right_inv, map_one, one_apply] }
  invFun f := {
    toLinearMap := TensorProduct.uncurry k _ _ _ f.toLinearMap.flip
    comm := fun g => TensorProduct.ext' fun x y => by
      simp only [tprod_apply, coe_comp, Function.comp_apply, TensorProduct.map_tmul,
        TensorProduct.uncurry_apply, flip_apply, Hom.comm_apply, linHom_apply, ← mul_apply, ←
        map_mul, mul_left_inv, map_one, one_apply] }
  left_inv f := Hom.ext _ _ <| TensorProduct.ext' fun _ _ => rfl
  right_inv f := by ext; rfl

end
end Representation
