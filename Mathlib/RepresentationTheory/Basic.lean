/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Basic

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
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `MonoidAlgebra k G`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `MonoidAlgebra k G-module `M`
`M.ofModule` is the associociated representation seen as a homomorphism.
-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is a homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivial

variable (k : Type*) {G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The trivial representation of `G` on a `k`-module V.
-/
def trivial : Representation k G V :=
  1

-- Porting note: why is `V` implicit
theorem trivial_def (g : G) (v : V) : trivial k (V := V) g v = v :=
  rfl

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

theorem asAlgebraHom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl

@[simp]
theorem asAlgebraHom_single (g : G) (r : k) : asAlgebraHom ρ (Finsupp.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by simp

theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

/-- If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module (MonoidAlgebra k G) ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
@[nolint unusedArguments]
def asModule (_ : Representation k G V) :=
  V

-- Porting note: no derive handler
instance : AddCommMonoid (ρ.asModule) := inferInstanceAs <| AddCommMonoid V

instance : Inhabited ρ.asModule where
  default := 0

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `MonoidAlgebra k G`.
-/
noncomputable instance asModuleModule : Module (MonoidAlgebra k G) ρ.asModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

-- Porting note: ρ.asModule doesn't unfold now
instance : Module k ρ.asModule := inferInstanceAs <| Module k V

/-- The additive equivalence from the `Module (MonoidAlgebra k G)` to the original vector space
of the representative.

This is just the identity, but it is helpful for typechecking and keeping track of instances.
-/
def asModuleEquiv : ρ.asModule ≃+ V :=
  AddEquiv.refl _

@[simp]
theorem asModuleEquiv_map_smul (r : MonoidAlgebra k G) (x : ρ.asModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl

@[simp]
theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k (MonoidAlgebra k G) r • ρ.asModuleEquiv.symm x := by
  apply_fun ρ.asModuleEquiv
  simp

@[simp]
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  apply_fun ρ.asModuleEquiv
  simp

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
    simp only [w, map_smul, LinearMap.smul_apply, RestrictScalars.addEquiv_symm_map_smul_smul]

@[simp]
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k (MonoidAlgebra k G) ρ.asModule) :
    ofModule (k := k) (G := G) ρ.asModule g x = -- Porting note: more help with implicit
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  apply_fun RestrictScalars.addEquiv _ _ ρ.asModule using
    (RestrictScalars.addEquiv _ _ ρ.asModule).injective
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp

theorem smul_ofModule_asModule (r : MonoidAlgebra k G) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

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

variable {k G H}

theorem ofMulAction_def (g : G) : ofMulAction k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl

theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

end MulAction
section DistribMulAction

variable (k G A : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid A] [Module k A]
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

@[simp] theorem ofMulDistribMulAction_apply_apply (g : M) (a : Additive G) :
    ofMulDistribMulAction M G g a = Additive.ofMul (g • Additive.toMul a) := rfl

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

-- Porting note: did not need this in ML3; noncomputable because IR check complains
noncomputable instance :
    HMul (MonoidAlgebra k G) ((ofMulAction k G G).asModule) (MonoidAlgebra k G) :=
  inferInstanceAs <| HMul (MonoidAlgebra k G) (MonoidAlgebra k G) (MonoidAlgebra k G)

theorem ofMulAction_self_smul_eq_mul (x : MonoidAlgebra k G) (y : (ofMulAction k G G).asModule) :
    x • y = (x * y : MonoidAlgebra k G) := -- by
  -- Porting note: trouble figuring out the motive
  x.induction_on (p := fun z => z • y = z * y)
    (fun g => by
      show asAlgebraHom (ofMulAction k G G) _ _ = _; ext
      simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul,
        ofMulAction_apply, smul_eq_mul]
      -- Porting note: single_mul_apply not firing in simp
      rw [MonoidAlgebra.single_mul_apply, one_mul]
    )
    (fun x y hx hy => by simp only [hx, hy, add_mul, add_smul]) fun r x hx => by
    show asAlgebraHom (ofMulAction k G G) _ _ = _  -- Porting note: was simpa [← hx]
    simp only [map_smul, smul_apply, Algebra.smul_mul_assoc]
    rw [← hx]
    rfl

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
noncomputable def ofMulActionSelfAsModuleEquiv :
    (ofMulAction k G G).asModule ≃ₗ[MonoidAlgebra k G] MonoidAlgebra k G :=
  { asModuleEquiv _ with map_smul' := ofMulAction_self_smul_eq_mul }

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ

theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

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
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

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

theorem smul_one_tprod_asModule (r : MonoidAlgebra k G) (x : V) (y : W) :
    -- Porting note: required to since Lean 4 doesn't unfold asModule
    let y' : ρW.asModule := y
    let z : (1 ⊗ ρW).asModule := x ⊗ₜ y
    r • z = x ⊗ₜ (r • y') := by
  show asAlgebraHom (1 ⊗ ρW) _ _ = _ ⊗ₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

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
      dsimp -- Porting note (#11227):now needed
      simp_rw [inv_one, map_one, one_eq_id, comp_id, id_comp]
  map_mul' g h :=
    LinearMap.ext fun x => by
      dsimp -- Porting note (#11227):now needed
      simp_rw [mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]

@[simp]
theorem linHom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

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
    dsimp -- Porting note (#11227):now needed
    simp only [coe_comp, Function.comp_apply, map_one, inv_one, coe_mk, one_apply]
  map_mul' g h := by
    ext
    dsimp -- Porting note (#11227):now needed
    simp only [coe_comp, Function.comp_apply, mul_inv_rev, map_mul, coe_mk, mul_apply]

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `LinearAlgebra.Contraction.dualTensorHom`).
Given representations of $G$ on $V$ and $W$,there are representations of $G$ on $V^* ⊗ W$ and on
$Hom_k(V, W)$.
This lemma says that $φ$ is $G$-linear.
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W := by
  ext; simp [Module.Dual.transpose_apply]

end LinearHom

end Representation
