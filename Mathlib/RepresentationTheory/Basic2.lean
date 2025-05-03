/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * `Representation`
  * `Representation.tprod`
  * `Representation.linHom`
  * `Representation.dual`

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `MonoidAlgebra k G`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `MonoidAlgebra k G`-module `M`,
`M.ofModule` is the associociated representation seen as a homomorphism.
-/


open MonoidAlgebra (lift single)

/-- A representation of `G` on the `k`-module `V` is TODO. -/
class Representation (R G V : Type*)
    [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V] [DistribMulAction G V]
    extends Module (MonoidAlgebra R G) V,
      SMulCommClass R G V, IsScalarTower R (MonoidAlgebra R G) V where
  single_one_smul (R) : ∀ g : G, ∀ v : V, single g (1:R) • v = g • v

namespace Representation

variable (R G V W : Type*)
variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid V] [Module R V] [DistribMulAction G V] [Representation R G V]
variable [AddCommMonoid W] [Module R W] [DistribMulAction G W] [Representation R G W]

instance : SMulCommClass G R V := SMulCommClass.symm R G V

@[simp]
protected lemma single_smul (g : G) (r : R) (v : V) :
    single g r • v = g • r • v := by
  rw [smul_comm g, ← single_one_smul R g v, ← smul_assoc, MonoidAlgebra.smul_single', mul_one]

instance : SMulCommClass R (MonoidAlgebra R G) V where
  smul_comm x y v := by apply y.induction_on <;> simp [smul_comm x]

instance : SMulCommClass (MonoidAlgebra R G) R V := SMulCommClass.symm R (MonoidAlgebra R G) V

noncomputable
def mk_of_action (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    [DistribMulAction G V] [SMulCommClass k G V] [SMulCommClass G k V] :
    Representation k G V where
  smul x := lift k G (Module.End k V) (DistribMulAction.toModuleEnd k V) x
  one_smul v := by simp [(· • ·)]
  mul_smul := by simp [(· • ·)]
  smul_zero := by simp [(· • ·)]
  smul_add := by simp [(· • ·)]
  add_smul := by simp [(· • ·)]
  zero_smul := by simp [(· • ·)]
  smul_assoc x y v := by
    have := map_smul (lift k G (Module.End k V) (DistribMulAction.toModuleEnd k V)) x y
    apply_fun (· v) at this
    rwa [LinearMap.smul_apply] at this
  single_one_smul g v := by
    have := MonoidAlgebra.lift_single (DistribMulAction.toModuleEnd k V) g (1:k)
    apply_fun (· v) at this
    rwa [one_smul, DistribMulAction.toModuleEnd_apply, DistribMulAction.toLinearMap_apply] at this

open MonoidAlgebra (of) in
noncomputable
def mk_mulAction_of_module (R G V : Type*) [CommSemiring R] [Monoid G] [AddCommMonoid V]
    [Module R V] [Module (MonoidAlgebra R G) V] [IsScalarTower R (MonoidAlgebra R G) V] :
    DistribMulAction G V where
  smul g v := of R G g • v
  one_smul v := show of R G 1 • v = v by simp only [map_one, one_smul]
  mul_smul g h v := show of R G (g * h) • v = of R G g • (of R G h • v) by
    simp only [map_mul, mul_smul]
  smul_zero g := show of R G g • (0 : V) = 0 by simp only [smul_zero]
  smul_add g v₁ v₂ := show of R G g • (v₁ + v₂) = of R G g • v₁ + of R G g • v₂ by
    simp only [smul_add]

open MonoidAlgebra (of) in
def mk_of_module (R G V : Type*) [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V]
    [Module (MonoidAlgebra R G) V] [IsScalarTower R (MonoidAlgebra R G) V] :
    letI : DistribMulAction G V := mk_mulAction_of_module R G V
    Representation R G V :=
  letI : DistribMulAction G V := mk_mulAction_of_module R G V
  { smul_comm r g v := by
      show r • of R G g • v = of R G g • (r • v)
      rw [← algebraMap_smul (MonoidAlgebra R G) r v, ← smul_assoc, ← smul_assoc,
        smul_eq_mul, ← Algebra.commutes, ← smul_eq_mul, algebraMap_smul]
    single_one_smul g v := rfl }

set_option linter.unusedVariables false in
variable {G} in
def OneDim (χ : G →* R) : Type _ := R

namespace OneDim

variable (χ : G →* R)

instance : AddCommMonoid (OneDim R χ) := inferInstanceAs <| AddCommMonoid R

omit [CommSemiring R] in
instance [CommRing R] : AddCommGroup (OneDim R χ) := inferInstanceAs <| AddCommGroup R

instance : Module R (OneDim R χ) := inferInstanceAs <| Module R R

instance : SMul G (OneDim R χ) where
  smul g v := χ g • v

lemma smul_def (g : G) (v : OneDim R χ) : g • v = χ g • v := rfl

instance : DistribMulAction G (OneDim R χ) where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]
  smul_zero := by simp [smul_def]
  smul_add := by simp [smul_def, mul_add]

instance : SMulCommClass R G (OneDim R χ) where
  smul_comm := by simp [smul_def, mul_left_comm]

instance : SMulCommClass G R (OneDim R χ) := SMulCommClass.symm R G (OneDim R χ)

noncomputable
instance : Representation R G (OneDim R χ) :=
  mk_of_action R G (OneDim R χ)

end OneDim

abbrev Trivial : Type _ := OneDim R (1 : G →* R)

namespace Trivial

@[simp]
theorem smul_def (g : G) (v : Trivial R G) : g • v = v := by simp [OneDim.smul_def]

end Trivial

/-- An `R`-linear representation of `G` on `V` can be thought of as
an algebra map from `MonoidAlgebra R G` into the `R`-linear endomorphisms of `V`. -/
noncomputable def asAlgebraHom : MonoidAlgebra R G →ₐ[R] Module.End R V :=
  (lift R G _) (DistribMulAction.toModuleEnd R V)

theorem asAlgebraHom_def : asAlgebraHom R G V = (lift R G _) (DistribMulAction.toModuleEnd R V) :=
  rfl

variable {R G} in
@[simp]
theorem asAlgebraHom_single (g : G) (r : R) :
    asAlgebraHom R G V (MonoidAlgebra.single g r) = r • (DistribMulAction.toModuleEnd R V g) := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

variable {G} in
theorem asAlgebraHom_single_one (g : G) :
  asAlgebraHom R G V (MonoidAlgebra.single g 1) = DistribMulAction.toModuleEnd R V g := by simp

variable {G} in
theorem asAlgebraHom_of (g : G) :
  asAlgebraHom R G V (MonoidAlgebra.of R G g) = DistribMulAction.toModuleEnd R V g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

section Constructions

instance : Representation R G (V × W) where
  single_one_smul g v := by ext <;> simp

section Hom

instance : Representation R G (V →ₗ[R] W) where
  single_one_smul g f := by ext; simp only [LinearMap.smul_apply, one_smul]

end Hom

section TensorProduct

end TensorProduct

end Constructions

end Representation

#exit


section Group

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

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
  map_one' := ext fun x => by simp [one_eq_id]
  map_mul' g h := ext fun x => by simp [mul_eq_comp, comp_assoc]

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
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl

/-- Given $k$-modules $V, W$, there is a homomorphism $φ : V^* ⊗ W → Hom_k(V, W)$
(implemented by `dualTensorHom` in `Mathlib.LinearAlgebra.Contraction`).
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
