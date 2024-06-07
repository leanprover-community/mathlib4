/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Elementwise
import Mathlib.RepresentationTheory.Action.Monoidal
import Mathlib.RepresentationTheory.Basic

#align_import representation_theory.Rep from "leanprover-community/mathlib"@"cec81510e48e579bde6acd8568c06a87af045b63"

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `Module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We construct the categorical equivalence `Rep k G ≌ ModuleCat (MonoidAlgebra k G)`.
We verify that `Rep k G` is a `k`-linear abelian symmetric monoidal category with all (co)limits.
-/

suppress_compilation

universe u

open CategoryTheory

open CategoryTheory.Limits

/-- The category of `k`-linear representations of a monoid `G`. -/
abbrev Rep (k G : Type u) [Ring k] [Monoid G] :=
  Action (ModuleCat.{u} k) (MonCat.of G)
set_option linter.uppercaseLean3 false in
#align Rep Rep

instance (k G : Type u) [CommRing k] [Monoid G] : Linear k (Rep k G) := by infer_instance

namespace Rep

variable {k G : Type u} [CommRing k]

section

variable [Monoid G]

instance : CoeSort (Rep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : Rep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (Rep k G) (ModuleCat k)).obj V); infer_instance

instance (V : Rep k G) : Module k V := by
  change Module k ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

/-- Specialize the existing `Action.ρ`, changing the type to `Representation k G V`.
-/
def ρ (V : Rep k G) : Representation k G V :=
-- Porting note: was `V.ρ`
  Action.ρ V
set_option linter.uppercaseLean3 false in
#align Rep.ρ Rep.ρ

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, ρ⟩
set_option linter.uppercaseLean3 false in
#align Rep.of Rep.of

@[simp]
theorem coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.coe_of Rep.coe_of

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.of_ρ Rep.of_ρ

theorem Action_ρ_eq_ρ {A : Rep k G} : Action.ρ A = A.ρ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.Action_ρ_eq_ρ Rep.Action_ρ_eq_ρ

/-- Allows us to apply lemmas about the underlying `ρ`, which would take an element `g : G` rather
than `g : MonCat.of G` as an argument. -/
theorem of_ρ_apply {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (g : MonCat.of G) : (Rep.of ρ).ρ g = ρ (g : G) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.of_ρ_apply Rep.of_ρ_apply

@[simp]
theorem ρ_inv_self_apply {G : Type u} [Group G] (A : Rep k G) (g : G) (x : A) :
    A.ρ g⁻¹ (A.ρ g x) = x :=
  show (A.ρ g⁻¹ * A.ρ g) x = x by rw [← map_mul, inv_mul_self, map_one, LinearMap.one_apply]
set_option linter.uppercaseLean3 false in
#align Rep.ρ_inv_self_apply Rep.ρ_inv_self_apply

@[simp]
theorem ρ_self_inv_apply {G : Type u} [Group G] {A : Rep k G} (g : G) (x : A) :
    A.ρ g (A.ρ g⁻¹ x) = x :=
  show (A.ρ g * A.ρ g⁻¹) x = x by rw [← map_mul, mul_inv_self, map_one, LinearMap.one_apply]
set_option linter.uppercaseLean3 false in
#align Rep.ρ_self_inv_apply Rep.ρ_self_inv_apply

theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (f.comm g) x
set_option linter.uppercaseLean3 false in
#align Rep.hom_comm_apply Rep.hom_comm_apply

variable (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
def trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (@Representation.trivial k G V _ _ _ _)
set_option linter.uppercaseLean3 false in
#align Rep.trivial Rep.trivial

variable {k G}

theorem trivial_def {V : Type u} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.trivial_def Rep.trivial_def

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance {V : Type u} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where

-- Porting note: the two following instances were found automatically in mathlib3
noncomputable instance : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.instPreservesLimitsForget.{u} _ _

noncomputable instance : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.instPreservesColimitsForget.{u} _ _

/- Porting note: linter complains `simp` unfolds some types in the LHS, so
have removed `@[simp]`. -/
theorem MonoidalCategory.braiding_hom_apply {A B : Rep k G} (x : A) (y : B) :
    Action.Hom.hom (β_ A B).hom (TensorProduct.tmul k x y) = TensorProduct.tmul k y x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_category.braiding_hom_apply Rep.MonoidalCategory.braiding_hom_apply

/- Porting note: linter complains `simp` unfolds some types in the LHS, so
have removed `@[simp]`. -/
theorem MonoidalCategory.braiding_inv_apply {A B : Rep k G} (x : A) (y : B) :
    Action.Hom.hom (β_ A B).inv (TensorProduct.tmul k y x) = TensorProduct.tmul k x y :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_category.braiding_inv_apply Rep.MonoidalCategory.braiding_inv_apply

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization : MonoidalFunctor (Action (Type u) (MonCat.of G)) (Rep k G) :=
  (ModuleCat.monoidalFree k).mapAction (MonCat.of G)
set_option linter.uppercaseLean3 false in
#align Rep.linearization Rep.linearization

variable {k G}

@[simp]
theorem linearization_obj_ρ (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V →₀ k) :
    ((linearization k G).obj X).ρ g x = Finsupp.lmapDomain k k (X.ρ g) x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.linearization_obj_ρ Rep.linearization_obj_ρ

theorem linearization_of (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V) :
    ((linearization k G).obj X).ρ g (Finsupp.single x (1 : k))
      = Finsupp.single (X.ρ g x) (1 : k) := by
  rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
set_option linter.uppercaseLean3 false in
#align Rep.linearization_of Rep.linearization_of

-- Porting note: helps fixing `linearizationTrivialIso` since change in behaviour of ext
theorem linearization_single (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable {X Y : Action (Type u) (MonCat.of G)} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom = Finsupp.lmapDomain k k f.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.linearization_map_hom Rep.linearization_map_hom

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single
set_option linter.uppercaseLean3 false in
#align Rep.linearization_map_hom_single Rep.linearization_map_hom_single

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) (MonCat.of G)) :
    ((linearization k G).μ X Y).hom = (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.linearization_μ_hom Rep.linearization_μ_hom

@[simp]
theorem linearization_μ_inv_hom (X Y : Action (Type u) (MonCat.of G)) :
    (inv ((linearization k G).μ X Y)).hom = (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap := by
-- Porting note (#11039): broken proof was
/- simp_rw [← Action.forget_map, Functor.map_inv, Action.forget_map, linearization_μ_hom]
  apply IsIso.inv_eq_of_hom_inv_id _
  exact LinearMap.ext fun x => LinearEquiv.symm_apply_apply _ _-/
  rw [← Action.forget_map, Functor.map_inv]
  apply IsIso.inv_eq_of_hom_inv_id
  exact LinearMap.ext fun x => LinearEquiv.symm_apply_apply (finsuppTensorFinsupp' k X.V Y.V) x
set_option linter.uppercaseLean3 false in
#align Rep.linearization_μ_inv_hom Rep.linearization_μ_inv_hom

@[simp]
theorem linearization_ε_hom : (linearization k G).ε.hom = Finsupp.lsingle PUnit.unit :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.linearization_ε_hom Rep.linearization_ε_hom

theorem linearization_ε_inv_hom_apply (r : k) :
    (inv (linearization k G).ε).hom (Finsupp.single PUnit.unit r) = r :=
  IsIso.hom_inv_id_apply (linearization k G).ε r
set_option linter.uppercaseLean3 false in
#align Rep.linearization_ε_inv_hom_apply Rep.linearization_ε_inv_hom_apply

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps!]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => linearization_single ..
set_option linter.uppercaseLean3 false in
#align Rep.linearization_trivial_iso Rep.linearizationTrivialIso

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbrev ofMulAction (H : Type u) [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H
set_option linter.uppercaseLean3 false in
#align Rep.of_mul_action Rep.ofMulAction

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
noncomputable def leftRegular : Rep k G :=
  ofMulAction k G G
set_option linter.uppercaseLean3 false in
#align Rep.left_regular Rep.leftRegular

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
noncomputable def diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)
set_option linter.uppercaseLean3 false in
#align Rep.diagonal Rep.diagonal

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
noncomputable def linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Iso.refl _
set_option linter.uppercaseLean3 false in
#align Rep.linearization_of_mul_action_iso Rep.linearizationOfMulActionIso

section

variable (k G A : Type u) [CommRing k] [Monoid G] [AddCommGroup A]
  [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)

@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `S`. -/
@[simp] def ofAlgebraAut (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := ofDistribMulAction ℤ (S ≃ₐ[R] S) S

end
section
variable (M G : Type) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • Additive.toMul a) := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `Sˣ`. -/
@[simp] def ofAlgebraAutOnUnits (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
@[simps]
noncomputable def leftRegularHom (A : Rep k G) (x : A) : Rep.ofMulAction k G G ⟶ A where
  hom := Finsupp.lift _ _ _ fun g => A.ρ g x
  comm g := by
    refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
/- Porting note: rest of broken proof was
    simpa only [LinearMap.comp_apply, ModuleCat.comp_def, Finsupp.lsingle_apply, Finsupp.lift_apply,
      Action_ρ_eq_ρ, of_ρ_apply, Representation.ofMulAction_single, Finsupp.sum_single_index,
      zero_smul, one_smul, smul_eq_mul, A.ρ.map_mul] -/
    simp only [LinearMap.comp_apply, ModuleCat.comp_def, Finsupp.lsingle_apply]
    erw [Finsupp.lift_apply, Finsupp.lift_apply, Representation.ofMulAction_single (G := G)]
    simp only [Finsupp.sum_single_index, zero_smul, one_smul, smul_eq_mul, A.ρ.map_mul, of_ρ]
    rfl
set_option linter.uppercaseLean3 false in
#align Rep.left_regular_hom Rep.leftRegularHom

theorem leftRegularHom_apply {A : Rep k G} (x : A) :
    (leftRegularHom A x).hom (Finsupp.single 1 1) = x := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [leftRegularHom_hom, Finsupp.lift_apply, Finsupp.sum_single_index, one_smul,
    A.ρ.map_one, LinearMap.one_apply]
  rw [zero_smul]
set_option linter.uppercaseLean3 false in
#align Rep.left_regular_hom_apply Rep.leftRegularHom_apply

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (Rep.ofMulAction k G G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (Finsupp.single 1 1)
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun x := leftRegularHom A x
  left_inv f := by
    refine Action.Hom.ext _ _ (Finsupp.lhom_ext' fun x : G => LinearMap.ext_ring ?_)
    have :
      f.hom ((ofMulAction k G G).ρ x (Finsupp.single (1 : G) (1 : k))) =
        A.ρ x (f.hom (Finsupp.single (1 : G) (1 : k))) :=
      LinearMap.ext_iff.1 (f.comm x) (Finsupp.single 1 1)
    simp only [leftRegularHom_hom, LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lift_apply,
      ← this, coe_of, of_ρ, Representation.ofMulAction_single x (1 : G) (1 : k), smul_eq_mul,
      mul_one, zero_smul, Finsupp.sum_single_index, one_smul]
    -- Mismatched `Zero k` instances
    rfl
  right_inv x := leftRegularHom_apply x
set_option linter.uppercaseLean3 false in
#align Rep.left_regular_hom_equiv Rep.leftRegularHomEquiv

theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g 1) = A.ρ g x := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [leftRegularHomEquiv_symm_apply, leftRegularHom_hom, Finsupp.lift_apply,
    Finsupp.sum_single_index, one_smul]
  rw [zero_smul]
set_option linter.uppercaseLean3 false in
#align Rep.left_regular_hom_equiv_symm_single Rep.leftRegularHomEquiv_symm_single

end Linearization

end

section MonoidalClosed
open MonoidalCategory Action

variable [Group G] (A B C : Rep k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map := fun {X} {Y} f =>
    { hom := ModuleCat.ofHom (LinearMap.llcomp k _ _ _ f.hom)
      comm := fun g => LinearMap.ext fun x => LinearMap.ext fun y => by
        show f.hom (X.ρ g _) = _
        simp only [hom_comm_apply]; rfl }
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl
set_option linter.uppercaseLean3 false in
#align Rep.ihom Rep.ihom

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.ihom_obj_ρ_apply Rep.ihom_obj_ρ_apply

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f :=
    { hom := (TensorProduct.curry f.hom).flip
      comm := fun g => by
        refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
        change f.hom (_ ⊗ₜ[k] _) = C.ρ g (f.hom (_ ⊗ₜ[k] _))
        rw [← hom_comm_apply]
        change _ = f.hom ((A.ρ g * A.ρ g⁻¹) y ⊗ₜ[k] _)
        simp only [← map_mul, mul_inv_self, map_one]
        rfl }
  invFun f :=
    { hom := TensorProduct.uncurry k _ _ _ f.hom.flip
      comm := fun g => TensorProduct.ext' fun x y => by
/- Porting note: rest of broken proof was
        dsimp only [MonoidalCategory.tensorLeft_obj, ModuleCat.comp_def, LinearMap.comp_apply,
          tensor_rho, ModuleCat.MonoidalCategory.hom_apply, TensorProduct.map_tmul]
        simp only [TensorProduct.uncurry_apply f.hom.flip, LinearMap.flip_apply, Action_ρ_eq_ρ,
          hom_comm_apply f g y, Rep.ihom_obj_ρ_apply, LinearMap.comp_apply, ρ_inv_self_apply] -/
        change TensorProduct.uncurry k _ _ _ f.hom.flip (A.ρ g x ⊗ₜ[k] B.ρ g y) =
          C.ρ g (TensorProduct.uncurry k _ _ _ f.hom.flip (x ⊗ₜ[k] y))
        -- The next 3 tactics used to be `rw` before leanprover/lean4#2644
        erw [TensorProduct.uncurry_apply, LinearMap.flip_apply, hom_comm_apply,
          Rep.ihom_obj_ρ_apply,
          LinearMap.comp_apply, LinearMap.comp_apply] --, ρ_inv_self_apply (A := C)]
        dsimp
        erw [ρ_inv_self_apply]
        rfl}
  left_inv f := Action.Hom.ext _ _ (TensorProduct.ext' fun _ _ => rfl)
  right_inv f := by ext; rfl
set_option linter.uppercaseLean3 false in
#align Rep.hom_equiv Rep.homEquiv

variable {A B C}

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_apply_hom (f : A ⊗ B ⟶ C) :
    (homEquiv A B C f).hom = (TensorProduct.curry f.hom).flip := rfl
set_option linter.uppercaseLean3 false in
#align Rep.hom_equiv_apply_hom Rep.homEquiv_apply_hom

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_symm_apply_hom (f : B ⟶ (Rep.ihom A).obj C) :
    ((homEquiv A B C).symm f).hom = TensorProduct.uncurry k A B C f.hom.flip := rfl
set_option linter.uppercaseLean3 false in
#align Rep.hom_equiv_symm_apply_hom Rep.homEquiv_symm_apply_hom

instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv (
      { homEquiv := Rep.homEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Action.Hom.ext _ _
          (TensorProduct.ext' fun _ _ => rfl)
        homEquiv_naturality_right := fun _ _ => Action.Hom.ext _ _ (LinearMap.ext
          fun _ => LinearMap.ext fun _ => rfl) })}

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.ihom_obj_ρ_def Rep.ihom_obj_ρ_def

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C = Rep.homEquiv A B C :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.hom_equiv_def Rep.homEquiv_def

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.ev A).app B)
      = TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl
set_option linter.uppercaseLean3 false in
#align Rep.ihom_ev_app_hom Rep.ihom_ev_app_hom

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.coev A).app B) = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
set_option linter.uppercaseLean3 false in
#align Rep.ihom_coev_app_hom Rep.ihom_coev_app_hom

variable (A B C)

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
def MonoidalClosed.linearHomEquiv : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv Rep.MonoidalClosed.linearHomEquiv

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv_comm Rep.MonoidalClosed.linearHomEquivComm

variable {A B C}

-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom = (TensorProduct.curry f.hom).flip :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv_hom Rep.MonoidalClosed.linearHomEquiv_hom

-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom = TensorProduct.curry f.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv_comm_hom Rep.MonoidalClosed.linearHomEquivComm_hom

theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom = TensorProduct.uncurry k A B C f.hom.flip :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv_symm_hom Rep.MonoidalClosed.linearHomEquiv_symm_hom

theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom
      = TensorProduct.uncurry k A B C f.hom :=
  TensorProduct.ext' fun _ _ => rfl
set_option linter.uppercaseLean3 false in
#align Rep.monoidal_closed.linear_hom_equiv_comm_symm_hom Rep.MonoidalClosed.linearHomEquivComm_symm_hom

end MonoidalClosed

end Rep

namespace Representation
open MonoidalCategory
variable {k G : Type u} [CommRing k] [Monoid G] {V W : Type u} [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W] (ρ : Representation k G V) (τ : Representation k G W)

/-- Tautological isomorphism to help Lean in typechecking. -/
def repOfTprodIso : Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ :=
  Iso.refl _
set_option linter.uppercaseLean3 false in
#align representation.Rep_of_tprod_iso Representation.repOfTprodIso

theorem repOfTprodIso_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).hom.hom x = x :=
  rfl
set_option linter.uppercaseLean3 false in
#align representation.Rep_of_tprod_iso_apply Representation.repOfTprodIso_apply

theorem repOfTprodIso_inv_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).inv.hom x = x :=
  rfl
set_option linter.uppercaseLean3 false in
#align representation.Rep_of_tprod_iso_inv_apply Representation.repOfTprodIso_inv_apply

end Representation

/-!
# The categorical equivalence `Rep k G ≌ Module.{u} (MonoidAlgebra k G)`.
-/


namespace Rep

variable {k G : Type u} [CommRing k] [Monoid G]

-- Verify that the symmetric monoidal structure is available.
example : SymmetricCategory (Rep k G) := by infer_instance

example : MonoidalPreadditive (Rep k G) := by infer_instance

example : MonoidalLinear k (Rep k G) := by infer_instance

noncomputable section

/-- Auxiliary lemma for `toModuleMonoidAlgebra`. -/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : MonoidAlgebra k G) (x : V) :
    f ((((MonoidAlgebra.lift k G (V →ₗ[k] V)) ρ) r) x) =
      (((MonoidAlgebra.lift k G (W →ₗ[k] W)) σ) r) (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, add_left_inj, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [AlgHom.map_smul, w, RingHom.id_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ]
set_option linter.uppercaseLean3 false in
#align Rep.to_Module_monoid_algebra_map_aux Rep.to_Module_monoidAlgebra_map_aux

/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep k G} (f : V ⟶ W) :
    ModuleCat.of (MonoidAlgebra k G) V.ρ.asModule ⟶ ModuleCat.of (MonoidAlgebra k G) W.ρ.asModule :=
  { f.hom with
    map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ f.hom f.comm r x }
set_option linter.uppercaseLean3 false in
#align Rep.to_Module_monoid_algebra_map Rep.toModuleMonoidAlgebraMap

/-- Functorially convert a representation of `G` into a module over `MonoidAlgebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G) where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f
set_option linter.uppercaseLean3 false in
#align Rep.to_Module_monoid_algebra Rep.toModuleMonoidAlgebra

/-- Functorially convert a module over `MonoidAlgebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G where
  obj M := Rep.of (Representation.ofModule M)
  map f :=
    { hom := { f with map_smul' := fun r x => f.map_smul (algebraMap k _ r) x }
      comm := fun g => by ext; apply f.map_smul }
set_option linter.uppercaseLean3 false in
#align Rep.of_Module_monoid_algebra Rep.ofModuleMonoidAlgebra

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M : Type u) = RestrictScalars k (MonoidAlgebra k G) M :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.of_Module_monoid_algebra_obj_coe Rep.ofModuleMonoidAlgebra_obj_coe

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.of_Module_monoid_algebra_obj_ρ Rep.ofModuleMonoidAlgebra_obj_ρ

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{u} (MonoidAlgebra k G)} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.trans
    (RestrictScalars.addEquiv k (MonoidAlgebra k G) _)
set_option linter.uppercaseLean3 false in
#align Rep.counit_iso_add_equiv Rep.counitIsoAddEquiv

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIsoAddEquiv {V : Rep k G} : V ≃+ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  refine V.ρ.asModuleEquiv.symm.trans ?_
  exact (RestrictScalars.addEquiv _ _ _).symm
set_option linter.uppercaseLean3 false in
#align Rep.unit_iso_add_equiv Rep.unitIsoAddEquiv

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIso (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso'
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        set_option tactic.skipAssignedInstances false in
        dsimp [counitIsoAddEquiv]
        /- Porting note: rest of broken proof was `simp`. -/
        rw [AddEquiv.trans_apply]
        rw [AddEquiv.trans_apply]
        erw [@Representation.ofModule_asAlgebraHom_apply_apply k G _ _ _ _ (_)]
        exact AddEquiv.symm_apply_apply _ _}
set_option linter.uppercaseLean3 false in
#align Rep.counit_iso Rep.counitIso

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  dsimp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
/- Porting note: rest of broken proof was
  simp only [AddEquiv.apply_eq_iff_eq, AddEquiv.apply_symm_apply,
    Representation.asModuleEquiv_symm_map_rho, Representation.ofModule_asModule_act] -/
  erw [Representation.asModuleEquiv_symm_map_rho]
  rfl
set_option linter.uppercaseLean3 false in
#align Rep.unit_iso_comm Rep.unit_iso_comm

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIso (V : Rep k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  Action.mkIso
    (LinearEquiv.toModuleIso'
      { unitIsoAddEquiv with
        map_smul' := fun r x => by
          dsimp [unitIsoAddEquiv]
/- Porting note: rest of broken proof was
          simp only [Representation.asModuleEquiv_symm_map_smul,
            RestrictScalars.addEquiv_symm_map_algebraMap_smul] -/
          -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
          erw [AddEquiv.trans_apply,
            Representation.asModuleEquiv_symm_map_smul]
          rfl })
    fun g => by ext; apply unit_iso_comm
set_option linter.uppercaseLean3 false in
#align Rep.unit_iso Rep.unitIso

/-- The categorical equivalence `Rep k G ≌ ModuleCat (MonoidAlgebra k G)`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} (MonoidAlgebra k G) where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by aesop_cat)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by aesop_cat)
set_option linter.uppercaseLean3 false in
#align Rep.equivalence_Module_monoid_algebra Rep.equivalenceModuleMonoidAlgebra

-- TODO Verify that the equivalence with `ModuleCat (MonoidAlgebra k G)` is a monoidal functor.
end
