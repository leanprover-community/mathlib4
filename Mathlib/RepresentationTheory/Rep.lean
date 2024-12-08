/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Elementwise
import Mathlib.RepresentationTheory.Action.Monoidal
import Mathlib.RepresentationTheory.Basic

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
  (ModuleCat.endMulEquiv V.V).toMonoidHom.comp (Action.ρ V)

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, MonCat.ofHom ((ModuleCat.endMulEquiv _).symm.toMonoidHom.comp ρ) ⟩

@[simp]
theorem coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V :=
  rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

theorem Action_ρ_eq_ρ {A : Rep k G} :
    Action.ρ A = (ModuleCat.endMulEquiv _).symm.toMonoidHom.comp A.ρ :=
  rfl

@[simp]
lemma ρ_hom {X : Rep k G} (g : G) : (Action.ρ X g).hom = X.ρ g := rfl

@[simp]
lemma ofHom_ρ {X : Rep k G} (g : G) : ModuleCat.ofHom (X.ρ g) = Action.ρ X g := rfl

/-- Allows us to apply lemmas about the underlying `ρ`, which would take an element `g : G` rather
than `g : MonCat.of G` as an argument. -/
theorem of_ρ_apply {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (g : MonCat.of G) : (Rep.of ρ).ρ g = ρ (g : G) :=
  rfl

@[simp]
theorem ρ_inv_self_apply {G : Type u} [Group G] (A : Rep k G) (g : G) (x : A) :
    A.ρ g⁻¹ (A.ρ g x) = x :=
  show (A.ρ g⁻¹ * A.ρ g) x = x by rw [← map_mul, inv_mul_cancel, map_one, LinearMap.one_apply]

@[simp]
theorem ρ_self_inv_apply {G : Type u} [Group G] {A : Rep k G} (g : G) (x : A) :
    A.ρ g (A.ρ g⁻¹ x) = x :=
  show (A.ρ g * A.ρ g⁻¹) x = x by rw [← map_mul, mul_inv_cancel, map_one, LinearMap.one_apply]

theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp (f.comm g)) x

variable (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
def trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (@Representation.trivial k G V _ _ _ _)

variable {k G}

theorem trivial_def {V : Type u} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v :=
  rfl

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance {V : Type u} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where

-- Porting note: the two following instances were found automatically in mathlib3
noncomputable instance : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.preservesLimits_forget.{u} _ _

noncomputable instance : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.preservesColimits_forget.{u} _ _

/- Porting note: linter complains `simp` unfolds some types in the LHS, so
have removed `@[simp]`. -/
theorem MonoidalCategory.braiding_hom_apply {A B : Rep k G} (x : A) (y : B) :
    Action.Hom.hom (β_ A B).hom (TensorProduct.tmul k x y) = TensorProduct.tmul k y x :=
  rfl

/- Porting note: linter complains `simp` unfolds some types in the LHS, so
have removed `@[simp]`. -/
theorem MonoidalCategory.braiding_inv_apply {A B : Rep k G} (x : A) (y : B) :
    Action.Hom.hom (β_ A B).inv (TensorProduct.tmul k y x) = TensorProduct.tmul k x y :=
  rfl

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization : (Action (Type u) (MonCat.of G)) ⥤ (Rep k G) :=
  (ModuleCat.free k).mapAction (MonCat.of G)

instance : (linearization k G).Monoidal := by
  dsimp only [linearization]
  infer_instance

variable {k G}

@[simp]
theorem linearization_obj_ρ (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V →₀ k) :
    ((linearization k G).obj X).ρ g x = Finsupp.lmapDomain k k (X.ρ g) x :=
  rfl

theorem linearization_of (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V) :
    ((linearization k G).obj X).ρ g (Finsupp.single x (1 : k))
      = Finsupp.single (X.ρ g x) (1 : k) := by
  rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) (MonCat.of G)) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable {X Y : Action (Type u) (MonCat.of G)} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom =
    ModuleCat.ofHom (Finsupp.lmapDomain k k f.hom) :=
  rfl

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) (MonCat.of G)) :
    (μ (linearization k G) X Y).hom =
      ModuleCat.ofHom (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_δ_hom (X Y : Action (Type u) (MonCat.of G)) :
    (δ (linearization k G) X Y).hom =
      ModuleCat.ofHom (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap :=
  rfl

@[simp]
theorem linearization_ε_hom : (ε (linearization k G)).hom =
    ModuleCat.ofHom (Finsupp.lsingle PUnit.unit) :=
  rfl

theorem linearization_η_hom_apply (r : k) :
    (η (linearization k G)).hom (Finsupp.single PUnit.unit r) = r :=
  (εIso (linearization k G)).hom_inv_id_apply r

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps!]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => linearization_single ..

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbrev ofMulAction (H : Type u) [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
noncomputable def leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
noncomputable def diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
noncomputable def linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Iso.refl _

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
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

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
  hom := ModuleCat.ofHom <| Finsupp.lift _ _ _ fun g => A.ρ g x
  comm g := by
    ext : 1
    refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
/- Porting note: rest of broken proof was
    simpa only [LinearMap.comp_apply, ModuleCat.comp_def, Finsupp.lsingle_apply, Finsupp.lift_apply,
      Action_ρ_eq_ρ, of_ρ_apply, Representation.ofMulAction_single, Finsupp.sum_single_index,
      zero_smul, one_smul, smul_eq_mul, A.ρ.map_mul] -/
    simp only [LinearMap.comp_apply, ModuleCat.hom_comp, Finsupp.lsingle_apply]
    erw [Finsupp.lift_apply, Finsupp.lift_apply, Representation.ofMulAction_single (G := G)]
    simp only [Finsupp.sum_single_index, zero_smul, one_smul, smul_eq_mul, A.ρ.map_mul, of_ρ]
    rfl

theorem leftRegularHom_apply {A : Rep k G} (x : A) :
    (leftRegularHom A x).hom (Finsupp.single 1 1) = x := by
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [leftRegularHom_hom_hom, Finsupp.lift_apply, Finsupp.sum_single_index, one_smul,
    A.ρ.map_one, LinearMap.one_apply]
  rw [zero_smul]

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (Rep.ofMulAction k G G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (Finsupp.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := leftRegularHom A x
  left_inv f := by
    refine Action.Hom.ext (ModuleCat.hom_ext (Finsupp.lhom_ext' fun x : G => LinearMap.ext_ring ?_))
    have :
      f.hom ((ofMulAction k G G).ρ x (Finsupp.single (1 : G) (1 : k))) =
        A.ρ x (f.hom (Finsupp.single (1 : G) (1 : k))) :=
      LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp (f.comm x)) (Finsupp.single 1 1)
    simp only [leftRegularHom_hom_hom, LinearMap.comp_apply, Finsupp.lsingle_apply,
      Finsupp.lift_apply, ← this, coe_of, of_ρ, Representation.ofMulAction_single x (1 : G) (1 : k),
      smul_eq_mul, mul_one, zero_smul, Finsupp.sum_single_index, one_smul]
    -- Mismatched `Zero k` instances
    rfl
  right_inv x := leftRegularHom_apply x

theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g 1) = A.ρ g x := by
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [leftRegularHomEquiv_symm_apply, leftRegularHom_hom_hom, Finsupp.lift_apply,
    Finsupp.sum_single_index, one_smul]
  rw [zero_smul]

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
    { hom := ModuleCat.ofHom (LinearMap.llcomp k _ _ _ f.hom.hom)
      comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun x => LinearMap.ext fun y => by
        show f.hom (X.ρ g _) = _
        simp only [hom_comm_apply]; rfl }
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f :=
    { hom := ModuleCat.ofHom <| (TensorProduct.curry f.hom.hom).flip
      comm := fun g => by
        ext x : 2
        refine LinearMap.ext fun y => ?_
        change f.hom (_ ⊗ₜ[k] _) = C.ρ g (f.hom (_ ⊗ₜ[k] _))
        rw [← hom_comm_apply]
        change _ = f.hom ((A.ρ g * A.ρ g⁻¹) y ⊗ₜ[k] _)
        simp only [← map_mul, mul_inv_cancel, map_one]
        rfl }
  invFun f :=
    { hom := ModuleCat.ofHom <| TensorProduct.uncurry k _ _ _ f.hom.hom.flip
      comm := fun g => ModuleCat.hom_ext <| TensorProduct.ext' fun x y => by
          /- Porting note: rest of broken proof was
        dsimp only [MonoidalCategory.tensorLeft_obj, ModuleCat.comp_def, LinearMap.comp_apply,
          tensor_ρ, ModuleCat.MonoidalCategory.hom_apply, TensorProduct.map_tmul]
        simp only [TensorProduct.uncurry_apply f.hom.flip, LinearMap.flip_apply, Action_ρ_eq_ρ,
          hom_comm_apply f g y, Rep.ihom_obj_ρ_apply, LinearMap.comp_apply, ρ_inv_self_apply] -/
        change TensorProduct.uncurry k _ _ _ f.hom.hom.flip (A.ρ g x ⊗ₜ[k] B.ρ g y) =
          C.ρ g (TensorProduct.uncurry k _ _ _ f.hom.hom.flip (x ⊗ₜ[k] y))
        -- The next 3 tactics used to be `rw` before https://github.com/leanprover/lean4/pull/2644
        erw [TensorProduct.uncurry_apply, LinearMap.flip_apply, hom_comm_apply,
          Rep.ihom_obj_ρ_apply,
          LinearMap.comp_apply, LinearMap.comp_apply] --, ρ_inv_self_apply (A := C)]
        dsimp
        rw [ρ_inv_self_apply]
        rfl }
  left_inv _ := Action.Hom.ext (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl))
  right_inv f := by ext; rfl

variable {A B C}

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_apply_hom (f : A ⊗ B ⟶ C) :
    (homEquiv A B C f).hom = ModuleCat.ofHom (TensorProduct.curry f.hom.hom).flip := rfl

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_symm_apply_hom (f : B ⟶ (Rep.ihom A).obj C) :
    ((homEquiv A B C).symm f).hom =
      ModuleCat.ofHom (TensorProduct.uncurry k A B C f.hom.hom.flip) := rfl

instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv (
      { homEquiv := Rep.homEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Action.Hom.ext
          (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl))
        homEquiv_naturality_right := fun _ _ => Action.Hom.ext (ModuleCat.hom_ext (LinearMap.ext
          fun _ => LinearMap.ext fun _ => rfl)) })}

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C = Rep.homEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.ev A).app B) = ModuleCat.ofHom
      (TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip) := by
  ext; rfl

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    Action.Hom.hom ((ihom.coev A).app B) = ModuleCat.ofHom (TensorProduct.mk k _ _).flip :=
  ModuleCat.hom_ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

variable (A B C)

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
def MonoidalClosed.linearHomEquiv : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

variable {A B C}

-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom =
      ModuleCat.ofHom (TensorProduct.curry f.hom.hom).flip :=
  rfl

-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom =
      ModuleCat.ofHom (TensorProduct.curry f.hom.hom) :=
  rfl

theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom =
      ModuleCat.ofHom (TensorProduct.uncurry k A B C f.hom.hom.flip) := by
  simp [linearHomEquiv]
  rfl

theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom =
      ModuleCat.ofHom (TensorProduct.uncurry k A B C f.hom.hom) :=
  ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed

end Rep

namespace Representation
open MonoidalCategory
variable {k G : Type u} [CommRing k] [Monoid G] {V W : Type u} [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W] (ρ : Representation k G V) (τ : Representation k G W)

/-- Tautological isomorphism to help Lean in typechecking. -/
def repOfTprodIso : Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ :=
  Iso.refl _

theorem repOfTprodIso_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).hom.hom x = x :=
  rfl

theorem repOfTprodIso_inv_apply (x : TensorProduct k V W) : (repOfTprodIso ρ τ).inv.hom x = x :=
  rfl

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
    simp only [map_smul, w, RingHom.id_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ]

/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep k G} (f : V ⟶ W) :
    ModuleCat.of (MonoidAlgebra k G) V.ρ.asModule ⟶ ModuleCat.of (MonoidAlgebra k G) W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.hom with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ f.hom.hom
        (fun g => ModuleCat.hom_ext_iff.mp (f.comm g)) r x }

/-- Functorially convert a representation of `G` into a module over `MonoidAlgebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G) where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

/-- Functorially convert a module over `MonoidAlgebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G where
  obj M := Rep.of (Representation.ofModule M)
  map f :=
    { hom := ModuleCat.ofHom
        { f.hom with
          map_smul' := fun r x => f.hom.map_smul (algebraMap k _ r) x }
      comm := fun g => by ext; apply f.hom.map_smul }

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M : Type u) = RestrictScalars k (MonoidAlgebra k G) M :=
  rfl

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{u} (MonoidAlgebra k G)} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.trans
    (RestrictScalars.addEquiv k (MonoidAlgebra k G) _)

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIsoAddEquiv {V : Rep k G} : V ≃+ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  refine V.ρ.asModuleEquiv.symm.trans ?_
  exact (RestrictScalars.addEquiv _ _ _).symm

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIso (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        set_option tactic.skipAssignedInstances false in
        dsimp [counitIsoAddEquiv]
        /- Porting note: rest of broken proof was `simp`. -/
        rw [AddEquiv.trans_apply]
        rw [AddEquiv.trans_apply]
        erw [@Representation.ofModule_asAlgebraHom_apply_apply k G _ _ _ _ (_)]
        exact AddEquiv.symm_apply_apply _ _}

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  dsimp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  simp only [AddEquiv.apply_eq_iff_eq, AddEquiv.apply_symm_apply,
    Representation.asModuleEquiv_symm_map_rho, Representation.ofModule_asModule_act]

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIso (V : Rep k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  Action.mkIso
    (LinearEquiv.toModuleIso
      { unitIsoAddEquiv with
        map_smul' := fun r x => by
          dsimp [unitIsoAddEquiv]
/- Porting note: rest of broken proof was
          simp only [Representation.asModuleEquiv_symm_map_smul,
            RestrictScalars.addEquiv_symm_map_algebraMap_smul] -/
          -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
          erw [AddEquiv.trans_apply,
            Representation.asModuleEquiv_symm_map_smul]
          rfl })
    fun g => by ext; apply unit_iso_comm

/-- The categorical equivalence `Rep k G ≌ ModuleCat (MonoidAlgebra k G)`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} (MonoidAlgebra k G) where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by aesop_cat)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by aesop_cat)

-- TODO Verify that the equivalence with `ModuleCat (MonoidAlgebra k G)` is a monoidal functor.
end

end Rep
