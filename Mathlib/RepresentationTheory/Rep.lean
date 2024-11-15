/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Elementwise
import Mathlib.RepresentationTheory.Action.Monoidal
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.DifferentFile

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

universe v u w

open CategoryTheory

@[simp] lemma Finsupp.finsuppProdLEquiv_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α × β) (m : M) :
    Finsupp.finsuppProdLEquiv R (Finsupp.single a m) =
      Finsupp.single a.1 (Finsupp.single a.2 m) := by
  show Finsupp.curry _ = _
  simp only [Finsupp.curry, Finsupp.single_zero, Finsupp.sum_single_index]

@[simp] lemma Finsupp.finsuppProdLEquiv_symm_single_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α) (b : β) (m : M) :
    (Finsupp.finsuppProdLEquiv R).symm (Finsupp.single a (Finsupp.single b m)) =
      Finsupp.single (a, b) m := by
  show Finsupp.uncurry _ = _
  simp only [Finsupp.uncurry, Finsupp.sum_zero_index, Finsupp.sum_single_index, Finsupp.single_zero]

namespace ModuleCat

attribute [moduleCat_simps] ModuleCat.comp_def ModuleCat.coe_of ModuleCat.asHom

@[moduleCat_simps]
theorem hom_def {R : Type u} [Ring R] {X Y : ModuleCat R} : (X ⟶ Y) = (X →ₗ[R] Y) := rfl

@[moduleCat_simps]
theorem end_def {R : Type u} [Ring R] {X : ModuleCat R} : End X = (X →ₗ[R] X) := rfl

@[moduleCat_simps]
theorem id_def {R : Type u} [Ring R] {X : ModuleCat R} : 𝟙 X = LinearMap.id := rfl

end ModuleCat

open CategoryTheory.Limits

/-- The category of `k`-linear representations of a monoid `G`. -/
abbrev Rep (k G : Type u) [Ring k] [Monoid G] :=
  Action (ModuleCat.{u} k) G

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

@[simp]
lemma coe_V {V : Rep k G} : (V.V : Type u) = V := rfl

/-- Specialize the existing `Action.ρ`, changing the type to `Representation k G V`.
-/
def ρ (V : Rep k G) : Representation k G V :=
-- Porting note: was `V.ρ`
  Action.ρ V

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, ρ⟩

@[simp]
theorem coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V :=
  rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

@[simp]
theorem Action_ρ_eq_ρ {A : Rep k G} : Action.ρ A = A.ρ :=
  rfl

theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (f.comm g) x

variable (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (@Representation.trivial k G V ..)

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

/-- The functor equipping a module with the trivial representation. -/
@[simps]
noncomputable def trivialFunctor : ModuleCat k ⥤ Rep k G where
  obj V := trivial k G V
  map f := { hom := f, comm := fun _ => rfl }

-- Porting note: the two following instances were found automatically in mathlib3
noncomputable instance : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.instPreservesLimitsForget.{u} _ _

noncomputable instance : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  Action.instPreservesColimitsForget.{u} _ _

noncomputable instance : ReflectsLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  inferInstanceAs <| ReflectsLimits (Action.forget (ModuleCat.{u} k) G)

noncomputable instance : ReflectsColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) :=
  inferInstanceAs <| ReflectsColimits (Action.forget (ModuleCat.{u} k) G)

theorem epi_iff_surjective {A B : Rep k G} (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    ((forget₂ _ _).map f)).2 h)⟩

theorem mono_iff_injective {A B : Rep k G} (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    ((forget₂ _ _).map f)).2 h)⟩

section
open MonoidalCategory

@[simp]
theorem coe_tensor {A B : Rep k G} : (A ⊗ B : Rep k G) = TensorProduct k A B := rfl

@[simp]
theorem tensor_ρ {A B : Rep k G} : (A ⊗ B).ρ = A.ρ.tprod B.ρ := rfl

end

section Res

variable {H : Type u} [Monoid H] (f : G →* H) (A : Rep k H)

@[simp]
lemma coe_res_obj : ((Action.res _ f).obj A : Type u) = A := rfl

@[simp]
lemma coe_res_obj_ρ (g : G) :
    @DFunLike.coe (no_index G →* (A →ₗ[k] A)) _ _ _
      (Rep.ρ ((Action.res _ f).obj A)) g = A.ρ (f g) := rfl

end Res

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization : MonoidalFunctor (Action (Type u) G) (Rep k G) :=
  (ModuleCat.monoidalFree k).mapAction G

variable {k G}

@[simp]
theorem coe_linearization_obj (X : Action (Type u) G) :
    (linearization k G).obj X = (X.V →₀ k) := rfl

theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

@[simp]
theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
      (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

-- Porting note (#11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r :=
  Finsupp.mapDomain_single

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom = Finsupp.lmapDomain k k f.hom :=
  rfl

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    ((linearization k G).μ X Y).hom = (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_μ_inv_hom (X Y : Action (Type u) G) :
    (inv ((linearization k G).μ X Y)).hom = (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap := by
  rw [← Action.forget_map, Functor.map_inv]
  apply IsIso.inv_eq_of_hom_inv_id
  exact LinearMap.ext fun x ↦ LinearEquiv.symm_apply_apply _ _

@[simp]
theorem linearization_ε_hom : (linearization k G).ε.hom = Finsupp.lsingle PUnit.unit :=
  rfl

theorem linearization_ε_inv_hom_apply (r : k) :
    (inv (linearization k G).ε).hom (Finsupp.single PUnit.unit r) = r :=
  IsIso.hom_inv_id_apply (linearization k G).ε r

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps! hom_hom inv_hom]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => Finsupp.mapDomain_single

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
noncomputable abbrev ofMulAction (H : Type u) [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
noncomputable abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
noncomputable abbrev diagonal (n : ℕ) : Rep k G :=
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
def leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A where
  hom := Finsupp.lift A k G fun g => A.ρ g x
  comm _ := Finsupp.lhom_ext' fun _ => LinearMap.ext_ring <| by simp [moduleCat_simps]

theorem leftRegularHom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (Finsupp.single g r) = r • A.ρ g x := by
  simp [moduleCat_simps]

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (Finsupp.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := leftRegularHom A x
  left_inv f := Action.Hom.ext <| Finsupp.lhom_ext' fun x => LinearMap.ext_ring <| by
    simpa using (hom_comm_apply f x (Finsupp.single 1 1)).symm
  right_inv x := by simp [moduleCat_simps]

end Linearization

section Finsupp

open Finsupp

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp (α : Type u) (A : Rep k G) : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

variable (k G) in
/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
abbrev free (α : Type u) : Rep k G :=
  finsupp α (leftRegular k G)

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
@[simps]
def freeLift {α : Type u} (A : Rep k G) (f : α → A) :
    free k G α ⟶ A where
  hom := linearCombination k (fun x => A.ρ x.2 (f x.1)) ∘ₗ (finsuppProdLEquiv k).symm.toLinearMap
  comm _ := lhom_ext' fun _ => lhom_ext fun _ _ => by simp [moduleCat_simps]

lemma freeLift_hom_single_single {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (single i (single g r)) = r • A.ρ g (f i) := by
  simp [moduleCat_simps]

/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
@[simps]
def freeLiftEquiv (α : Type u) (A : Rep k G) :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := f.hom (single i (single 1 1))
  invFun := freeLift A
  left_inv x := Action.Hom.ext <| lhom_ext' fun i => lhom_ext fun j y => by
      have := (hom_comm_apply x j (single i (single 1 1))).symm
      simp_all [← map_smul]
  right_inv _ := by ext; simp [moduleCat_simps]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[ext]
lemma free_ext {α : Type u} {A : Rep k G} (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g :=
  (freeLiftEquiv α A).injective (funext_iff.2 h)

section

open MonoidalCategory

variable (A B : Rep k G) (α : Type u)

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorLeft [DecidableEq α] :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppLeft k A B α).toModuleIso
    fun _ => TensorProduct.ext <| lhom_ext fun _ _ => by
      ext
      simp [TensorProduct.finsuppLeft_apply_tmul, moduleCat_simps,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
        ModuleCat.MonoidalCategory.tensorObj]

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorRight [DecidableEq α] :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppRight k A B α).toModuleIso fun _ => TensorProduct.ext <|
    LinearMap.ext fun _ => lhom_ext fun _ _ => by
      simp [TensorProduct.finsuppRight_apply_tmul, moduleCat_simps,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
        ModuleCat.MonoidalCategory.tensorObj]

variable (k G) in
/-- The natural isormorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
@[simps! (config := .lemmasOnly) hom_hom inv_hom]
def leftRegularTensorTrivialIsoFree (α : Type u) :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  Action.mkIso (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    finsuppProdLEquiv k).toModuleIso fun _ => TensorProduct.ext <| lhom_ext fun _ _ =>
      lhom_ext fun _ _ => by simp [moduleCat_simps,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
        ModuleCat.MonoidalCategory.tensorObj]

variable {α : Type u} (i : α)

lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single
    {α : Type u} (i : α) (g : G) (r s : k) :
    (leftRegularTensorTrivialIsoFree k G α).hom.hom (single g r ⊗ₜ single i s) =
      single i (single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree, moduleCat_simps,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single {α : Type u} (i : α) (g : G) (r : k) :
    (leftRegularTensorTrivialIsoFree k G α).inv.hom (single i (single g r)) =
      TensorProduct.tmul k (single g r) (single i 1) := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one,
    moduleCat_simps, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

end
end Finsupp
end
section

open Finsupp Action

variable (k G n) [Group G]

/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the righthand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
def diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  (linearization k G).mapIso (diagonalSuccIsoTensorTrivial G n ≪≫ β_ _ _) ≪≫
    Action.mkIso (finsuppProdLEquiv k).toModuleIso fun _ => lhom_ext fun _ _ => by
      simp only [coe_V, ModuleCat.end_def, coe_linearization_obj, Action_ρ_eq_ρ,
        coe_linearization_obj_ρ, Action.tensor_ρ, trivial_V, trivial_ρ, MonoidHom.one_apply,
        ModuleCat.comp_def]
      simp [types_tensorObj, types_end]

variable {k G n}

theorem diagonalSuccIsoFree_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
    (diagonalSuccIsoFree k G n).hom.hom (single f a) =
      single (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
  simp [diagonalSuccIsoFree, moduleCat_simps, types_tensorObj]

theorem diagonalSuccIsoFree_inv_hom_single_single (g : G) (f : Fin n → G) (a : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single f (single g a)) =
      single (g • Fin.partialProd f) a := by
  simp [diagonalSuccIsoFree, coe_linearization_obj, types_tensorObj,
    diagonalSuccIsoTensorTrivial_inv_hom g f, moduleCat_simps]

theorem diagonalSuccIsoFree_inv_hom_single (g : G →₀ k) (f : Fin n → G) :
    (diagonalSuccIsoFree k G n).inv.hom (single f g) =
      lift _ k G (fun a => single (a • Fin.partialProd f) 1) g :=
  g.induction (by simpa [moduleCat_simps] using map_zero _) fun _ _ _ _ _ _ => by
    simp only [single_add, map_add, diagonalSuccIsoFree_inv_hom_single_single]
    simp_all

section
variable [Fintype G] (A : Rep k G)

/-- Given a representation `A` of a finite group `G`, this is the representation morphism `A ⟶ A`
sending `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
@[simps (config := .lemmasOnly)]
def norm (A : Rep k G) : A ⟶ A where
  hom := ∑ g : G, A.ρ g
  comm g := by
    ext x
    simpa [moduleCat_simps] using Fintype.sum_bijective (fun x => g⁻¹ * x * g)
      ((Group.mulRight_bijective g).comp (Group.mulLeft_bijective g⁻¹)) _ _ (by simp)

@[simp]
lemma norm_hom_comp_ρ (g : G) : (norm A).hom ≫ A.ρ g = (norm A).hom := by
  ext
  simpa [norm, moduleCat_simps] using Fintype.sum_bijective (g * ·)
    (Group.mulLeft_bijective g) _ _ fun _ => by simp

@[simp]
lemma ρ_comp_norm_hom (g : G) : A.ρ g ≫ (norm A).hom = (norm A).hom := by
  ext
  simpa [norm, moduleCat_simps] using Fintype.sum_bijective (· * g)
    (Group.mulRight_bijective g) _ _ fun _ => by simp

end
section MonoidalClosed
open MonoidalCategory Action

variable (A B C : Rep k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map f := {
    hom := (LinearMap.llcomp k _ _ _ f.hom)
    comm := fun x => LinearMap.ext fun _ => LinearMap.ext fun _ => by
      have := hom_comm_apply f x
      simp_all [moduleCat_simps] }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ := rfl

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps (config := .lemmasOnly)]
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f :=
    { hom := (TensorProduct.curry f.hom).flip
      comm := fun g =>
        LinearMap.ext fun x => LinearMap.ext fun y => by
        simpa using hom_comm_apply (A := A ⊗ B) f g (A.ρ g⁻¹ y ⊗ₜ[k] x) }
  invFun f :=
    { hom := (TensorProduct.uncurry k A B C f.hom.flip)
      comm := fun g => TensorProduct.ext' fun x y => by
        simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x) }
  left_inv _ := Action.Hom.ext (TensorProduct.ext' fun _ _ => rfl)
  right_inv _ := by ext; rfl

variable {A B C}

instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv (
      { homEquiv := Rep.homEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Action.Hom.ext
          (TensorProduct.ext' fun _ _ => rfl)
        homEquiv_naturality_right := fun _ _ => Action.Hom.ext (LinearMap.ext
          fun _ => LinearMap.ext fun _ => rfl) })}

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C = Rep.homEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom =
      TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

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
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv ..

variable {A B C}

@[simp]
theorem MonoidalClosed.linearHomEquiv_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom = (TensorProduct.curry f.hom).flip := by
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom = TensorProduct.curry f.hom :=
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom =
      TensorProduct.uncurry k A B C f.hom.flip := by
  simp only [linearHomEquiv, tensorLeft_obj, homEquiv_def]
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom =
      TensorProduct.uncurry k A B C f.hom :=
  TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed
end

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

variable [Monoid G]

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
  { f.hom with
    map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ f.hom f.comm r x }

/-- Functorially convert a representation of `G` into a module over `MonoidAlgebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G) where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

/-- Functorially convert a module over `MonoidAlgebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G where
  obj M := Rep.of (Representation.ofModule M)
  map f :=
    { hom := { f with map_smul' := fun r x => f.map_smul (algebraMap k _ r) x }
      comm := fun g => by ext; apply f.map_smul }

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

theorem unit_iso_comm (V : Rep k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  dsimp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
/- Porting note: rest of broken proof was
  simp only [AddEquiv.apply_eq_iff_eq, AddEquiv.apply_symm_apply,
    Representation.asModuleEquiv_symm_map_rho, Representation.ofModule_asModule_act] -/
  rw [Representation.asModuleEquiv_symm_map_rho]
  rfl

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

/-- The categorical equivalence `Rep k G ≌ ModuleCat (MonoidAlgebra k G)`. -/
def equivalenceModuleMonoidAlgebra : Rep k G ≌ ModuleCat.{u} (MonoidAlgebra k G) where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by aesop_cat)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by aesop_cat)

-- TODO Verify that the equivalence with `ModuleCat (MonoidAlgebra k G)` is a monoidal functor.
end

instance : EnoughProjectives (Rep k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.moduleCat_enoughProjectives.{u}

end Rep

namespace Representation
open Rep

variable (k G : Type u) [CommRing k] [Group G] (n : ℕ)

/-- `Gⁿ` defines a `k[G]`-basis of `k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ)` to
`single (1, g₁, g₁g₂, ..., g₁...gₙ).` -/
def ofMulActionAsModuleBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule where
  repr := (equivalenceModuleMonoidAlgebra.functor.mapIso
    (diagonalSuccIsoFree k G n)).toLinearEquiv ≪≫ₗ (finsuppLEquivFreeAsModule k G (Fin n → G)).symm

theorem ofMulAction_asModule_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionAsModuleBasis k G n)

end Representation
