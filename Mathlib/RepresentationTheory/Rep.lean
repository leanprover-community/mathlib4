/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Action.Monoidal
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
  Action (ModuleCat.{u} k) G

instance (k G : Type u) [CommRing k] [Monoid G] : Linear k (Rep k G) := by infer_instance

namespace Rep

variable {k G : Type u} [CommRing k]

section

variable [Monoid G]

instance : CoeSort (Rep k G) (Type u) :=
  HasForget.hasCoeToSort _

instance (V : Rep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (Rep k G) (ModuleCat k)).obj V); infer_instance

instance (V : Rep k G) : Module k V := by
  change Module k ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

/-- Specialize the existing `Action.ρ`, changing the type to `Representation k G V`.
-/
def ρ (V : Rep k G) : Representation k G V :=
-- Porting note: was `V.ρ`
  (ModuleCat.endRingEquiv V.V).toMonoidHom.comp (Action.ρ V)

/-- Lift an unbundled representation to `Rep`. -/
def of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp ρ⟩

@[simp]
theorem coe_of {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ : Type u) = V :=
  rfl

@[simp]
lemma coe_V {V : Rep k G} : (V.V : Type u) = V := rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

theorem Action_ρ_eq_ρ {A : Rep k G} :
    Action.ρ A = (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp A.ρ :=
  rfl

@[simp]
lemma ρ_hom {X : Rep k G} (g : G) : (Action.ρ X g).hom = X.ρ g := rfl

@[simp]
lemma ofHom_ρ {X : Rep k G} (g : G) : ModuleCat.ofHom (X.ρ g) = Action.ρ X g := rfl

theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp (f.comm g)) x

variable (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)

variable {k G}

theorem trivial_def {V : Type u} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id :=
  rfl

variable (G) in
/-- The functor equipping a module with the trivial representation. -/
@[simps]
noncomputable def trivialFunctor : ModuleCat k ⥤ Rep k G where
  obj V := trivial k G V
  map f := { hom := f, comm := fun _ => rfl }

instance (X : ModuleCat k) : ((trivialFunctor G).obj X).ρ.IsTrivial where

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
noncomputable def linearization : (Action (Type u) G) ⥤ (Rep k G) :=
  (ModuleCat.free k).mapAction G

instance : (linearization k G).Monoidal := by
  dsimp only [linearization]
  infer_instance

variable {k G}

@[simp]
theorem coe_linearization_obj (X : Action (Type u) G) :
    (linearization k G).obj X = (X.V →₀ k) := rfl

theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
  rfl

@[simp]
theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
      (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  simp

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom =
    ModuleCat.ofHom (Finsupp.lmapDomain k k f.hom) :=
  rfl

theorem linearization_map_hom_single (x : X.V) (r : k) :
    ((linearization k G).map f).hom (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    (μ (linearization k G) X Y).hom =
      ModuleCat.ofHom (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_δ_hom (X Y : Action (Type u) G) :
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
@[simps! hom_hom inv_hom]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext
    fun _ => linearization_single ..

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

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
@[simps! hom_hom inv_hom]
def diagonalOneIsoLeftRegular [Monoid G] :
    diagonal k G 1 ≅ leftRegular k G :=
  Action.mkIso (Finsupp.domLCongr <| Equiv.funUnique (Fin 1) G).toModuleIso fun _ =>
    ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => by simp [diagonal]

/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
@[simps! hom_hom inv_hom]
def ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  letI : Unique H := uniqueOfSubsingleton 1
  Action.mkIso (Finsupp.LinearEquiv.finsuppUnique _ _ _).toModuleIso fun _ =>
    ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => by simp [Subsingleton.elim _ (1 : H)]

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
def leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A where
  hom := ModuleCat.ofHom <| Finsupp.lift A k G fun g => A.ρ g x
  comm _ := ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext_ring <| by simp

theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (Finsupp.single g r) = r • A.ρ g x := by
  simp

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := f.hom (Finsupp.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := leftRegularHom A x
  left_inv f := Action.Hom.ext <| ModuleCat.hom_ext <| Finsupp.lhom_ext' fun x =>
    LinearMap.ext_ring <| by simpa using (hom_comm_apply f x (Finsupp.single 1 1)).symm
  right_inv x := by simp

theorem leftRegularHomEquiv_symm_hom_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g 1) = A.ρ g x := by
  simp

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
  Rep.of (V := (α →₀ G →₀ k)) (Representation.free k G α)

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
@[simps]
def freeLift {α : Type u} (A : Rep k G) (f : α → A) :
    free k G α ⟶ A where
  hom := ModuleCat.ofHom <| linearCombination k (fun x => A.ρ x.2 (f x.1)) ∘ₗ
    (finsuppProdLEquiv k).symm.toLinearMap
  comm _ := ModuleCat.hom_ext <| lhom_ext' fun _ => lhom_ext fun _ _ => by simp

lemma freeLift_hom_single_single {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (single i (single g r)) = r • A.ρ g (f i) := by
  simp

/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
@[simps]
def freeLiftLEquiv (α : Type u) (A : Rep k G) :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := f.hom (single i (single 1 1))
  invFun := freeLift A
  left_inv x := Action.Hom.ext <| ModuleCat.hom_ext <| lhom_ext' fun i => lhom_ext fun j y => by
      have := (hom_comm_apply x j (single i (single 1 1))).symm
      simp_all [← map_smul]
  right_inv _ := by ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[ext]
lemma free_ext {α : Type u} {A : Rep k G} (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g :=
  (freeLiftLEquiv α A).injective (funext_iff.2 h)

section

open MonoidalCategory

variable (A B : Rep k G) (α : Type u)

open ModuleCat.MonoidalCategory

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorLeft [DecidableEq α] :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppLeft k A B α).toModuleIso
    fun _ => ModuleCat.hom_ext <| TensorProduct.ext <| lhom_ext fun _ _ => by
      ext
      simp only [Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ']
      simp [TensorProduct.finsuppLeft_apply_tmul, instMonoidalCategoryStruct_tensorObj,
        instMonoidalCategoryStruct_tensorHom, ModuleCat.MonoidalCategory.tensorObj]

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
@[simps! hom_hom inv_hom]
def finsuppTensorRight [DecidableEq α] :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  Action.mkIso (TensorProduct.finsuppRight k A B α).toModuleIso fun _ => ModuleCat.hom_ext <|
    TensorProduct.ext <| LinearMap.ext fun _ => lhom_ext fun _ _ => by
      simp only [Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ']
      simp [TensorProduct.finsuppRight_apply_tmul, instMonoidalCategoryStruct_tensorHom,
        instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj]

variable (k G) in
/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
@[simps! (config := .lemmasOnly) hom_hom inv_hom]
def leftRegularTensorTrivialIsoFree (α : Type u) :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  Action.mkIso (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    finsuppProdLEquiv k).toModuleIso fun _ =>
      ModuleCat.hom_ext <| TensorProduct.ext <| lhom_ext fun _ _ => lhom_ext fun _ _ => by
        simp only [Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ']
        simp [instMonoidalCategoryStruct_tensorObj,
          instMonoidalCategoryStruct_tensorHom, ModuleCat.MonoidalCategory.tensorObj]

variable {α : Type u} (i : α)

lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
    (leftRegularTensorTrivialIsoFree k G α).hom.hom (single g r ⊗ₜ single i s) =
      single i (single g (r * s)) := by
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ']
  simp [leftRegularTensorTrivialIsoFree, instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj]

lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
    (leftRegularTensorTrivialIsoFree k G α).inv.hom (single i (single g r)) =
      single g r ⊗ₜ[k] single i 1 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ']
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one,
    instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj]

end
end Finsupp

end
section Group

open Finsupp MonoidalCategory ModuleCat.MonoidalCategory
open Representation (IsTrivial)

variable [Group G] {n : ℕ}

variable (k G n) in
/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
def diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  (linearization k G).mapIso (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
      tensorIso (Iso.refl _) (linearizationTrivialIso k G (Fin n → G))

theorem diagonalSuccIsoTensorTrivial_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
    (diagonalSuccIsoTensorTrivial k G n).hom.hom (single f a) =
      single (f 0) 1 ⊗ₜ single (fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) a := by
  simp [diagonalSuccIsoTensorTrivial, instMonoidalCategoryStruct_whiskerLeft, tensorObj_def,
    ModuleCat.MonoidalCategory.whiskerLeft, instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul,
    ModuleCat.hom_id (M := ((linearization k G).obj _).V)]

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_single (g : G) (f : Fin n → G) (a b : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (single g a ⊗ₜ single f b) =
      single (g • Fin.partialProd f) (a * b) := by
  have := Action.diagonalSuccIsoTensorTrivial_inv_hom (G := G) (n := n)
  simp_all [diagonalSuccIsoTensorTrivial, instMonoidalCategoryStruct_tensorHom,
    instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj, tensorObj_def,
    ModuleCat.hom_id (M := ((linearization k G).obj _).V)]

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_left (g : G) (f : (Fin n → G) →₀ k) (r : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (single g r ⊗ₜ f) =
      Finsupp.lift ((Fin (n + 1) → G) →₀ k) k (Fin n → G)
      (fun f => single (g • Fin.partialProd f) r) f := by
  refine f.induction ?_ ?_
  · simp only [TensorProduct.tmul_zero, map_zero]
  · intro a b x _ _ hx
    simp only [lift_apply, smul_single', mul_one, TensorProduct.tmul_add, map_add, mul_comm b, hx,
      diagonalSuccIsoTensorTrivial_inv_hom_single_single, sum_single_index, zero_mul, single_zero]

theorem diagonalSuccIsoTensorTrivial_inv_hom_single_right (g : G →₀ k) (f : Fin n → G) (r : k) :
    (diagonalSuccIsoTensorTrivial k G n).inv.hom (g ⊗ₜ single f r) =
      Finsupp.lift _ k G (fun a => single (a • Fin.partialProd f) r) g := by
  refine g.induction ?_ ?_
  · simp only [TensorProduct.zero_tmul, map_zero]
  · intro a b x _ _ hx
    simp only [lift_apply, smul_single', map_add, hx, TensorProduct.add_tmul, single_zero,
      diagonalSuccIsoTensorTrivial_inv_hom_single_single, sum_single_index, zero_mul]

variable (k G n) in
/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the righthand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
def diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

theorem diagonalSuccIsoFree_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
    (diagonalSuccIsoFree k G n).hom.hom (single f a) =
      single (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
  have := diagonalSuccIsoTensorTrivial_hom_hom_single f a
  have := leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single
    (k := k) (G := G) (α := Fin n → G)
  simp_all [diagonalSuccIsoFree]

theorem diagonalSuccIsoFree_inv_hom_single_single (g : G) (f : Fin n → G) (a : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single f (single g a)) =
      single (g • Fin.partialProd f) a := by
  have := leftRegularTensorTrivialIsoFree_inv_hom_single_single (k := k) (G := G) (α := Fin n → G)
  have := diagonalSuccIsoTensorTrivial_inv_hom_single_single g f a 1
  simp_all [diagonalSuccIsoFree]

theorem diagonalSuccIsoFree_inv_hom_single (g : G →₀ k) (f : Fin n → G) :
    (diagonalSuccIsoFree k G n).inv.hom (single f g) =
      lift _ k G (fun a => single (a • Fin.partialProd f) 1) g :=
  g.induction (by simp) fun _ _ _ _ _ _ => by
    simp only [single_add, map_add, diagonalSuccIsoFree_inv_hom_single_single]
    simp_all

section MonoidalClosed
open MonoidalCategory Action

variable (A B C : Rep k G)

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
      comm := fun g => ModuleCat.hom_ext <| LinearMap.ext fun x => LinearMap.ext fun y => by
        simpa using hom_comm_apply (A := A ⊗ B) f g (A.ρ g⁻¹ y ⊗ₜ[k] x)  }
  invFun f :=
    { hom := ModuleCat.ofHom <| TensorProduct.uncurry k _ _ _ f.hom.hom.flip
      comm := fun g => ModuleCat.hom_ext <| TensorProduct.ext' fun x y => by
        simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x) }
  left_inv _ := Action.Hom.ext (ModuleCat.hom_ext <| TensorProduct.ext' fun _ _ => rfl)
  right_inv _ := by ext; rfl

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
end Group

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
        dsimp [counitIsoAddEquiv]
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

instance : EnoughProjectives (Rep k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.moduleCat_enoughProjectives.{u}

instance free_projective {G α : Type u} [Group G] :
    Projective (free k G α) :=
  equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : ℕ}

instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) :=
  Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 → G)) diagonal_succ_projective

end
end Rep
