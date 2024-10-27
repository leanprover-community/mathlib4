/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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

@[simp]
theorem coeFn_sum {R : Type*} [Ring R] {M N : ModuleCat R}
    {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N)) :
    ⇑(∑ i in t, f i) = ∑ i in t, ⇑(f i) :=
  LinearMap.coeFn_sum _ _

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

export Action (ρ)

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

/-- The linear map underlying a representation hom `f : A ⟶ B`, with type expressed `A →ₗ[k] B`
rather than `f.hom : A.V ⟶ B.V`. -/
def hom {A B : Rep k G} (f : A ⟶ B) : A →ₗ[k] B := f.hom

theorem hom_def {A B : Rep k G} (f : A ⟶ B) : hom f = f.hom := rfl

theorem ext {A B : Rep k G} {f g : A ⟶ B} (h : hom f = hom g) : f = g :=
  Action.hom_ext _ _ h

@[simp]
theorem hom_id (A : Rep k G) : hom (𝟙 A) = LinearMap.id := rfl

@[simp]
theorem hom_comp {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = hom g ∘ₗ (hom f) :=
  rfl

@[simp]
theorem hom_zero {A B : Rep k G} : hom (0 : A ⟶ B) = 0 := rfl

@[simp]
theorem hom_add {A B : Rep k G} (f g : A ⟶ B) : hom (f + g) = hom f + hom g := rfl

@[simp]
theorem hom_neg {A B : Rep k G} (f : A ⟶ B) : hom (-f) = -hom f := rfl

@[simp]
theorem hom_sum {A B : Rep k G} {ι : Type w} (s : Finset ι) (f : ι → (A ⟶ B)) :
    hom (∑ i in s, f i) = ∑ i in s, hom (f i) := Action.sum_hom _ _

@[simp]
theorem hom_smul {A B : Rep k G} (r : k) (f : A ⟶ B) : hom (r • f) = r • hom f := rfl

/-- Construct a representation hom using a linear map, rather than a morphism in `ModuleCat`. -/
@[simps]
def mkHom {A B : Rep k G} (f : A →ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    A ⟶ B where
  hom := f
  comm g := h g

@[simp]
theorem hom_mkHom {A B : Rep k G} (f : A →ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkHom f h) = f := rfl

/-
lemma mkHom_hom {A B : Rep k G} (f : A →ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    @DFunLike.coe (no_index (A →ₗ[k] B)) A (fun _ => B) _
      (mkHom f h).hom = f := rfl-/

/-- Construct a representation hom using a linear equivalence, rather than an
isomorphism in `ModuleCat`. -/
@[simps! hom_hom inv_hom]
abbrev mkIso {A B : Rep k G} (f : A ≃ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    A ≅ B :=
  Action.mkIso f.toModuleIso h

@[simp]
theorem hom_mkIso_hom {A B : Rep k G} (f : A ≃ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkIso f h).hom = f := rfl

@[simp]
theorem hom_mkIso_inv {A B : Rep k G} (f : A ≃ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkIso f h).inv = f.symm := rfl

theorem Action_ρ_eq_ρ {A : Rep k G} : Action.ρ A = A.ρ :=
  rfl

/-theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (f.comm g) x-/

/-theorem hom_comm_apply' {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    @DFunLike.coe (no_index A →ₗ[k] B) A (fun _ => no_index B) _ f.hom
      (@DFunLike.coe (no_index A →ₗ[k] A) A (fun _ => no_index A) _ (A.ρ g) x)
      = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (f.comm g) x-/

@[simp]
theorem hom_comm_apply {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    hom f (A.ρ g x) = B.ρ g (hom f x) :=
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
    IsTrivial (Rep.of ρ) := ⟨by simp⟩

/-- The functor equipping a module with the trivial representation. -/
@[simps]
noncomputable def trivialFunctor : ModuleCat k ⥤ Rep k G where
  obj V := trivial k G V
  map f := { hom := f, comm := fun g => rfl }

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

/-
@[simp]
theorem tensor_ρ' {A B : Rep k G} :
    DFunLike.coe (F := no_index (G →* (TensorProduct k A B →ₗ[k] TensorProduct k A B)))
      (A ⊗ B).ρ = fun g => TensorProduct.map (A.ρ g) (B.ρ g) := rfl
-/

@[simp]
theorem tensor_ρ {A B : Rep k G} : (A ⊗ B).ρ = A.ρ.tprod B.ρ := rfl

@[simp]
theorem hom_tensorHom {A B C D : Rep k G} (f : A ⟶ C) (g : B ⟶ D) :
    hom (f ⊗ g) = TensorProduct.map (hom f) (hom g) := rfl

@[simp]
theorem hom_whiskerLeft {A B : Rep k G} (C : Rep k G) (f : A ⟶ B) :
    hom (C ◁ f) = (hom f).lTensor C := rfl

@[simp]
theorem hom_whiskerRight {A B : Rep k G} (C : Rep k G) (f : A ⟶ B) :
    hom (f ▷ C) = (hom f).rTensor C := rfl

@[simp]
theorem hom_associator_hom (A B C : Rep k G) :
    hom (α_ A B C).hom = (TensorProduct.assoc k A B C).toLinearMap :=
  TensorProduct.ext_threefold <| by intros; rfl

@[simp]
theorem hom_associator_inv (A B C : Rep k G) :
    hom (α_ A B C).inv = (TensorProduct.assoc k A B C).symm.toLinearMap :=
  TensorProduct.ext <| LinearMap.ext fun _ => TensorProduct.ext' fun _ _ => rfl

@[simp]
theorem hom_leftUnitor_hom (A : Rep k G) :
    hom (λ_ A).hom = (TensorProduct.lid k A).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

@[simp]
theorem hom_leftUnitor_inv (A : Rep k G) :
    hom (λ_ A).inv = (TensorProduct.lid k A).symm.toLinearMap :=
  rfl

@[simp]
theorem hom_rightUnitor_hom (A : Rep k G) :
    hom (ρ_ A).hom = (TensorProduct.rid k A).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

@[simp]
theorem hom_rightUnitor_inv (A : Rep k G) :
    hom (ρ_ A).inv = (TensorProduct.rid k A).symm.toLinearMap :=
  rfl

@[simp]
theorem hom_braiding_hom (A B : Rep k G) :
    hom (β_ A B).hom = (TensorProduct.comm k A B).toLinearMap := rfl

@[simp]
theorem hom_braiding_inv (A B : Rep k G) :
    hom (β_ A B).inv = (TensorProduct.comm k B A).toLinearMap := rfl

end

section Res

variable {H : Type u} [Monoid H] (f : G →* H)

@[simp]
lemma coe_res_obj (A : Rep k H) :
    ((Action.res _ f).obj A : Type u) = A := rfl

/-
@[simp]
lemma res_obj_ρ_apply (A : Rep k H) (g : G) :
    DFunLike.coe (F := no_index G →* (A →ₗ[k] A)) (β := no_index fun _ => (A →ₗ[k] A))
      ((Action.res _ f).obj A).ρ g = A.ρ (f g) := rfl

lemma res_obj_ρ (A : Rep k H) :
    ((Action.res _ f).obj A).ρ = A.ρ.comp f := rfl
-/

@[simp]
lemma hom_res_map {A B : Rep k H} (φ : A ⟶ B) :
    hom ((Action.res _ f).map φ) = hom φ := rfl

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

/-- Adding this solves `simpNF` linter report at `linearization_obj_ρ`. -/
@[simp]
theorem linearization_obj_ρ' (X : Action (Type u) G) (g : G) :
    DFunLike.coe (F := no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k)))
      ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
  rfl

@[simp]
theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

/-
-- Porting note (#11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.typeρ g x) r :=
  Finsupp.mapDomain_single
-/

variable {X Y : Action (Type u) G} (f : X ⟶ Y)
/-
@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom = Finsupp.lmapDomain k k f.hom :=
  rfl
-/

@[simp]
theorem linearization_map_hom :
    hom ((linearization k G).map f) = Finsupp.lmapDomain k k f.hom :=
  rfl

/-
theorem linearization_map_hom_single (x : X.V) (r : k) :
    hom ((linearization k G).map f) (Finsupp.single x r) = Finsupp.single (f.hom x) r :=
  Finsupp.mapDomain_single
-/
/-
@[simp]
theorem linearization_μ_hom (X Y : Action (Type u) G) :
    ((linearization k G).μ X Y).hom = (finsuppTensorFinsupp' k X.V Y.V).toLinearMap :=
  rfl

@[simp]
theorem linearization_μ_inv_hom (X Y : Action (Type u) G) :
    (inv ((linearization k G).μ X Y)).hom = (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap := by
-- Porting note (#11039): broken proof was
/- simp_rw [← Action.forget_map, Functor.map_inv, Action.forget_map, linearization_μ_hom]
  apply IsIso.inv_eq_of_hom_inv_id _
  exact LinearMap.ext fun x => LinearEquiv.symm_apply_apply _ _-/
  rw [← Action.forget_map, Functor.map_inv]
  apply IsIso.inv_eq_of_hom_inv_id
  exact LinearMap.ext fun x => LinearEquiv.symm_apply_apply (finsuppTensorFinsupp' k X.V Y.V) x

@[simp]
theorem linearization_ε_hom : (linearization k G).ε.hom = Finsupp.lsingle PUnit.unit :=
  rfl

theorem linearization_ε_inv_hom_apply (r : k) :
    (inv (linearization k G).ε).hom (Finsupp.single PUnit.unit r) = r :=
  IsIso.hom_inv_id_apply (linearization k G).ε r-/

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
--@[simps!]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  mkIso (LinearEquiv.refl _ _) fun _ => Finsupp.lhom_ext' fun _ => LinearMap.ext
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
abbrev leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
  mkHom (Finsupp.lift A k G fun g => A.ρ g x)
    fun g => Finsupp.lhom_ext' fun y => LinearMap.ext_ring <| by simp

/-@[simp]
theorem leftRegularHom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (Finsupp.single g r) = r • A.ρ g x := by
  simp [ModuleCat.hom_def, coe_of]-/
/-
theorem leftRegularHom_single' {A : Rep k G} (g : G) (x : A) (r : k) :
    hom (leftRegularHom A x) (Finsupp.single g r) = r • A.ρ g x := by
  simp
-/
/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := hom f (Finsupp.single 1 1)
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun x := leftRegularHom A x
  left_inv f := ext <| Finsupp.lhom_ext' fun x : G => LinearMap.ext_ring <| by
    simpa using (hom_comm_apply f x (Finsupp.single 1 1)).symm
  right_inv x := by simp

/-
theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) (r : k) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g r) = r • A.ρ g x :=
  leftRegularHom_single ..-/
/-
@[simp]
theorem leftRegularHomEquiv_symm' {A : Rep k G} (x : A) :
    hom ((leftRegularHomEquiv A).symm x) = hom (leftRegularHom A x) := rfl
-/
end Linearization

section Finsupp

open Finsupp

/-- The representation on `α →₀ A` induced pointwise by a representation on `A`. -/
abbrev finsupp (α : Type u) (A : Rep k G) : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

variable (k G) in
/-- The representation on `α →₀ k[G]` induced pointwise by the left regular representation on
`k[G]`. -/
abbrev free (α : Type u) : Rep k G :=
  finsupp α (leftRegular k G)

/-- Given `a : α`, the representation morphism `A ⟶ (α →₀ A)` sending `x ↦ single a x`. -/
abbrev lsingle (A : Rep k G) {α : Type u} (a : α) :
    A ⟶ (A.finsupp α) :=
  mkHom (Finsupp.lsingle a) fun g => by ext x; simp

/-- Given `f : α → β`, the natural representation morphism induced from `α →₀ A` to `β →₀ A`. -/
abbrev finsuppHom (A : Rep k G) {α β : Type u} (f : α → β) :
    (A.finsupp α) ⟶ (A.finsupp β) :=
  mkHom (lmapDomain A k f) fun g => lhom_ext fun i x => by simp

/-- Given `f : α → β`, the natural representation morphism induced from `α →₀ k[G]` to `β →₀ k[G]`,
where `k[G]` is equipped with the left regular representation. -/
abbrev freeHom {α β : Type u} (f : α → β) :
    free k G α ⟶ free k G β := finsuppHom _ f

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
abbrev freeLift {α : Type u} (A : Rep k G) (f : α → A) :
    free k G α ⟶ A :=
  mkHom (linearCombination k (fun x => A.ρ x.2 (f x.1)) ∘ₗ (finsuppProdLEquiv k).symm.toLinearMap)
    fun g => lhom_ext' fun i => lhom_ext fun j y => by simp

/-@[simp]
lemma freeLift_hom_single_single {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (Finsupp.single i (Finsupp.single g r)) = r • A.ρ g (f i) := by
  simp [ModuleCat.hom_def, ← hom_def]
-/
/-
lemma freeLift_hom_single_single' {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    hom (freeLift A f) (single i (single g r)) = r • A.ρ g (f i) := by
  simp-/

/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
@[simps]
def freeLiftEquiv (α : Type u) (A : Rep k G) :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := hom f (single i (single 1 1))
  invFun := freeLift A
  left_inv x := ext <| lhom_ext' fun i => lhom_ext fun j y => by
      have := (hom_comm_apply x j (single i (single 1 1))).symm
      simp_all [← map_smul]
  right_inv x := by ext; simp
  map_add' x y := rfl
  map_smul' r x := rfl

@[ext]
lemma free_ext {α : Type u} {A : Rep k G} (f g : (free k G α) ⟶ A)
    (h : ∀ i : α, hom f (single i (single 1 1)) = hom g (single i (single 1 1))) : f = g :=
  (freeLiftEquiv α A).injective (funext_iff.2 h)

section

open MonoidalCategory

variable (A B : Rep k G) (α : Type u)

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
def finsuppTensorLeft [DecidableEq α] :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  mkIso (TensorProduct.finsuppLeft k A B α) fun g => TensorProduct.ext <|
    Finsupp.lhom_ext fun a b => by ext; simp [TensorProduct.finsuppLeft_apply_tmul]

variable {A B}

theorem finsuppTensorLeft_hom_apply_tmul [DecidableEq α] (x : α →₀ A) (y : B) :
    hom (finsuppTensorLeft A B α).hom (x ⊗ₜ y) = x.sum fun i a => Finsupp.single i (a ⊗ₜ y) :=
  TensorProduct.finsuppLeft_apply_tmul _ _

theorem finsuppTensorLeft_inv_apply_single [DecidableEq α] (a : α) (x : A) (y : B) :
    hom (finsuppTensorLeft A B α).inv (Finsupp.single a (x ⊗ₜ y)) = Finsupp.single a x ⊗ₜ y :=
  TensorProduct.finsuppLeft_symm_apply_single _ _ _

variable (A B)

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
def finsuppTensorRight [DecidableEq α] :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  mkIso (TensorProduct.finsuppRight k A B α) fun g => TensorProduct.ext <| LinearMap.ext
    fun x => Finsupp.lhom_ext fun a b => by simp [TensorProduct.finsuppRight_apply_tmul]

variable {A B}

@[simp]
theorem finsuppTensorRight_hom_apply_tmul [DecidableEq α] (x : A) (y : α →₀ B) :
    hom (finsuppTensorRight A B α).hom (x ⊗ₜ y) = y.sum fun i b => Finsupp.single i (x ⊗ₜ b) :=
  TensorProduct.finsuppRight_apply_tmul _ _

@[simp]
theorem finsuppTensorRight_inv_apply_single [DecidableEq α] (a : α) (x : A) (y : B) :
    hom (finsuppTensorRight A B α).inv (Finsupp.single a (x ⊗ₜ y)) = x ⊗ₜ Finsupp.single a y :=
  TensorProduct.finsuppRight_symm_apply_single _ _ _

variable (k G) in
/-- The natural isormorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
def tensorIsoFree (α : Type u) :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  mkIso (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    finsuppProdLEquiv k) fun g => TensorProduct.ext <| lhom_ext fun x r => lhom_ext fun y s => by
      simp [tensor_ρ]

variable {α : Type u} (i : α)

lemma tensorIsoFree_hom_hom_single_tmul_single {α : Type u} (i : α) (g : G) (r s : k) :
    hom (tensorIsoFree k G α).hom (single g r ⊗ₜ single i s) = single i (single g (r * s)) := by
  simp [tensorIsoFree]

lemma tensorIsoFree_inv_hom_single_single {α : Type u} (i : α) (g : G) (r : k) :
    hom (tensorIsoFree k G α).inv (single i (single g r)) =
      TensorProduct.tmul k (single g r) (single i 1) := by
  simp [tensorIsoFree, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

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
    mkIso (finsuppProdLEquiv k) fun g => lhom_ext fun ⟨(x : Fin n → G), (y : G)⟩ r => by
      rw [linearization_obj_ρ]
      simp only [instMonoidalCategory_tensorObj_V, coe_linearization_obj, tensor_ρ', trivial_ρ]
      simp only [trivial_V, types_tensorObj, MonoidHom.one_apply]
      simp [types_end]

variable {k G n}
/-
theorem diagonalSucc_hom_single' (f : Fin (n + 1) → G) (a : k) :
    hom (diagonalSucc k G n).hom (single f a) =
      single (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
  simp [diagonalSucc, diagonalSucc'_hom_apply', coe_linearization_obj, type_tensorObj,
    trivial_V, ofMulAction_V]-/

theorem diagonalSuccIsoFree_inv_single_single (g : G) (f : Fin n → G) (a : k) :
    hom (diagonalSuccIsoFree k G n).inv (single f (single g a)) =
      single (g • Fin.partialProd f) a := by
  simp [diagonalSuccIsoFree, coe_linearization_obj, types_tensorObj,
    diagonalSuccIsoTensorTrivial_inv_hom g f]

/-
theorem diagonalSucc_inv_single' (g : G →₀ k) (f : Fin n → G) :
    hom (diagonalSucc k G n).inv (single f g) =
      lift _ k G (fun a => single (a • Fin.partialProd f) 1) g :=
  g.induction (by simp) fun _ _ _ _ _ _ => by
    simp only [single_add, map_add, diagonalSucc_inv_single_single']
    simp_all-/
/-
variable (k G) in
/-- The functor sending a type `α` to the representation on `α →₀ k[G]` defined pointwise by the
left regular representation on `k[G]`. -/
@[simps]
def freeFunctor : Type u ⥤ Rep k G where
  obj := fun α => free k G α
  map := fun f => freeHom f
#check Action.instConcreteCategory
def freeAdjunction : freeFunctor k G ⊣ forget _ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => (freeLiftEquiv X Y).toEquiv
    homEquiv_naturality_left_symm := fun {X Y Z} f g => by
      apply free_ext
      intro i
      simp_all [types_comp, types_hom, forget]
      rw [freeLiftEquiv_symm_apply X Z (g ∘ f), mkHom_hom,
        Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.linearCombination_single, map_one,
        LinearMap.one_apply, one_smul, comp_hom, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

    homEquiv_naturality_right := _
  }

lemma freeLiftEquiv_naturality {α β : Type u} (A : Rep k G)
    (f : α → β) (g : β → A) :
    (freeLiftEquiv α A).symm (g ∘ f) = freeHom f ≫ (freeLiftEquiv β A).symm g :=
  free_ext _ _ fun i => by simp only [coe_of, freeLiftEquiv_symm_apply, mkHom_hom,
    Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Finsupp.finsuppProdLEquiv_symm_single_single, Finsupp.linearCombination_single, map_one,
    LinearMap.one_apply, one_smul, comp_hom, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
-/

/-
open MonoidalCategory in
theorem tensor_ρ' {A B : Rep k G} : @DFunLike.coe
    (no_index (G →* (TensorProduct k A B →ₗ[k] TensorProduct k A B)))
    G (fun _ => no_index (TensorProduct k A B →ₗ[k] TensorProduct k A B)) _
    (A ⊗ B).ρ = fun g => TensorProduct.map (A.ρ g) (B.ρ g) := rfl
-/

section
variable [Fintype G] (A : Rep k G)

/-- Given a representation `A` of a finite group `G`, this is the representation morphism `A ⟶ A`
sending `x ↦ ∑ A.ρ g x`. -/
def norm (A : Rep k G) : A ⟶ A :=
  mkHom (∑ g : G, A.ρ g) fun g => by
    ext x
    simpa using Fintype.sum_bijective (α := A) (fun x => g⁻¹ * x * g)
      ((Group.mulRight_bijective g).comp (Group.mulLeft_bijective g⁻¹)) _ _ (by simp)

@[simp]
lemma ρ_comp_norm (g : G) : A.ρ g ∘ₗ hom (norm A) = hom (norm A) := by
  ext
  simpa [norm] using Fintype.sum_bijective (α := A) (g * ·)
    (Group.mulLeft_bijective g) _ _ fun _ => by simp

@[simp]
lemma norm_comp_ρ (g : G) : hom (norm A) ∘ₗ A.ρ g = hom (norm A) := by
  ext
  simpa [norm] using Fintype.sum_bijective (α := A) (· * g)
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
  map f := mkHom (LinearMap.llcomp k _ _ _ (hom f))
    fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => by simp [hom_comm_apply, ← hom_def]
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ := rfl

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps (config := .lemmasOnly)]
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := mkHom (TensorProduct.curry (hom f)).flip fun g =>
    LinearMap.ext fun x => LinearMap.ext fun y => by
      simpa using hom_comm_apply (A := A ⊗ B) f g (A.ρ g⁻¹ y ⊗ₜ[k] x)
  invFun f := mkHom (TensorProduct.uncurry k A B C (hom f).flip)
      fun g => TensorProduct.ext' fun x y => by
      simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)
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
/-
@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom =
      TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl
/-
@[simp]
theorem ihom_ev_app_hom' (A B : Rep k G) :
    hom ((ihom.ev A).app B) = TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl-/

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
/-
@[simp] theorem ihom_coev_app_hom' (A B : Rep k G) :
    hom ((ihom.coev A).app B) = (TensorProduct.mk k _ _).flip := rfl
-/
-/
variable (A B C)

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
@[simps]
def MonoidalClosed.linearHomEquiv : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    toFun := (ihom.adjunction A).homEquiv _ _
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms`Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv ..

variable {A B C}
/-
-- `simpNF` times out
@[simp]
theorem MonoidalClosed.linearHomEquiv_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom = (TensorProduct.curry (hom f)).flip := by
  rfl

/-
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_hom' (f : A ⊗ B ⟶ C) :
    hom (MonoidalClosed.linearHomEquiv A B C f) = (TensorProduct.curry (hom f)).flip :=
  rfl
-/
-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom = TensorProduct.curry (hom f) :=
  rfl
/-
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom' (f : A ⊗ B ⟶ C) :
    hom (MonoidalClosed.linearHomEquivComm A B C f) = TensorProduct.curry (hom f) :=
  rfl
-/
theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom =
      TensorProduct.uncurry k A B C (hom f).flip := by
  simp [linearHomEquiv]
  rfl
/-
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_symm_hom' (f : B ⟶ A ⟶[Rep k G] C) :
    hom ((MonoidalClosed.linearHomEquiv A B C).symm f) =
      TensorProduct.uncurry k A B C (hom f).flip := by
  simp [linearHomEquiv]
  rfl
-/
theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom =
      TensorProduct.uncurry k A B C (hom f) :=
  TensorProduct.ext' fun _ _ => rfl
/-
@[simp]
theorem MonoidalClosed.linearHomEquivComm_symm_hom' (f : A ⟶ B ⟶[Rep k G] C) :
    hom ((MonoidalClosed.linearHomEquivComm A B C).symm f)
      = TensorProduct.uncurry k A B C (hom f) :=
  TensorProduct.ext' fun _ _ => rfl
-/
-/

end MonoidalClosed
end

/-
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
-/

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
  erw [Representation.asModuleEquiv_symm_map_rho]
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
