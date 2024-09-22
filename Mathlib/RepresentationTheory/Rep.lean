/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
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

universe v u w

open CategoryTheory

namespace ModuleCat

theorem hom_def {R : Type u} [Ring R] {X Y : ModuleCat R} : (X ⟶ Y) = (X →ₗ[R] Y) := rfl

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

lemma coe_def {V : Rep k G} : V.V = (V : Type u) := rfl
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
theorem of_V {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) :
    (of ρ).V = V :=
  rfl

@[simp]
theorem of_ρ {V : Type u} [AddCommGroup V] [Module k V] (ρ : G →* V →ₗ[k] V) : (of ρ).ρ = ρ :=
  rfl

def hom {A B : Rep k G} (f : A ⟶ B) : A →ₗ[k] B := f.hom

theorem hom_def {A B : Rep k G} (f : A ⟶ B) : f.hom = hom f := rfl

theorem hom_ext {A B : Rep k G} {f g : A ⟶ B} (h : hom f = hom g) : f = g :=
  Action.hom_ext _ _ h

@[simps]
def mkHom' {A B : Rep k G} (f : A →ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    A ⟶ B where
  hom := f
  comm g := h g

@[simp]
theorem mkHom'_hom' {A B : Rep k G} (f : A →ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkHom' f h) = f := rfl

lemma mkHom_hom' {A B : Rep k G} (f : A →ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    @DFunLike.coe (no_index (A →ₗ[k] B)) A (fun _ => B) _
      (mkHom' f h).hom = f := rfl

abbrev mkIso' {A B : Rep k G} (f : A ≃ₗ[k] B) (h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f) :
    A ≅ B :=
  Action.mkIso f.toModuleIso h

@[simp]
theorem mkIso'_hom_hom' {A B : Rep k G} (f : A ≃ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkIso' f h).hom = f := rfl

@[simp]
theorem mkIso'_inv_hom' {A B : Rep k G} (f : A ≃ₗ[k] B) {h : ∀ g, f ∘ₗ A.ρ g = B.ρ g ∘ₗ f} :
    hom (mkIso' f h).inv = f.symm := rfl

theorem Action_ρ_eq_ρ {A : Rep k G} : Action.ρ A = A.ρ :=
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
  LinearMap.ext_iff.1 (f.comm g) x

theorem hom_comm_apply' {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    @DFunLike.coe (no_index A →ₗ[k] B) A (fun _ => no_index B) _ f.hom
      (@DFunLike.coe (no_index A →ₗ[k] A) A (fun _ => no_index A) _ (A.ρ g) x)
      = B.ρ g (f.hom x) :=
  LinearMap.ext_iff.1 (f.comm g) x

theorem hom_comm_apply'' {A B : Rep k G} (f : A ⟶ B) (g : G) (x : A) :
    hom f (A.ρ g x) = B.ρ g (hom f x) :=
  hom_comm_apply f g x

@[simp]
theorem comp_hom {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = hom g ∘ₗ (hom f) :=
  rfl

@[simp]
theorem zero_hom {A B : Rep k G} : hom (0 : A ⟶ B) = 0 := rfl

@[simp]
theorem add_hom {A B : Rep k G} (f g : A ⟶ B) : hom (f + g) = hom f + hom g := rfl

@[simp]
theorem neg_hom {A B : Rep k G} (f : A ⟶ B) : hom (-f) = -hom f := rfl

@[simp]
theorem sum_hom {A B : Rep k G} {ι : Type w} (s : Finset ι) (f : ι → (A ⟶ B)) :
    hom (∑ i in s, f i) = ∑ i in s, hom (f i) := Action.sum_hom _ _

@[simp]
theorem smul_hom {A B : Rep k G} (r : k) (f : A ⟶ B) : hom (r • f) = r • hom f := rfl

variable (k G)

/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type u) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (@Representation.trivial k G V _ _ _ _)

variable {k G}

theorem trivial_def {V : Type u} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v :=
  rfl

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := Representation.IsTrivial A.ρ

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

/- Porting note: linter complains `simp` unfolds some types in the LHS, so
have removed `@[simp]`. -/
theorem MonoidalCategory.braiding_inv_apply {A B : Rep k G} (x : A) (y : B) :
    Action.Hom.hom (β_ A B).inv (TensorProduct.tmul k y x) = TensorProduct.tmul k x y :=
  rfl

section Linearization

variable (k G)

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
noncomputable def linearization : MonoidalFunctor (Action (Type u) G) (Rep k G) :=
  (ModuleCat.monoidalFree k).mapAction G

variable {k G}

theorem linearization_obj_V (X : Action (Type u) G) :
    ((linearization k G).obj X).V = ModuleCat.of k (X.V →₀ k) :=
  rfl

theorem coe_linearization_obj (X : Action (Type u) G) :
    (linearization k G).obj X = (X.V →₀ k) := rfl

@[simp]
theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
    @DFunLike.coe (no_index ((linearization k G).obj X →ₗ[k] (linearization k G).obj X))
      (no_index (linearization k G).obj X)
      (no_index fun _ => (linearization k G).obj X) _
       (((linearization k G).obj X).ρ g) = ⇑(Finsupp.lmapDomain k k (X.ρ g)) :=
  rfl

@[simp]
theorem linearization_obj_ρ' (X : Action (Type u) G) (g : G) :
    ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.typeρ g) := rfl

theorem linearization_of (X : Action (Type u) G) (g : G) (x : X.V) :
    ((linearization k G).obj X).ρ g (Finsupp.single x (1 : k))
      = Finsupp.single (X.ρ g x) (1 : k) := by
  rw [linearization_obj_ρ (k := k) (G := G) X g, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

-- Porting note (#11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (r : k) :
    ((linearization k G).obj X).ρ g (Finsupp.single x r) = Finsupp.single (X.ρ g x) r := by
  rw [linearization_obj_ρ, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

variable {X Y : Action (Type u) G} (f : X ⟶ Y)

@[simp]
theorem linearization_map_hom : ((linearization k G).map f).hom = Finsupp.lmapDomain k k f.hom :=
  rfl

@[simp]
theorem linearization_map_hom' :
    hom ((linearization k G).map f) = Finsupp.lmapDomain k k (Action.hom f) :=
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
  IsIso.hom_inv_id_apply (linearization k G).ε r

variable (k G)

/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
@[simps!]
noncomputable def linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.mk X 1) ≅ trivial k G (X →₀ k) :=
  Action.mkIso (Iso.refl _) fun _ => Finsupp.lhom_ext' fun _ => LinearMap.ext
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
  mkHom' (Finsupp.lift A k G fun g => A.ρ g x)
    fun g => Finsupp.lhom_ext' fun y => LinearMap.ext_ring <| by simp

@[simp]
theorem leftRegularHom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (Finsupp.single g r) = r • A.ρ g x := by
  simp [ModuleCat.hom_def, of_V, coe_def]

@[simp] theorem leftRegularHom_single' {A : Rep k G} (g : G) (x : A) (r : k) :
    hom (leftRegularHom A x) (Finsupp.single g r) = r • A.ρ g x := by
  simp

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
@[simps]
noncomputable def leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A where
  toFun f := hom f (Finsupp.single 1 1)
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun x := leftRegularHom A x
  left_inv f := hom_ext <| Finsupp.lhom_ext' fun x : G => LinearMap.ext_ring <| by
    simpa using (hom_comm_apply f x (Finsupp.single 1 1)).symm
  right_inv x := by simp

theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) (r : k) :
    ((leftRegularHomEquiv A).symm x).hom (Finsupp.single g r) = r • A.ρ g x :=
  leftRegularHom_single _ _ _

@[simp]
theorem leftRegularHomEquiv_symm' {A : Rep k G} (x : A) :
    hom ((leftRegularHomEquiv A).symm x) = hom (leftRegularHom A x) := rfl

end Linearization

abbrev finsupp (α : Type u) (A : Rep k G) : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

variable (k G) in
abbrev free (α : Type u) : Rep k G :=
  finsupp α (leftRegular k G)

abbrev lsingle (A : Rep k G) {α : Type u} (a : α) :
    A ⟶ (A.finsupp α) :=
  mkHom' (Finsupp.lsingle a) fun g => by ext x; simp [coe_def, of_V]

abbrev finsuppHom (A : Rep k G) {α β : Type u} (f : α → β) :
    (A.finsupp α) ⟶ (A.finsupp β) :=
  mkHom' (Finsupp.lmapDomain A k f) fun g => Finsupp.lhom_ext fun i x => by simp

abbrev freeHom {α β : Type u} (f : α → β) :
    free k G α ⟶ free k G β := finsuppHom _ f

@[simp] lemma _root_.Finsupp.finsuppProdLEquiv_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α × β) (m : M) :
    Finsupp.finsuppProdLEquiv R (Finsupp.single a m)
      = Finsupp.single a.1 (Finsupp.single a.2 m) := by
  show Finsupp.curry _ = _
  simp only [Finsupp.curry, Finsupp.single_zero, Finsupp.sum_single_index]

@[simp] lemma _root_.Finsupp.finsuppProdLEquiv_symm_single_single {α β R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] (a : α) (b : β) (m : M) :
    (Finsupp.finsuppProdLEquiv R).symm (Finsupp.single a (Finsupp.single b m))
      = Finsupp.single (a, b) m := by
  show Finsupp.uncurry _ = _
  simp only [Finsupp.uncurry, Finsupp.sum_zero_index, Finsupp.sum_single_index, Finsupp.single_zero]

abbrev freeLift {α : Type u} (A : Rep k G) (f : α → A) :
    free k G α ⟶ A :=
  mkHom' (Finsupp.linearCombination k (fun x => A.ρ x.2 (f x.1))
    ∘ₗ (Finsupp.finsuppProdLEquiv k).symm.toLinearMap)
    fun g => Finsupp.lhom_ext' fun i => Finsupp.lhom_ext fun j y => by simp

@[simp]
lemma freeLift_hom_single_single {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    (freeLift A f).hom (Finsupp.single i (Finsupp.single g r)) = r • A.ρ g (f i) := by
  simp [of_V, coe_def, ModuleCat.hom_def]

@[simp]
lemma freeLift_hom_single_single' {α : Type u} (A : Rep k G)
    (f : α → A) (i : α) (g : G) (r : k) :
    hom (freeLift A f) (Finsupp.single i (Finsupp.single g r)) = r • A.ρ g (f i) := by
  simp

@[simps] def freeLiftEquiv (α : Type u) (A : Rep k G) :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) where
  toFun f i := hom f (Finsupp.single i (Finsupp.single 1 1))
  invFun := freeLift A
  left_inv x := hom_ext <| Finsupp.lhom_ext' fun i =>
    Finsupp.lhom_ext fun j y => by
      have := (hom_comm_apply'' x j (Finsupp.single i (Finsupp.single 1 1))).symm
      simp_all [← map_smul]
  right_inv x := by ext; simp
  map_add' x y := rfl
  map_smul' r x := rfl

lemma free_ext {α : Type u} {A : Rep k G} (f g : (free k G α) ⟶ A)
  (h : ∀ i : α, hom f (Finsupp.single i (Finsupp.single 1 1))
    = hom g (Finsupp.single i (Finsupp.single 1 1))) : f = g :=
  (freeLiftEquiv α A).injective (Function.funext_iff.2 h)

lemma freeLiftEquiv_naturality {α β : Type u} (A : Rep k G)
    (f : α → β) (g : β → A) :
    (freeLiftEquiv α A).symm (g ∘ f) = freeHom f ≫ (freeLiftEquiv β A).symm g :=
  free_ext _ _ fun i => by simp

variable (B C : Action (Type u) G)
open MonoidalCategory in
example : (B ⊗ C).V = (B.V × C.V) := rfl

open MonoidalCategory in
theorem coe_tensor {A B : Rep k G} : (A ⊗ B : Rep k G) = TensorProduct k A B := rfl

open MonoidalCategory in
theorem tensor_V {A B : Rep k G} : (A ⊗ B).V = TensorProduct k A B := rfl

open MonoidalCategory in
@[simp]
theorem tensor_ρ {A B : Rep k G} (g : G) : (A ⊗ B).ρ g = TensorProduct.map (A.ρ g) (B.ρ g) := rfl

open MonoidalCategory in
theorem tensor_ρ' {A B : Rep k G} : @DFunLike.coe
    (no_index (G →* (TensorProduct k A B →ₗ[k] TensorProduct k A B)))
    G (fun _ => no_index (TensorProduct k A B →ₗ[k] TensorProduct k A B)) _
    (A ⊗ B).ρ = fun g => TensorProduct.map (A.ρ g) (B.ρ g) := rfl

variable (k G) in
open MonoidalCategory in
abbrev tprodIsoFree (α : Type u) :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  mkIso' (finsuppTensorFinsupp' k G α
    ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α)
    ≪≫ₗ Finsupp.finsuppProdLEquiv k)
    fun g => TensorProduct.ext <| Finsupp.lhom_ext fun x r => Finsupp.lhom_ext fun y s => by
    simp only [tensor_ρ]
    simp [ModuleCat.coe_of, coe_tensor,
      ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
      ModuleCat.MonoidalCategory.tensorObj]

variable {α : Type u} (i : α)

@[simp]
lemma tprodIsoFree_inv_hom_single_single' {α : Type u} (i : α) (g : G) (r : k) :
    hom (tprodIsoFree k G α).inv (Finsupp.single i (Finsupp.single g r)) =
      TensorProduct.tmul k (Finsupp.single g r) (Finsupp.single i 1) := by
  simp [finsuppTensorFinsupp'_symm_single_eq_tmul_single_one, coe_tensor]

@[simp] lemma tprodIsoFree_inv_hom_single_single {α : Type u} (i : α) (g : G) (r : k) :
    (tprodIsoFree k G α).inv.hom (Finsupp.single i (Finsupp.single g r)) =
      TensorProduct.tmul k (Finsupp.single g r) (Finsupp.single i 1) :=
  tprodIsoFree_inv_hom_single_single' _ _ _

@[simp] lemma tprodIsoFree_hom_hom_single_tmul_single' {α : Type u} (i : α) (g : G) (r s : k) :
    hom (tprodIsoFree k G α).hom (Finsupp.single g r ⊗ₜ Finsupp.single i s)
      = Finsupp.single i (Finsupp.single g (r * s)) := by
  simp [coe_tensor, of_V]

@[simp] lemma tprodIsoFree_hom_hom_single_tmul_single {α : Type u} (i : α) (g : G) (r s : k) :
    (tprodIsoFree k G α).hom.hom (Finsupp.single g r ⊗ₜ Finsupp.single i s)
      = Finsupp.single i (Finsupp.single g (r * s)) :=
  tprodIsoFree_hom_hom_single_tmul_single' _ _ _ _

end
section idfk

variable [Group G] [Fintype G] (A : Rep k G)

@[simp]
theorem _root_.ModuleCat.coeFn_sum {R : Type*} [Ring R] {M N : ModuleCat R}
    {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N)) :
    ⇑(∑ i in t, f i) = ∑ i in t, ⇑(f i) :=
  LinearMap.coeFn_sum _ _

abbrev norm (A : Rep k G) : A ⟶ A :=
  mkHom' (∑ g : G, A.ρ g) fun g => by
    ext x
    simpa using Fintype.sum_bijective (α := A) (fun x => g⁻¹ * x * g)
      ((Group.mulRight_bijective g).comp (Group.mulLeft_bijective g⁻¹)) _ _ (by simp)

end idfk
section MonoidalClosed
open MonoidalCategory Action

variable [Group G] (A B C : Rep k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map := fun {X} {Y} f => mkHom' (LinearMap.llcomp k _ _ _ (hom f))
    fun g => LinearMap.ext fun x => LinearMap.ext fun y => by simp [hom_comm_apply'', hom_def]
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps (config := .lemmasOnly)]
def homEquiv (A B C : Rep k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := mkHom' (TensorProduct.curry (hom f)).flip fun g =>
    LinearMap.ext fun x => LinearMap.ext fun y => by
      have :=  hom_comm_apply'' (A := A ⊗ B) f g (A.ρ g⁻¹ y ⊗ₜ[k] x)
      simp only [tensor_ρ] at this
      simp_all [coe_tensor]
  invFun f := mkHom' (TensorProduct.uncurry k A B C (hom f).flip)
      fun g => TensorProduct.ext' fun x y => by
      simp only [tensor_ρ]
      simpa [coe_tensor, hom_def, coe_def]
        using LinearMap.ext_iff.1 (hom_comm_apply' f g y) (A.ρ g x)
  left_inv f := Action.Hom.ext (TensorProduct.ext' fun _ _ => rfl)
  right_inv f := by ext; rfl

variable {A B C}

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_apply_hom (f : A ⊗ B ⟶ C) :
    hom (homEquiv A B C f) = (TensorProduct.curry (hom f)).flip := rfl

/-- Porting note: if we generate this with `@[simps]` the linter complains some types in the LHS
simplify. -/
theorem homEquiv_symm_apply_hom (f : B ⟶ (Rep.ihom A).obj C) :
    hom ((homEquiv A B C).symm f) = TensorProduct.uncurry k A B C (hom f).flip := rfl

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
    ((ihom.ev A).app B).hom
      = TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl

@[simp]
theorem ihom_ev_app_hom' (A B : Rep k G) :
    hom ((ihom.ev A).app B) = TensorProduct.uncurry k A (A →ₗ[k] B) B LinearMap.id.flip := by
  ext; rfl

@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

@[simp] theorem ihom_coev_app_hom' (A B : Rep k G) :
    hom ((ihom.coev A).app B) = (TensorProduct.mk k _ _).flip := rfl

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
    (MonoidalClosed.linearHomEquiv A B C f).hom = (TensorProduct.curry (hom f)).flip :=
  rfl

@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_hom' (f : A ⊗ B ⟶ C) :
    hom (MonoidalClosed.linearHomEquiv A B C f) = (TensorProduct.curry (hom f)).flip :=
  rfl

-- `simpNF` times out
@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom = TensorProduct.curry (hom f) :=
  rfl

@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquivComm_hom' (f : A ⊗ B ⟶ C) :
    hom (MonoidalClosed.linearHomEquivComm A B C f) = TensorProduct.curry (hom f) :=
  rfl

theorem MonoidalClosed.linearHomEquiv_symm_hom (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom =
      TensorProduct.uncurry k A B C (hom f).flip := by
  simp [linearHomEquiv]
  rfl

@[simp, nolint simpNF]
theorem MonoidalClosed.linearHomEquiv_symm_hom' (f : B ⟶ A ⟶[Rep k G] C) :
    hom ((MonoidalClosed.linearHomEquiv A B C).symm f) =
      TensorProduct.uncurry k A B C (hom f).flip := by
  simp [linearHomEquiv]
  rfl

theorem MonoidalClosed.linearHomEquivComm_symm_hom (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom
      = TensorProduct.uncurry k A B C (hom f) :=
  TensorProduct.ext' fun _ _ => rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_symm_hom' (f : A ⟶ B ⟶[Rep k G] C) :
    hom ((MonoidalClosed.linearHomEquivComm A B C).symm f)
      = TensorProduct.uncurry k A B C (hom f) :=
  TensorProduct.ext' fun _ _ => rfl


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
    ModuleCat.of (MonoidAlgebra k G) (Representation.asModule V.ρ)
      ⟶ ModuleCat.of (MonoidAlgebra k G) (Representation.asModule W.ρ) :=
  { f.hom with
    map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V W V.ρ W.ρ f.hom f.comm r x }

/-- Functorially convert a representation of `G` into a module over `MonoidAlgebra k G`. -/
def toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat.{u} (MonoidAlgebra k G) where
  obj V := ModuleCat.of _ (Representation.asModule V.ρ)
  map f := toModuleMonoidAlgebraMap f

/-- Functorially convert a module over `MonoidAlgebra k G` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat.{u} (MonoidAlgebra k G) ⥤ Rep k G where
  obj M := Rep.of (Representation.ofModule M)
  map f :=
    { hom := { f with map_smul' := fun r x => f.map_smul (algebraMap k _ r) x }
      comm := fun g => by ext; apply f.map_smul }

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{u} (MonoidAlgebra k G)) :
    (ofModuleMonoidAlgebra.obj M) = RestrictScalars k (MonoidAlgebra k G) M :=
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
def unitIsoAddEquiv {V : Rep k G} :
    V ≃+ ((toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V) := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  refine (Representation.asModuleEquiv V.ρ).symm.trans ?_
  exact (RestrictScalars.addEquiv k (MonoidAlgebra k G) _).symm

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

end Rep
