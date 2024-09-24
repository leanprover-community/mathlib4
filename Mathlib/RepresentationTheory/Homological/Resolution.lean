/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric
import Mathlib.RepresentationTheory.Rep

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial `G`-set `EG`
is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `groupCohomology.projectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `groupCohomology.resolution.actionDiagonalSucc`
 * `groupCohomology.resolution.diagonalSucc`
 * `groupCohomology.resolution.ofMulActionBasis`
 * `classifyingSpaceUniversalCover`
 * `groupCohomology.resolution.forget₂ToModuleCatHomotopyEquiv`
 * `groupCohomology.projectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `Representation`
definition. We avoid using instances `Module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.ofMulAction k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/

/- Porting note: most altered proofs in this file involved changing `simp` to `rw` or `erw`, so
https://github.com/leanprover-community/mathlib4/issues/5026 and
https://github.com/leanprover-community/mathlib4/issues/5164 are relevant. -/

suppress_compilation

noncomputable section

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory Finsupp

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

namespace groupCohomology.resolution

open Finsupp hiding lift
open MonoidalCategory
open Fin (partialProd)

section Basis

variable (k G n) [Group G]

section Action

open Action

/-- An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).` -/
def actionDiagonalSucc (G : Type u) [Group G] :
    ∀ n : ℕ, diagonal G (n + 1) ≅ leftRegular G ⊗ Action.trivial G (Fin n → G)
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.equivOfUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSucc _ _ ≪≫
      tensorIso (Iso.refl _) (actionDiagonalSucc G n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Fin.insertNthEquiv (fun _ => G) 0).toIso fun _ => rfl)

theorem type_tensorObj {X Y : Type u} : (X ⊗ Y) = (X × Y) := rfl

theorem actionDiagonalSucc_hom_apply {G : Type u} [Group G] {n : ℕ} (f : Fin (n + 1) → G) :
    (actionDiagonalSucc G n).hom.hom f = (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction' n with n hn
  · exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  · refine Prod.ext rfl (funext fun x => ?_)
    induction' x using Fin.cases with i
    <;> simp_all only [actionDiagonalSucc, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        id_tensorHom, comp_hom, instMonoidalCategory_whiskerLeft_hom, types_comp_apply,
        whiskerLeft_apply]
    <;> rfl

theorem actionDiagonalSucc_hom_apply' {G : Type u} [Group G] {n : ℕ} (f : Fin (n + 1) → G) :
    hom (actionDiagonalSucc G n).hom f = (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) :=
  actionDiagonalSucc_hom_apply _

theorem actionDiagonalSucc_inv_apply {G : Type u} [Group G] {n : ℕ} (g : G) (f : Fin n → G) :
    (actionDiagonalSucc G n).inv.hom (g, f) = (g • Fin.partialProd f : Fin (n + 1) → G) := by
  revert g
  induction' n with n hn
  · intro g
    funext (x : Fin 1)
    simp only [Subsingleton.elim x 0, Pi.smul_apply, Fin.partialProd_zero, smul_eq_mul, mul_one]
    rfl
  · intro g
    funext x
    induction' x using Fin.cases with i
    · simp_all only [Pi.smul_apply, Fin.partialProd_zero, smul_eq_mul, mul_one]
      rfl
    · dsimp [actionDiagonalSucc, -instMonoidalCategory_tensorObj_V] at *
      simp_all only [Fin.partialProd_succ', ← mul_assoc]
      rfl

theorem actionDiagonalSucc_inv_apply' {G : Type u} [Group G] {n : ℕ} (g : G) (f : Fin n → G) :
    Action.hom (actionDiagonalSucc G n).inv (g, f) = (g • Fin.partialProd f : Fin (n + 1) → G) :=
  actionDiagonalSucc_inv_apply _ _

end Action

section Rep

open Rep

def diagonalSucc (n : ℕ) :
    diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  (linearization k G).mapIso (actionDiagonalSucc G n ≪≫ β_ _ _)
  ≪≫ mkIso' (Finsupp.finsuppProdLEquiv k)
  fun g => Finsupp.lhom_ext fun ⟨(x : Fin n → G), (y : G)⟩ r => by
    rw [linearization_obj_ρ']
    dsimp only [coe_linearization_obj, Action.tensor_typeρ, LinearMap.coe_comp,
      Function.comp_apply, lmapDomain_apply]
    simp only [mapDomain_single, Prod.map_apply, Action.trivial_typeρ_apply,
      Action.ofMulAction_apply]
    simp [Action.trivial_V, Action.ofMulAction_V, type_tensorObj]

variable {k G n}

theorem diagonalSucc_hom_single' (f : Gⁿ⁺¹) (a : k) :
    hom (diagonalSucc k G n).hom (single f a) =
      single (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
  simp [diagonalSucc, actionDiagonalSucc_hom_apply', coe_linearization_obj, type_tensorObj,
    Action.trivial_V, Action.ofMulAction_V]

@[simp]
theorem diagonalSucc_inv_single_single' (g : G) (f : Gⁿ) (a : k) :
    hom (diagonalSucc k G n).inv (Finsupp.single f (Finsupp.single g a)) =
      single (g • partialProd f) a := by
  simpa [diagonalSucc, coe_linearization_obj, type_tensorObj, Action.trivial_V,
    Action.ofMulAction_V] using congr(single $(actionDiagonalSucc_inv_apply' g f) a)

theorem diagonalSucc_inv_single' (g : G →₀ k) (f : Gⁿ) :
    hom (diagonalSucc k G n).inv (Finsupp.single f g) =
      Finsupp.lift _ k G (fun a => single (a • partialProd f) 1) g := by
  classical
  refine g.induction ?_ ?_
  · simp
  · intro x r y _ _ hx
    simp only [single_add, map_add, diagonalSucc_inv_single_single']
    simp_all

end Rep

open scoped TensorProduct

open Representation

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `TensorProduct.leftModule`, whilst that of the righthand side comes from
`Representation.asModule`. Allows us to use `Algebra.TensorProduct.basis` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    ((Fin n → G) →₀ MonoidAlgebra k G) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (diagonalSucc k G n).symm).toLinearEquiv with
    map_smul' := fun r x => by
      rw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      refine x.induction ?_ fun x y f _ _ h => ?_
      · simp only [smul_zero]
      · rw [smul_add, h]
        show _ + asAlgebraHom _ _ _ = asAlgebraHom _ _ _
        simp only [map_add, smul_single, smul_eq_mul, MonoidAlgebra.mul_def,
          asAlgebraHom_def, MonoidAlgebra.lift_apply, single_sum]
        congr
        ext g : 2
        simp [MonoidAlgebra, finsupp_single, ofMulAction_def,
          ← single_sum, ← map_smul, mapDomain, smul_sum] }

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule where
  repr := (ofMulActionBasisAux k G n).symm

theorem ofMulAction_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)

end Basis

end groupCohomology.resolution

namespace Rep

variable (n) [Group G] (A : Rep k G)

open groupCohomology.resolution

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the
et of functions `Gⁿ → A`. -/
noncomputable def diagonalHomEquiv :
    (Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSucc k G n) (Iso.refl _) ≪≫ₗ freeLiftEquiv (Fin n → G) A

variable {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
theorem diagonalHomEquiv_apply (f : Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = hom f (Finsupp.single (Fin.partialProd x) 1) := by
  simp [-coe_of, diagonalHomEquiv, diagonalSucc_inv_single_single', Linear.homCongr_apply]

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    hom ((diagonalHomEquiv n A).symm f) (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  have := diagonalSucc_hom_single' x (1 : k)
  simp_all [diagonalHomEquiv, Linear.homCongr_symm_apply]

/-- Auxiliary lemma for defining group cohomology, used to show that the isomorphism
`diagonalHomEquiv` commutes with the differentials in two complexes which compute
group cohomology. -/
theorem diagonalHomEquiv_symm_partialProd_succ (f : (Fin n → G) → A) (g : Fin (n + 1) → G)
    (a : Fin (n + 1)) :
    hom ((diagonalHomEquiv n A).symm f) (Finsupp.single (Fin.partialProd g ∘ a.succ.succAbove) 1)
      = f (Fin.contractNth a (· * ·) g) := by
  simp [-coe_of, diagonalHomEquiv_symm_apply, Fin.inv_partialProd_mul_eq_contractNth]

end Rep

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps (config := .lemmasOnly)]
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) <| G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma classifyingSpaceUniversalCover_map_hom' [Monoid G] {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : Fin (n.unop.len + 1) → G) :
    Action.hom ((classifyingSpaceUniversalCover G).map f) x = x ∘ f.unop.toOrderHom := rfl

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun n => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc, limit.isoLimitCone_hom_π, limit.lift_π, Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm

/-- As a simplicial set, `cechNerveTerminalFrom` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  NatIso.ofComponents (fun _ => Types.productIso _) fun _ =>
    Matrix.ext fun _ _ => Types.Limit.lift_π_apply (Discrete.functor fun _ ↦ G) _ _ _

variable (k)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _

/-- The augmented Čech nerve of the map from `Fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨fun _ => (1 : G),
      @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _⟩

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext terminalIsTerminal _ _)

/-- The free functor `Type u ⥤ ModuleCat.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `Fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `Fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ ModuleCat.{u} k`, the resulting augmented simplicial `k`-module has an extra
degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def groupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1)

namespace groupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) := by
  simp [d]

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (groupCohomology.resolution k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _

instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((groupCohomology.resolution k G).X n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).asModule)
      _ (ofMulActionBasis k G n)

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : Rep.hom ((groupCohomology.resolution k G).d (n + 1) n) = d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [classifyingSpaceUniversalCover_obj, Action.ofMulAction_V, groupCohomology.resolution,
    Rep.coe_linearization_obj, d_of (k := k) x, SimplicialObject.δ,
    ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), classifyingSpaceUniversalCover_map_hom',
    SimplexCategory.δ, Fin.succAboveOrderEmb]

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (groupCohomology.resolution k G)

/-- If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover of the
classifying space of `G` as a simplicial set, then take the alternating face map complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      groupCohomology.resolution.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1))

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (groupCohomology.resolution.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
abbrev ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k :=
  Rep.mkHom' (Finsupp.linearCombination _ fun _ => (1 : k)) fun g =>
    Finsupp.lhom_ext' fun _ => LinearMap.ext_ring (by simp)

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  refine Finsupp.lhom_ext fun (x : Fin 1 → G) r => ?_
  show mapDomain _ _ _ = Finsupp.linearCombination _ _ _
  simp only [HomotopyEquiv.ofIso, Iso.symm_hom, compForgetAugmented,
    SimplicialObject.augment_right, Functor.const_obj_obj, compForgetAugmentedIso, eqToIso.inv,
    HomologicalComplex.eqToHom_f]
  show mapDomain _ (single x r) _ = _
  simp [Unique.eq_default (terminal.from _), single_apply, if_pos (Subsingleton.elim _ _)]

theorem d_comp_ε : (groupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext : 1
  refine LinearMap.ext fun x => ?_
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 this _

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    groupCohomology.resolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((groupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  dsimp
  simpa using (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm

theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)

instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

end Exactness

end groupCohomology.resolution

open groupCohomology.resolution HomologicalComplex.Hom

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def groupCohomology.projectiveResolution : ProjectiveResolution (Rep.trivial k G k) where
  π := εToSingle₀ k G

instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `groupCohomology.resolution k G`. -/
def groupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((groupCohomology.resolution k G).linearYonedaObj k V).homology n :=
  (groupCohomology.projectiveResolution k G).isoExt n V

namespace groupHomology

open Rep

def d (n : ℕ) : free k G (Fin (n + 1) → G) ⟶ free k G (Fin n → G) :=
freeLift _ fun g => Finsupp.single (fun i => g i.succ) (Finsupp.single (g 0) 1)
  + Finset.univ.sum fun j : Fin (n + 1) =>
        Finsupp.single (Fin.contractNth j (· * ·) g)
          (Finsupp.single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1)))

variable {k G}

@[simp] lemma d_single (x : Gⁿ⁺¹) :
    hom (d k G n) (Finsupp.single x (Finsupp.single 1 1)) =
      Finsupp.single (fun i => x i.succ) (Finsupp.single (x 0) 1)
    + Finset.univ.sum fun j : Fin (n + 1) =>
          Finsupp.single (Fin.contractNth j (· * ·) x)
            (Finsupp.single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1))) := by
  simp [d]

lemma Fin.partialProd_contractNth_eq (g : Fin (n + 1) → G) (a : Fin (n + 1)) :
    Fin.partialProd (Fin.contractNth a (· * ·) g) = Fin.partialProd g ∘ a.succ.succAbove := by
  ext i
  refine Fin.inductionOn i ?_ ?_
  · simp only [Fin.partialProd_zero, Function.comp_apply, Fin.succ_succAbove_zero]
  · intro i hi
    simp only [Function.comp_apply, Fin.succ_succAbove_succ] at *
    rw [Fin.partialProd_succ, Fin.partialProd_succ, hi]
    rcases lt_trichotomy (i : ℕ) a with (h | h | h)
    · rw [Fin.succAbove_of_castSucc_lt, Fin.contractNth_apply_of_lt _ _ _ _ h,
        Fin.succAbove_of_castSucc_lt]
      <;> simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] <;> omega
    · rw [Fin.succAbove_of_castSucc_lt, Fin.contractNth_apply_of_eq _ _ _ _ h,
        Fin.succAbove_of_le_castSucc, Fin.castSucc_fin_succ, Fin.partialProd_succ, mul_assoc]
      <;> simp only [Fin.castSucc_lt_succ_iff, Fin.le_def, Fin.coe_castSucc] <;> omega
    · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc,
        Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.castSucc_fin_succ]
      <;> simp only [Fin.le_def, Nat.succ_eq_add_one, Fin.val_succ, Fin.coe_castSucc] <;> omega

variable (k G n)

lemma d_comp_diagonalSucc_inv_eq :
    d k G n ≫ (diagonalSucc k G n).inv =
      (diagonalSucc k G (n + 1)).inv ≫ (groupCohomology.resolution k G).d (n + 1) n :=
  free_ext _ _ fun i => by
    simp only [comp_hom, LinearMap.coe_comp, Function.comp_apply, d_single, map_add, map_sum,
      diagonalSucc_inv_single_single' (i 0), diagonalSucc_inv_single_single' (1 : G)]
    simpa [d_eq, d_of (k := k) (Fin.partialProd i), Fin.sum_univ_succ,
      Fin.partialProd_contractNth_eq]
      using congr(Finsupp.single $(by ext j; exact (Fin.partialProd_succ' i j).symm) 1)

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev barResolution : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => Rep.free k G (Fin n → G))
    (fun n => d k G n) fun n => by
    ext x
    simp only [(diagonalSucc k G _).comp_inv_eq.1 (d_comp_diagonalSucc_inv_eq k G _),
      Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc,
      Limits.zero_comp, Limits.comp_zero, Action.zero_hom]

@[simp]
theorem barResolution.d_def (n : ℕ) :
    (barResolution k G).d (n + 1) n = d k G n :=
  ChainComplex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def barResolutionIso : barResolution k G ≅ groupCohomology.resolution k G := by
/- Porting note: just needs a `refine'` now, instead of term mode -/
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    (diagonalSucc k G i).symm) ?_
  rintro i j (h : j + 1 = i)
  subst h
  simp only [ChainComplex.of_x, Iso.symm_hom, barResolution.d_def, d_comp_diagonalSucc_inv_eq]

variable {k G}
variable (A : Rep k G)

noncomputable def diagonalHomEquiv' :
    (ofMulAction k G (Fin (n + 1) → G) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k ((diagonalSucc k G n)) (Iso.refl _) ≪≫ₗ freeLiftEquiv _ _

variable {n A}

theorem diagonalHomEquiv_apply' (f : ofMulAction k G (Fin (n + 1) → G) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv' n A f x = hom f (Finsupp.single (Fin.partialProd x) 1) := by
  simp [-coe_of, diagonalHomEquiv', diagonalSucc_inv_single_single', Linear.homCongr_apply]

theorem diagonalHomEquiv'_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    hom ((diagonalHomEquiv' n A).symm f) (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  have := diagonalSucc_hom_single' x (1 : k)
  simp_all [diagonalHomEquiv', Linear.homCongr_symm_apply, freeLiftEquiv]

end groupHomology
