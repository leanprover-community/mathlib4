/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RepresentationTheory.Rep
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

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
`G`-representation. This simplicial object is the `Rep.linearization` of the simplicial `G`-set
given by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial
`G`-set `EG` is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `groupCohomology.projectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

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

open scoped TensorProduct

open Representation

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.actionDiagonalSucc := Action.diagonalSuccIsoTensorTrivial

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.actionDiagonalSucc_hom_apply :=
  Action.diagonalSuccIsoTensorTrivial_hom_hom_apply

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.actionDiagonalSucc_inv_apply :=
  Action.diagonalSuccIsoTensorTrivial_inv_hom_apply

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.diagonalSucc := Rep.diagonalSuccIsoTensorTrivial

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.diagonalSucc_hom_single :=
  Rep.diagonalSuccIsoTensorTrivial_hom_hom_single

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.diagonalSucc_inv_single_single :=
  Rep.diagonalSuccIsoTensorTrivial_inv_hom_single_single

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.diagonalSucc_inv_single_left :=
  Rep.diagonalSuccIsoTensorTrivial_inv_hom_single_left

@[deprecated (since := "2025-02-06")]
alias groupCohomology.resolution.diagonalSucc_inv_single_right :=
  Rep.diagonalSuccIsoTensorTrivial_inv_hom_single_right

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `TensorProduct.leftModule`, whilst that of the righthand side comes from
`Representation.asModule`. Allows us to use `Algebra.TensorProduct.basis` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  haveI e := (Rep.equivalenceModuleMonoidAlgebra.1.mapIso
    (Rep.diagonalSuccIsoTensorTrivial k G n).symm).toLinearEquiv
  { e with
    map_smul' := fun r x => by
      rw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul e]
      congr 1
      /- Porting note (https://github.com/leanprover-community/mathlib4/issues/11039): broken proof was
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← ofMulAction_self_smul_eq_mul, smul_tprod_one_asModule]
      · rw [smul_add, hz, hy, smul_add] -/
      show _ = Representation.asAlgebraHom (tensorObj (Rep.leftRegular k G)
        (Rep.trivial k G ((Fin n → G) →₀ k))).ρ r _
      refine x.induction_on ?_ (fun x y => ?_) fun y z hy hz => ?_
      · rw [smul_zero, map_zero]
      · rw [TensorProduct.smul_tmul', smul_eq_mul, ← ofMulAction_self_smul_eq_mul]
        exact (smul_tprod_one_asModule (Representation.ofMulAction k G G) r x y).symm
      · rw [smul_add, hz, hy, map_add] }

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Basis.map
    (Algebra.TensorProduct.basis (MonoidAlgebra k G)
      (Finsupp.basisSingleOne : Basis (Fin n → G) k ((Fin n → G) →₀ k)))
    (ofMulActionBasisAux k G n)

theorem ofMulAction_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)

end Basis

end groupCohomology.resolution

namespace Rep

variable (n) [Group G] (A : Rep k G)

open groupCohomology.resolution

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
noncomputable def diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k
        ((diagonalSuccIsoTensorTrivial k G n).trans
          ((Representation.ofMulAction k G G).repOfTprodIso 1))
        (Iso.refl _) ≪≫ₗ
      (Rep.MonoidalClosed.linearHomEquivComm _ _ _ ≪≫ₗ Rep.leftRegularHomEquiv _) ≪≫ₗ
    (Finsupp.llift A k k (Fin n → G)).symm

variable {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
theorem diagonalHomEquiv_apply (f : Rep.diagonal k G (n + 1) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = f.hom (Finsupp.single (Fin.partialProd x) 1) := by
/- Porting note (https://github.com/leanprover-community/mathlib4/issues/11039): broken proof was
  unfold diagonalHomEquiv
  simpa only [LinearEquiv.trans_apply, Rep.leftRegularHomEquiv_apply,
    MonoidalClosed.linearHomEquivComm_hom, Finsupp.llift_symm_apply, TensorProduct.curry_apply,
    Linear.homCongr_apply, Iso.refl_hom, Iso.trans_inv, Action.comp_hom, ModuleCat.comp_def,
    LinearMap.comp_apply, Representation.repOfTprodIso_inv_apply,
    diagonalSucc_inv_single_single (1 : G) x, one_smul, one_mul] -/
  change f.hom ((diagonalSuccIsoTensorTrivial k G n).inv.hom
    (Finsupp.single 1 1 ⊗ₜ[k] Finsupp.single x 1)) = _
  rw [diagonalSuccIsoTensorTrivial_inv_hom_single_single, one_smul, one_mul]

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  unfold diagonalHomEquiv
/- Porting note (https://github.com/leanprover-community/mathlib4/issues/11039): broken proof was
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Rep.leftRegularHomEquiv_symm_apply, Linear.homCongr_symm_apply, Action.comp_hom, Iso.refl_inv,
    Category.comp_id, Rep.MonoidalClosed.linearHomEquivComm_symm_hom, Iso.trans_hom,
    ModuleCat.comp_def, LinearMap.comp_apply, Representation.repOfTprodIso_apply,
    diagonalSucc_hom_single x (1 : k), TensorProduct.uncurry_apply, Rep.leftRegularHom_hom,
    Finsupp.lift_apply, ihom_obj_ρ_def, Rep.ihom_obj_ρ_apply, Finsupp.sum_single_index, zero_smul,
    one_smul, Rep.of_ρ, Rep.Action_ρ_eq_ρ, Rep.trivial_def (x 0)⁻¹, Finsupp.llift_apply A k k] -/
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    leftRegularHomEquiv_symm_apply, Linear.homCongr_symm_apply, Iso.trans_hom, Iso.refl_inv,
    Category.comp_id, Action.comp_hom, MonoidalClosed.linearHomEquivComm_symm_hom,
    ModuleCat.hom_comp, LinearMap.comp_apply, Action.tensorObj_V,
    diagonalSuccIsoTensorTrivial_hom_hom_single x 1]
  -- The prototype linter that checks if `erw` could be replaced with `rw` would time out
  -- if it replaces the next `erw`s with `rw`s. So we focus down on the relevant part.
  conv_lhs =>
    erw [TensorProduct.uncurry_apply, Finsupp.lift_apply, Finsupp.sum_single_index]
    · simp only [one_smul]
      erw [Representation.linHom_apply]
      simp only [LinearMap.comp_apply, MonoidHom.one_apply, Module.End.one_apply]
      erw [Finsupp.llift_apply]
      rw [Finsupp.lift_apply]
      erw [Finsupp.sum_single_index]
      · rw [one_smul]
      · rw [zero_smul]
    · rw [zero_smul]

/-- Auxiliary lemma for defining group cohomology, used to show that the isomorphism
`diagonalHomEquiv` commutes with the differentials in two complexes which compute
group cohomology. -/
theorem diagonalHomEquiv_symm_partialProd_succ (f : (Fin n → G) → A) (g : Fin (n + 1) → G)
    (a : Fin (n + 1)) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single (Fin.partialProd g ∘ a.succ.succAbove) 1)
      = f (Fin.contractNth a (· * ·) g) := by
  rw [diagonalHomEquiv_symm_apply]
  simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.partialProd_zero, map_one,
    Fin.succ_succAbove_succ, Module.End.one_apply, Fin.partialProd_succ]
  congr
  ext
  rw [← Fin.partialProd_succ, Fin.inv_partialProd_mul_eq_contractNth]

end Rep

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps obj map]
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

namespace classifyingSpaceUniversalCover

open CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
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
    (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)

namespace groupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory.Limits

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
theorem d_eq (n : ℕ) : ((groupCohomology.resolution k G).d (n + 1) n).hom =
    ModuleCat.ofHom (d k G (n + 1)) := by
  refine ModuleCat.hom_ext <| Finsupp.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [Action.ofMulAction_V, groupCohomology.resolution, SimplicialObject.δ,
    ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), SimplexCategory.δ, Fin.succAboveOrderEmb]

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
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G))

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
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k where
  hom := ModuleCat.ofHom <| Finsupp.linearCombination _ fun _ => (1 : k)
  comm g := ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext_ring (by
    show
      Finsupp.linearCombination k (fun _ => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.linearCombination k (fun _ => (1 : k)) (Finsupp.single _ _)
    simp only [Finsupp.mapDomain_single, Finsupp.linearCombination_single])

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  dsimp
  convert Category.id_comp (X := (forget₂ToModuleCat k G).X 0) _
  · dsimp only [HomotopyEquiv.ofIso, compForgetAugmentedIso]
    simp only [Iso.symm_hom, eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_refl]
  ext : 1
  trans (linearCombination _ fun _ => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _)).hom
  · erw [Finsupp.lmapDomain_linearCombination (α := Fin 1 → G) (R := k) (α' := ⊤_ Type u)
        (v := fun _ => (1 : k)) (v' := fun _ => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · rw [ModuleCat.hom_comp]
    congr
    · ext x
      dsimp +unfoldPartialApp [HomotopyEquiv.ofIso,
        Finsupp.LinearEquiv.finsuppUnique]
      rw [@Unique.eq_default _ Types.terminalIso.toEquiv.unique x]
      simp
    · exact @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _

theorem d_comp_ε : (groupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext : 1
  refine ModuleCat.hom_ext <| LinearMap.ext fun x => ?_
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp this) _

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
  complex := resolution k G
  π := εToSingle₀ k G

instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `groupCohomology.resolution k G`. -/
def groupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((groupCohomology.resolution k G).linearYonedaObj k V).homology n :=
  (groupCohomology.projectiveResolution k G).isoExt n V
