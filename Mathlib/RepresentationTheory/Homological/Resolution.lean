/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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

 * `Rep.diagonalSucc`
 * `Rep.ofMulActionBasis`
 * `classifyingSpaceUniversalCover`
 * `Rep.standardResolution.forget₂ToModuleCatHomotopyEquiv`
 * `Rep.standardResolution.projectiveResolution`

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
open CategoryTheory

namespace CategoryTheory.ShortComplex
open Limits
section

variable {C : Type*} [Category C] [Abelian C] (S : SnakeInput C)

theorem SnakeInput.mono_δ (h₀ : IsZero S.L₀.X₂) : Mono S.δ :=
  (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

theorem SnakeInput.epi_δ (h₃ : IsZero S.L₃.X₂) : Epi S.δ :=
  (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

theorem SnakeInput.isIso_δ (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) : IsIso S.δ :=
  @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

noncomputable def SnakeInput.δIso (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) :
    S.L₀.X₃ ≅ S.L₃.X₁ :=
  @asIso _ _ _ _ S.δ (SnakeInput.isIso_δ S h₀ h₃)

end
section

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem ShortExact.mono_δ (hi : IsZero (S.X₂.homology i)) : Mono (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi

theorem ShortExact.epi_δ (hj : IsZero (S.X₂.homology j)) : Epi (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj

theorem ShortExact.isIso_δ (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    IsIso (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

noncomputable def ShortExact.δIso (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    S.X₃.homology i ≅ S.X₁.homology j :=
  @asIso _ _ _ _ (hS.δ i j hij) (hS.isIso_δ i j hij hi hj)

end
end CategoryTheory.ShortComplex

namespace HomologicalComplex

theorem cyclesIsoSc'_cyclesMk {C : Type u} [Category C] [ConcreteCategory C] [HasForget₂ C Ab]
    [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {i j k : ι} (x : (forget₂ C Ab).obj (K.X j))
    (hi : c.prev j = i) (hk : c.next j = k) (hx : ((forget₂ C Ab).map (K.d j k)) x = 0) :
    ((forget₂ C Ab).map (K.cyclesIsoSc' i j k hi hk).hom) (K.cyclesMk x k hk hx)
      = (K.sc' i j k).cyclesMk x (by simp_all) := by
  apply (AddCommGrp.mono_iff_injective ((forget₂ C Ab).map (K.sc' i j k).iCycles)).1 inferInstance
  rw [(K.sc' i j k).i_cyclesMk x (by simp_all), ← Function.comp_apply (f := (forget₂ C Ab).map _),
    ← AddCommGrp.coe_comp, ← Functor.map_comp]
  simp

theorem cyclesIsoSc'_inv_cyclesMk {C : Type u} [Category C] [ConcreteCategory C] [HasForget₂ C Ab]
    [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {i j k : ι} (x : (forget₂ C Ab).obj (K.X j))
    (hi : c.prev j = i) (hk : c.next j = k) (hx : ((forget₂ C Ab).map (K.d j k)) x = 0) :
    ((forget₂ C Ab).map (K.cyclesIsoSc' i j k hi hk).inv) ((K.sc' i j k).cyclesMk x (by simp_all))
      = K.cyclesMk x k hk hx := by
  apply (AddCommGrp.mono_iff_injective ((forget₂ C Ab).map (K.iCycles j))).1 inferInstance
  rw [K.i_cyclesMk x k hk hx, ← Function.comp_apply (f := (forget₂ C Ab).map _),
    ← AddCommGrp.coe_comp, ← Functor.map_comp]
  simpa using (K.sc' i j k).i_cyclesMk x (by simp_all)

end HomologicalComplex
namespace LinearEquiv

variable {R₁ R₂ R₃ R₄ M₁ M₂ M₃ M₄ : Type*}
    [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
    {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
    {module_M₄ : Module R₄ M₄} {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} {σ₂₄ : R₂ →+* R₄}
    {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} {σ₁₄ : R₁ →+* R₄} {σ₂₃ : R₂ →+* R₃}
    {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
    {re₃₄ : RingHomInvPair σ₃₄ σ₄₃} {re₄₃ : RingHomInvPair σ₄₃ σ₃₄}
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃]
    {e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂} {e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄} (f : M₂ →ₛₗ[σ₂₄] M₄) (g : M₁ →ₛₗ[σ₁₃] M₃)

theorem symm_comp_eq_comp_symm_iff :
    e₃₄.symm.toLinearMap.comp f = g.comp (e₁₂.symm.toLinearMap)
      ↔ f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g := by
  rw [LinearEquiv.eq_comp_toLinearMap_symm, LinearMap.comp_assoc,
    LinearEquiv.toLinearMap_symm_comp_eq]

def kerLEquivOfCompEqComp (H : f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g) :
    LinearMap.ker f ≃ₛₗ[σ₂₁] LinearMap.ker g :=
  LinearEquiv.ofSubmodules e₁₂.symm _ _ <| by
    simp [Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp, H]

omit [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃] in
@[simp]
theorem subtype_comp_kerLEquivOfCompEqComp (H : f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g) :
    (LinearMap.ker g).subtype.comp (kerLEquivOfCompEqComp f g H).toLinearMap
      = e₁₂.symm.toLinearMap.comp (LinearMap.ker f).subtype := by ext; rfl

omit [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃] in
@[simp]
theorem subtype_comp_kerLEquivOfCompEqComp_symm
    (H : f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g) :
    (LinearMap.ker f).subtype.comp (kerLEquivOfCompEqComp f g H).symm.toLinearMap
      = e₁₂.toLinearMap.comp (LinearMap.ker g).subtype := by ext; rfl

omit [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃] in
@[simp]
theorem kerLEquivOfCompEqComp_apply
    (H : f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g) (x) :
    (kerLEquivOfCompEqComp f g H x).1 = e₁₂.symm x  := rfl

omit [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃] in
@[simp]
theorem kerLEquivOfCompEqComp_symm_apply
    (H : f.comp e₁₂.toLinearMap = e₃₄.toLinearMap.comp g) (x) :
    ((kerLEquivOfCompEqComp f g H).symm x).1
      = e₁₂ x := rfl

end LinearEquiv

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory Finsupp

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

open Finsupp hiding lift
open MonoidalCategory
open Fin (partialProd)

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] {M : ShortComplex (ModuleCat R)}
    (x : LinearMap.ker M.g)

theorem forget₂_moduleCat_mapCyclesIso (M : ShortComplex (ModuleCat R)) :
    (M.mapCyclesIso (forget₂ (ModuleCat R) Ab))
      ≪≫ (forget₂ (ModuleCat R) Ab).mapIso M.moduleCatCyclesIso
      = (ShortComplex.abCyclesIso _) := by
  apply Iso.ext
  rw [← Iso.inv_eq_inv]
  refine (cancel_mono (M.map (forget₂ (ModuleCat R) Ab)).iCycles).1 ?_
  simp only [Iso.trans_inv, Functor.mapIso_inv, ← Functor.map_comp, Category.assoc, mapCyclesIso,
    LeftHomologyData.cyclesIso_inv_comp_iCycles, abCyclesIso]
  exact congr((forget₂ (ModuleCat R) Ab).map $(moduleCatCyclesIso_inv_iCycles _))

theorem moduleCatCyclesIso_inv_apply {M : ShortComplex (ModuleCat R)}
    (x : M.X₂) (hx : M.g x = 0) :
    M.moduleCatCyclesIso.inv ⟨x, hx⟩ = M.cyclesMk x hx := by
  have := congr(Iso.inv $(forget₂_moduleCat_mapCyclesIso M))
  rw [Iso.trans_inv, Iso.comp_inv_eq] at this
  exact congr($this ⟨x, _⟩)

end CategoryTheory.ShortComplex
namespace Rep

variable (k G n) [Group G]

open Action

def diagonalSucc (n : ℕ) :
    diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  (linearization k G).mapIso (diagonalSucc' G n ≪≫ β_ _ _)
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
  simp [diagonalSucc, diagonalSucc'_hom_apply', coe_linearization_obj, type_tensorObj,
    Action.trivial_V, Action.ofMulAction_V]

@[simp]
theorem diagonalSucc_inv_single_single' (g : G) (f : Gⁿ) (a : k) :
    hom (diagonalSucc k G n).inv (Finsupp.single f (Finsupp.single g a)) =
      single (g • partialProd f) a := by
  simpa [diagonalSucc, coe_linearization_obj, type_tensorObj, Action.trivial_V,
    Action.ofMulAction_V] using congr(single $(diagonalSucc'_inv_apply' g f) a)

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

namespace Representation
open Rep

variable (k G n) [Group G]

def finsuppLEquivFreeAsModule :
    ((Fin n → G) →₀ MonoidAlgebra k G) ≃ₗ[MonoidAlgebra k G]
      ((free k G (Fin n → G))).asModule :=
  { AddEquiv.refl _ with
    map_smul' := fun r x => by
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        AddEquiv.refl_apply, RingHom.id_apply]
      refine x.induction ?_ fun x y f _ _ h => ?_
      · simp only [smul_zero]
      · rw [smul_add, h]
        show _ + asAlgebraHom _ _ _ = asAlgebraHom _ _ _
        simp only [map_add, smul_single, smul_eq_mul, MonoidAlgebra.mul_def,
          asAlgebraHom_def, MonoidAlgebra.lift_apply]
        congr
        simp [asModule, ofMulAction_def, mapDomain, smul_sum, ← single_sum] }

def freeAsModuleBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (free k G (Fin n → G)).asModule where
  repr := (finsuppLEquivFreeAsModule k G n).symm

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionAsModuleBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule where
  repr := (equivalenceModuleMonoidAlgebra.functor.mapIso (diagonalSucc k G n)).toLinearEquiv
    ≪≫ₗ (finsuppLEquivFreeAsModule k G n).symm

theorem free_asModule_free :
    Module.Free (MonoidAlgebra k G) (free k G (Fin n → G)).asModule :=
  Module.Free.of_basis (freeAsModuleBasis k G n)

theorem ofMulAction_asModule_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionAsModuleBasis k G n)

end Representation

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
def Rep.standardResolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1)

namespace Rep.standardResolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

section Differentials

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
def xIso (n : ℕ) : (standardResolution k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _

instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((standardResolution k G).X n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).asModule)
      _ (Representation.ofMulActionAsModuleBasis k G n)

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : Rep.hom ((standardResolution k G).d (n + 1) n) = d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [classifyingSpaceUniversalCover_obj, Action.ofMulAction_V, standardResolution,
    Rep.coe_linearization_obj, d_of (k := k) x, SimplicialObject.δ,
    ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), classifyingSpaceUniversalCover_map_hom',
    SimplexCategory.δ, Fin.succAboveOrderEmb]

end Differentials

section Exactness

variable [Monoid G]

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (standardResolution k G)

/-- If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover of the
classifying space of `G` as a simplicial set, then take the alternating face map complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      standardResolution.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1))

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (standardResolution.forget₂ToModuleCat k G)
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

theorem d_comp_ε : (standardResolution k G).d 1 0 ≫ ε k G = 0 := by
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
    standardResolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((standardResolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

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

open HomologicalComplex.Hom

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def projectiveResolution : ProjectiveResolution (Rep.trivial k G k) where
  π := εToSingle₀ k G

-- why's this here
instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k`. -/
def extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((standardResolution k G).linearYonedaObj k V).homology n :=
  (projectiveResolution k G).isoExt n V

end standardResolution

variable {k G} (n) [Group G] (A : Rep k G)

namespace barResolution

open Rep

variable (k G)

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

variable (k G)

lemma d_comp_diagonalSucc_inv_eq :
    d k G n ≫ (diagonalSucc k G n).inv =
      (diagonalSucc k G (n + 1)).inv ≫ (standardResolution k G).d (n + 1) n :=
  free_ext _ _ fun i => by
    simp only [comp_hom, LinearMap.coe_comp, Function.comp_apply, d_single, map_add, map_sum,
      diagonalSucc_inv_single_single' (i 0), diagonalSucc_inv_single_single' (1 : G)]
    simpa [standardResolution.d_eq, standardResolution.d_of (k := k) (Fin.partialProd i),
      Fin.sum_univ_succ, Fin.partialProd_contractNth_eq]
      using congr(Finsupp.single $(by ext j; exact (Fin.partialProd_succ' i j).symm) 1)

end barResolution

open barResolution

variable (k G)

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

namespace barResolution

@[simp]
theorem d_def (n : ℕ) :
    (barResolution k G).d (n + 1) n = d k G n :=
  ChainComplex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def isoStandardResolution : barResolution k G ≅ standardResolution k G := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    (diagonalSucc k G i).symm) ?_
  rintro i j (h : j + 1 = i)
  subst h
  simp only [ChainComplex.of_x, Iso.symm_hom, d_def, d_comp_diagonalSucc_inv_eq]

def projectiveResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := barResolution k G
  projective n := Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _ (@ModuleCat.of (MonoidAlgebra k G) _
      (Representation.free k G (Fin n → G)).asModule
      (inferInstance : AddCommGroup ((Fin n → G) →₀ G →₀ k)) _)
      _ (Representation.freeAsModuleBasis k G n)
  π := (isoStandardResolution k G).hom ≫ standardResolution.εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
bar resolution of `k`. -/
def extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((barResolution k G).linearYonedaObj k V).homology n :=
  (projectiveResolution k G).isoExt n V

end Rep.barResolution
