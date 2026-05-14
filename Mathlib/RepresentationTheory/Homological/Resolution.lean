/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.SuppressCompilation

/-!
# The standard and bar resolutions of `k` as a trivial `k`-linear `G`-representation

Given a commutative ring `k` and a group `G`, this file defines two projective resolutions of `k`
as a trivial `k`-linear `G`-representation.

The first one, the standard resolution, has objects `k[Gⁿ⁺¹]` equipped with the diagonal
representation, and differential defined by `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`.

We define this as the alternating face map complex associated to an appropriate simplicial
`k`-linear `G`-representation. This simplicial object is the `linearization` of the simplicial
`G`-set given by the universal cover of the classifying space of `G`, `EG`. We prove this
simplicial `G`-set `EG` is isomorphic to the Čech nerve of the natural arrow of `G`-sets
`G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `Rep.standardResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

We then construct the bar resolution. The `n`th object in this complex is the representation on
`Gⁿ →₀ k[G]` defined pointwise by the left regular representation on `k[G]`. The differentials are
defined by sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`.

In `RepresentationTheory.Rep` we define an isomorphism `Rep.diagonalSuccIsoFree` between
`k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ) ↦ g₀·(g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ)`.
We show that this isomorphism defines a commutative square with the bar resolution differential and
the standard resolution differential, and thus conclude that the bar resolution differential
squares to zero and that `Rep.diagonalSuccIsoFree` defines an isomorphism between the two
complexes. We carry the exactness properties across this isomorphism to conclude the bar resolution
is a projective resolution too, in `Rep.barResolution`.

In `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we then use
`Rep.barResolution` to define the inhomogeneous (co)chains of a representation, useful for
computing group (co)homology.

## Main definitions

 * `groupCohomology.resolution.ofMulActionBasis`
 * `classifyingSpaceUniversalCover`
 * `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv`
 * `Rep.standardResolution`

TODO: There's bad DefEq abuses in `Action` and the way we do `Rep.standardComplex` should be
  unified with continuous cohomology, therefore we should remove the use of `Action` in `Rep` which
  would remove all the unification hints in this file.
-/

@[expose] public noncomputable section

suppress_compilation

open CategoryTheory Finsupp
open scoped MonoidAlgebra

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps obj map]
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := ↾fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

namespace classifyingSpaceUniversalCover

open CategoryTheory.Limits

variable [Monoid G]

set_option backward.isDefEq.respectTransparency false in
/-- When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso : cechNerveTerminalFrom (Action.ofMulAction G (G)) ≅
    classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc, limit.isoLimitCone_hom_π, limit.lift_π, Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm

/-- As a simplicial set, `cechNerveTerminalFrom` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ := by
  refine NatIso.ofComponents (fun _ => Types.productIso _) fun _ => ?_
  ext : 2
  exact Matrix.ext fun _ _ => Pi.lift_π_apply (f := fun _ ↦ G) _ _ _

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
    ⟨↾fun _ => (1 : G), by cat_disch⟩

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
def Rep.standardComplex [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

namespace Rep.standardComplex

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory.Limits

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))

variable {k G}

@[simp]
theorem d_of {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) := by
  simp [d]

lemma d_single {n : ℕ} (c : Fin (n + 1) → G) (r : k) :
    d k G n (Finsupp.single c r) =
      Finset.univ.sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) (r * (-1 : k) ^ (p : ℕ)) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, map_smul, d_of]
  simp [Finset.smul_sum]

variable (k G) [Monoid G]

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (standardComplex k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _

instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((standardComplex k G).X n) := by
  classical exact inferInstanceAs <| Projective (Rep.diagonal k G (n + 1))

unif_hint where ⊢ Action.V (Action.ofMulAction G (Fin (n + 1) → G)) ≟ Fin (n + 1) → G in
set_option backward.isDefEq.respectTransparency false in
/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((standardComplex k G).d (n + 1) n).hom.toLinearMap =
    d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [standardComplex, Action.ofMulAction_V, SimplicialObject.δ, SimplexCategory.δ,
    Fin.succAboveOrderEmb, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), ← ofHom_smul, ← ofHom_sum,
    Representation.IntertwiningMap.coe_toLinearMap, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, (Representation.linearizeMap_single), smul_single,
    smul_eq_mul, mul_one]

lemma d_apply {n : ℕ} (f : (Fin (n + 1 + 1) → G) →₀ k) :
    ((standardComplex k G).d (n + 1) n).hom f = d k G (n + 1) f := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply, d_eq]; rfl

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj (standardComplex k G)

/-- If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover of the
classifying space of `G` as a simplicial set, then take the alternating face map complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      standardComplex.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ linearization k G))

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (standardComplex.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k := ofHom
  ⟨Finsupp.linearCombination _ fun _ ↦ (1 : k), fun _ ↦ Finsupp.lhom_ext'
    fun _ => LinearMap.ext_ring <| by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun (x : Fin 1 → G) r => ?_
  change mapDomain _ _ _ = Finsupp.linearCombination _ _ _
  simp only [HomotopyEquiv.ofIso, Iso.symm_hom, compForgetAugmented, compForgetAugmentedIso,
    eqToIso.inv, HomologicalComplex.eqToHom_f]
  change mapDomain _ (single x r) _ = _
  simp [Unique.eq_default (terminal.from _), single_apply, if_pos (Subsingleton.elim _ _)]

set_option backward.isDefEq.respectTransparency false in
theorem d_comp_ε : (standardComplex k G).d 1 0 ≫ ε k G = 0 := by
  ext : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp this) _

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    standardComplex k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((standardComplex k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩

theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  simpa using (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)

instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

end Exactness
end standardComplex

open HomologicalComplex.Hom standardComplex

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def standardResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := standardComplex k G
  π := εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `standardComplex k G`. -/
def standardResolution.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((standardComplex k G).linearYonedaObj k V).homology n :=
  (standardResolution k G).isoExt n V

namespace barComplex

open Rep Finsupp

variable (n)

/-- The differential from `Gⁿ⁺¹ →₀ k[G]` to `Gⁿ →₀ k[G]` in the bar resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`. -/
def d : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ :=
  freeLift k G _ fun g => single (fun i => g i.succ) (single (g 0) 1) +
    Finset.univ.sum fun j : Fin (n + 1) =>
      single (Fin.contractNth j (· * ·) g) (single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1)))

variable {k G} in
lemma d_single (x : Gⁿ⁺¹) :
    (d k G n).hom (single x (single 1 1)) = single (fun i => x i.succ) (Finsupp.single (x 0) 1) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        single (Fin.contractNth j (· * ·) x) (single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1))) := by
  simp [d, ← Representation.IntertwiningMap.toLinearMap_apply]

-- the reason the following two horrible lemmas exist is again because `Action` has bad DefEq and
-- we should be able to remove them as soon as we get rid of the use of `Action` in this file.
open scoped MonoidalCategory in
@[simp]
private lemma _root_.Representation.μ_apply_single_single_leftRegular (m : ℕ) (g : G) (r s : k)
    (f : Fin m → G) : @DFunLike.coe _ (TensorProduct k ((Action.leftRegular G).V →₀ k) _)
    (fun _ ↦ (Action.leftRegular G).V ⊗ (Fin m → G) →₀ k) _
    (Representation.LinearizeMonoidal.μ (Action.leftRegular G) (Action.trivial G (Fin m → G)))
    (single g r ⊗ₜ[k] single f s) = single (g, f) (r * s) :=
  Representation.LinearizeMonoidal.μ_apply_single_single
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f r s

open scoped MonoidalCategory in
@[simp]
private lemma _root_.Representation.linearizeMap_single_diagonal (m : ℕ) (g : G) (f : Fin m → G)
    (r : k) : @DFunLike.coe _ ((Action.leftRegular G).V ⊗ (Fin m → G) →₀ k)
    (fun _ ↦ (Action.diagonal G (m + 1)).V →₀ k) _
    (Representation.linearizeMap (Action.diagonalSuccIsoTensorTrivial G m).inv) (single (g, f) r)
    = single ((Action.diagonalSuccIsoTensorTrivial G m).inv.hom (g, f)) r :=
  Representation.linearizeMap_single (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) r

unif_hint (X : Type*) where ⊢ Action.V (Action.trivial G X) ≟ X in
unif_hint where ⊢ (HomologicalComplex.X (standardComplex k G) n).V ≟ ((Fin (n + 1) → G) →₀ k) in
set_option backward.isDefEq.respectTransparency false in
lemma d_comp_diagonalSuccIsoFree_inv_eq :
    d k G n ≫ (diagonalSuccIsoFree k G n).inv =
      (diagonalSuccIsoFree k G (n + 1)).inv ≫ (standardComplex k G).d (n + 1) n :=
  free_ext k G _ _ _ fun i ↦ by
    have eq3 : single (i 0 • Fin.partialProd fun i_1 ↦ i i_1.succ) (1 : k) =
      single (Fin.partialProd i ∘ Fin.succ) 1 := by
      congr; exact funext fun j ↦ Fin.partialProd_succ' i j |>.symm
    simp [μ_hom, d_single (k := k), Rep.mkIso_inv_hom_apply _,
      Representation.linearizeOfMulActionIso_symm_apply,
      Representation.linearizeTrivialIso_symm_apply _, d_apply (k := k),
      Representation.μ_apply_single_single_leftRegular _,
      Representation.linearizeMap_single_diagonal _]
    simp [Fin.partialProd_contractNth, Fin.sum_univ_succ, Action.ofMulAction_V, eq3]

end barComplex

open barComplex

set_option backward.isDefEq.respectTransparency false in
/-- The projective resolution of `k` as a trivial `k`-linear `G`-representation with `n`th
differential `(Gⁿ⁺¹ →₀ k[G]) → (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ)` to
`g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹·(g₀, ..., gₙ₋₁)` for
`j = 0, ..., n - 1`. -/
noncomputable abbrev barComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => free k G (Fin n → G)) (fun n => d k G n) fun m => by
    have key : (d k G (m + 1) ≫ d k G m) ≫ (diagonalSuccIsoFree k G m).inv = 0 := by
      rw [Category.assoc, d_comp_diagonalSuccIsoFree_inv_eq, ← Category.assoc,
        d_comp_diagonalSuccIsoFree_inv_eq, Category.assoc, HomologicalComplex.d_comp_d,
        Limits.comp_zero]
    exact (cancel_mono (diagonalSuccIsoFree k G m).inv).mp (by simpa using key)

namespace barComplex

theorem d_def : (barComplex k G).d (n + 1) n = d k G n := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphism between the bar resolution and standard resolution, with `n`th map
`(Gⁿ →₀ k[G]) → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)`. -/
def isoStandardComplex : barComplex k G ≅ standardComplex k G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    rw [d_def, Iso.symm_hom, Iso.symm_hom, d_comp_diagonalSuccIsoFree_inv_eq]

end barComplex

/-- The chain complex `barComplex k G` as a projective resolution of `k` as a trivial
`k`-linear `G`-representation. -/
@[simps complex]
def barResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := barComplex k G
  projective n := (inferInstance : Projective (free k G (Fin n → G)))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is the trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
bar resolution of `k`. -/
def barResolution.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((barComplex k G).linearYonedaObj k V).homology n :=
  (barResolution k G).isoExt n V

end Rep
