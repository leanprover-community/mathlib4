/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RepresentationTheory.Rep

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
elsewhere. Putting this material together allows us to define `Rep.standardResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

We then construct the bar resolution. The `n`th object in this complex is the representation on
`Gⁿ →₀ k[G]` defined pointwise by the left regular representation on `k[G]`. The differentials are
defined by sending `single (g₀, ..., gₙ) (single 1 1)` to
`single (g₁, ..., gₙ) (single g₀ 1) + ∑ single (g₀, ..., gⱼgⱼ₊₁, ..., gₙ) (single 1 (-1)ʲ⁺¹)`
` + single (g₀, ..., gₙ₋₁) (single 1 (-1)ⁿ⁺¹)` for `j = 0, ... , n - 1`.

In `RepresentationTheory.Rep` we define an isomorphism `Rep.diagonalSuccIsoFree` between
`k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])` sending
`(g₀, ..., gₙ) ↦ single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`.
We show that this isomorphism defines a commutative square with the bar resolution differential and
the standard resolution differential, and thus conclude that the bar resolution differential
squares to zero and that `Rep.diagonalSuccIsoFree` defines an isomorphism between the two
complexes. We carry the exactness properties across this isomorphism to conclude the bar resolution
is a projective resolution too, in `Rep.barResolution`.

In `RepresentationTheory.Homological.GroupCohomology.Basic` and
`RepresentationTheory.Homological.GroupHomology.Basic`, we then use `Rep.barResolution` to define
the inhomogeneous (co)chains of a representation, useful for computing group (co)homology.

## Main definitions

 * `classifyingSpaceUniversalCover`
 * `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv`
 * `Rep.standardResolution`
 * `Rep.barResolution`

-/

suppress_compilation

noncomputable section

universe u v w
open CategoryTheory

lemma Fin.partialProd_contractNth_eq {G : Type*} [Monoid G] {n : ℕ}
    (g : Fin (n + 1) → G) (a : Fin (n + 1)) :
    partialProd (contractNth a (· * ·) g) = partialProd g ∘ a.succ.succAbove := by
  ext i
  refine inductionOn i ?_ ?_
  · simp only [partialProd_zero, Function.comp_apply, succ_succAbove_zero]
  · intro i hi
    simp only [Function.comp_apply, succ_succAbove_succ] at *
    rw [partialProd_succ, partialProd_succ, hi]
    rcases lt_trichotomy (i : ℕ) a with (h | h | h)
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_lt _ _ _ _ h,
        succAbove_of_castSucc_lt] <;>
      simp only [lt_def, coe_castSucc, val_succ] <;>
      omega
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_eq _ _ _ _ h,
        succAbove_of_le_castSucc, castSucc_fin_succ, partialProd_succ, mul_assoc] <;>
      simp only [castSucc_lt_succ_iff, le_def, coe_castSucc] <;>
      omega
    · rw [succAbove_of_le_castSucc, succAbove_of_le_castSucc, contractNth_apply_of_gt _ _ _ _ h,
        castSucc_fin_succ] <;>
      simp only [le_def, Nat.succ_eq_add_one, val_succ, coe_castSucc] <;>
      omega

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory Finsupp

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

open Finsupp hiding lift
open MonoidalCategory
open Fin (partialProd)
open scoped TensorProduct

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
@[simps obj]
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) <| G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma classifyingSpaceUniversalCover_map_hom [Monoid G] {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : Fin (n.unop.len + 1) → G) :
    ((classifyingSpaceUniversalCover G).map f).hom x = x ∘ f.unop.toOrderHom := rfl

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
def Rep.standardComplex [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ linearization k G)

namespace Rep.standardComplex

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

section Differentials

variable (n)

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d : (Gⁿ⁺¹ →₀ k) →ₗ[k] Gⁿ →₀ k :=
  lift (Gⁿ →₀ k) k Gⁿ⁺¹ fun g => (@Finset.univ (Fin (n + 1)) _).sum fun p =>
    single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))

variable {k G n}

@[simp]
theorem d_of (c : Gⁿ⁺¹) :
    d k G n (single c 1) =
      Finset.univ.sum fun p : Fin (n + 1) => single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) := by
  simp [d]

variable (k G n)
/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso [Monoid G] : (standardComplex k G).X n ≅ Rep.ofMulAction k G Gⁿ⁺¹ := Iso.refl _

instance x_projective [Group G] :
    Projective ((standardComplex k G).X n) :=
  inferInstanceAs <| Projective (Rep.diagonal k G (n + 1))

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq [Monoid G] : ((standardComplex k G).d (n + 1) n).hom.hom = d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  simp [classifyingSpaceUniversalCover_obj, Action.ofMulAction_V, standardComplex,
    Rep.coe_linearization_obj, d_of (k := k) x, SimplicialObject.δ,
    ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), classifyingSpaceUniversalCover_map_hom,
    SimplexCategory.δ, Fin.succAboveOrderEmb]

end Differentials

section Exactness

variable [Monoid G]

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (standardComplex k G)

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
abbrev ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k where
  hom := ModuleCat.ofHom <| Finsupp.linearCombination _ fun _ => (1 : k)
  comm _ := ModuleCat.hom_ext <| Finsupp.lhom_ext' fun _ => LinearMap.ext_ring (by simp)

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun (x : Fin 1 → G) r => ?_
  show mapDomain _ _ _ = Finsupp.linearCombination _ _ _
  simp only [HomotopyEquiv.ofIso, Iso.symm_hom, compForgetAugmented,
    SimplicialObject.augment_right, Functor.const_obj_obj, compForgetAugmentedIso, eqToIso.inv,
    HomologicalComplex.eqToHom_f]
  show mapDomain _ (single x r) _ = _
  simp [Unique.eq_default (terminal.from _), single_apply, if_pos (Subsingleton.elim _ _)]

theorem d_comp_ε : (standardComplex k G).d 1 0 ≫ ε k G = 0 := by
  ext x : 3
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact congr($this x)

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
end standardComplex

open HomologicalComplex.Hom standardComplex

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def standardResolution : ProjectiveResolution (Rep.trivial k G k) where
  π := εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is the trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k`. -/
def extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((standardComplex k G).linearYonedaObj k V).homology n :=
  (standardResolution k G).isoExt n V

namespace barComplex

open Rep Finsupp

variable (n)

/-- The differential from `Gⁿ⁺¹ →₀ k[G]` to `Gⁿ →₀ k[G]` in the bar resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ)` to
`g₀ • (g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹ • (g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹ • (g₀, ..., gₙ₋₁)` for
`j = 0, ... , n - 1`. -/
def d : free k G Gⁿ⁺¹ ⟶ free k G Gⁿ :=
  freeLift _ fun g => single (fun i => g i.succ) (single (g 0) 1) +
    Finset.univ.sum fun j : Fin (n + 1) =>
      single (Fin.contractNth j (· * ·) g) (single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1)))

variable {k G}

lemma d_single (x : Gⁿ⁺¹) :
    (d k G n).hom (single x (single 1 1)) = single (fun i => x i.succ) (Finsupp.single (x 0) 1) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        single (Fin.contractNth j (· * ·) x)  (single (1 : G) ((-1 : k) ^ ((j : ℕ) + 1))) := by
  simp [d]

variable (k G)

lemma d_comp_diagonalSuccIsoFree_inv_eq :
    d k G n ≫ (diagonalSuccIsoFree k G n).inv =
      (diagonalSuccIsoFree k G (n + 1)).inv ≫ (standardComplex k G).d (n + 1) n :=
  free_ext _ _ fun i => by
    have := d_single (k := k) (G := G)
    have := @diagonalSuccIsoFree_inv_hom_hom_single_single k G _
    simp_all only [ModuleCat.hom_comp, Action.comp_hom, LinearMap.coe_comp, Function.comp_apply,
      map_add, map_sum]
    simpa [standardComplex.d_eq, standardComplex.d_of (k := k) (Fin.partialProd i),
      Fin.sum_univ_succ, Fin.partialProd_contractNth_eq]
      using congr(Finsupp.single $(by ext j; exact (Fin.partialProd_succ' i j).symm) 1)

end barComplex

open barComplex

/-- The projective resolution of `k` as a trivial `k`-linear `G`-representation with `n`th
differential `(Gⁿ⁺¹ →₀ k[G]) → (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ)` to
`g₀ • (g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹ • (g₀, ..., gⱼgⱼ₊₁, ..., gₙ) + (-1)ⁿ⁺¹ • (g₀, ..., gₙ₋₁)` for
`j = 0, ... , n - 1`. -/
noncomputable abbrev barComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (fun n => Rep.free k G (Fin n → G)) (fun n => d k G n) fun n => by
    ext x
    simp only [(diagonalSuccIsoFree k G _).comp_inv_eq.1 (d_comp_diagonalSuccIsoFree_inv_eq k G _),
      Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc,
      Limits.zero_comp, Limits.comp_zero, Action.zero_hom]

namespace barComplex

@[simp]
theorem d_def : (barComplex k G).d (n + 1) n = d k G n := ChainComplex.of_d _ _ _ _

/-- Isomorphism between the bar resolution and standard resolution, with `n`th map
`(Gⁿ →₀ k[G]) → k[Gⁿ⁺¹]` sending `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)`. -/
def isoStandardComplex : barComplex k G ≅ standardComplex k G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (diagonalSuccIsoFree k G i).symm) fun i j => by
    rintro (rfl : j + 1 = i)
    simp only [ChainComplex.of_x, Iso.symm_hom, d_def, d_comp_diagonalSuccIsoFree_inv_eq]

end barComplex

/-- The chain complex `Rep.barComplex k G` as a projective resolution of `k` as a trivial
`k`-linear `G`-representation. -/
@[simps complex]
def barResolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := barComplex k G
  projective n := Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _ (@ModuleCat.of (MonoidAlgebra k G) _
      (Representation.free k G (Fin n → G)).asModule
      (inferInstance : AddCommGroup ((Fin n → G) →₀ G →₀ k)) _)
      _ (Representation.freeAsModuleBasis k G (Fin n → G))
  π := (isoStandardComplex k G).hom ≫ standardComplex.εToSingle₀ k G

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is the trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
bar resolution of `k`. -/
def barResolution.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((barComplex k G).linearYonedaObj k V).homology n :=
  (barResolution k G).isoExt n V

end Rep
