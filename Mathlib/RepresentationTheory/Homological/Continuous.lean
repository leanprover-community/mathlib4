/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/

module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology

/-!

# Continuous cohomology

We define continuous cohomology as the homology of homogeneous cochains.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `Action (TopModuleCat R) G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `ContinuousCohomology.MultiInd.d`.

## Main definition
- `ContinuousCohomology.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

universe u₁ u₂ u₃

@[expose] public section

open CategoryTheory Functor ContinuousMap TopRep

variable (R : Type u₁) (G : Type u₂) [CommRing R] [Group G] [TopologicalSpace R]
  [IsTopologicalRing R]

namespace ContinuousCohomology
open TopRep.MultiInd ContRepresentation
variable [TopologicalSpace G] [IsTopologicalGroup G]

/--
The functor which removes the zeroth
term in a cochain complex and shufts the other terms down by one.
-/
abbrev crop (C : Type*) [Category C] [Limits.HasZeroMorphisms C]:=
  (ComplexShape.embeddingUp'Add 1 1).restrictionFunctor C

/-- `homogeneousCochains R G` is the functor taking
an `R`-linear `G`-representation to the complex of homogeneous cochains. -/
abbrev homogeneousCochains : TopRep R G ⥤ CochainComplex (TopModuleCat R) ℕ :=
  (MultiInd.complex R G).asFunctor ⋙ (invariants R G).mapHomologicalComplex _
  ⋙ crop (TopModuleCat R)

instance {n : ℕ} {rep : TopRep R G} : FunLike (((homogeneousCochains R G).obj rep).X n) G
    ((MultiInd.functor R G n).obj rep) where
  coe σ               := σ.val.toFun
  coe_injective _ _ _ := by simp_all

lemma homogeneousCochains_coe_apply {n : ℕ} {rep : TopRep R G}
    (σ : ((homogeneousCochains R G).obj rep).X n) (g : G) :
    σ.val.toFun g = σ g := rfl

lemma homogeneousCochains.d_eq (n : ℕ) (rep : TopRep R G) :
    ((homogeneousCochains R G).obj rep).d n (n + 1)
    = (invariants R G).map (((MultiInd.complex R G).asFunctor.obj rep).d (n + 1) (n + 2)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma homogeneousCochains.property {n : ℕ} {rep : TopRep R G}
    (σ : ((homogeneousCochains R G).obj rep).X n) (g₁ g₂ : G) :
    σ (g₁ * g₂) = ((MultiInd.functor R G n).obj rep).ρ g₁ (σ g₂) := by
  have := σ.2 g₁⁻¹
  -- conv_lhs at this => enter [1, 1]; tactic => simp_rw [ComplexShape.embeddingUp'Add_f, HomologicalComplex.asFunctor_obj_X] at this
  simp only [ComplexShape.embeddingUp'Add_f, HomologicalComplex.asFunctor_obj_X] at this
  apply_fun DFunLike.coe (F := ((MultiInd.functor R G (n + 1)).obj rep)) at this
  have := congr_fun this g₂
  simp only [functor, comp_obj, coind₁_apply_apply, inv_inv, ContinuousMap.comp_apply, coe_mulLeft,
    coe_mk] at this
  have key := congrArg (((MultiInd.functor R G n).obj rep).ρ g₁) this
  rwa [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self] at key

/-- `continuousCohomology R G n` is the functor taking
an `R`-linear `G`-representation to its `n`-th continuous cohomology. -/
noncomputable
def _root_.continuousCohomology (n : ℕ) : TopRep R G ⥤ TopModuleCat R :=
  homogeneousCochains R G ⋙ HomologicalComplex.homologyFunctor _ _ n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `0`-homogeneous cochains are isomorphic to `Xᴳ`. -/
def kerHomogeneousCochainsZeroEquiv
    (rep : TopRep R G) (n : ℕ) (hn : n = 1) :
    (((homogeneousCochains R G).obj rep).d 0 n).hom.ker ≃L[R] (invariants R G).obj rep where
  toFun σ :=
  { val := DFunLike.coe (F := C(G, _)) σ.1.1 1
    property g := by
      subst hn
      obtain ⟨⟨σ : C(G, _), hσ⟩, hσ'⟩ := σ
      have : (rep.ρ g) (σ (g⁻¹ * 1)) = σ 1 := congr(DFunLike.coe (F := C(G, _)) $(hσ g) 1)
      have hx' : σ (g⁻¹ * 1) - σ 1 = 0 := by
        rw [LinearMap.mem_ker] at hσ'
        simp only [ComplexShape.embeddingUp'Add_f, Nat.reduceAdd,
          HomologicalComplex.asFunctor_obj_X, ContinuousLinearMap.coe_coe] at hσ'
        rw [homogeneousCochains.d_eq, MultiInd.complex_d, MultiInd.d_succ, MultiInd.d_zero] at hσ'
        simp only [comp_obj, ComplexShape.Embedding.restrictionFunctor_obj,
          HomologicalComplex.restriction_X, ComplexShape.embeddingUp'Add_f, Nat.reduceAdd,
          mapHomologicalComplex_obj_X, HomologicalComplex.asFunctor_obj_X, id_obj, NatTrans.app_sub,
          whiskerLeft_app, coind₁ι_app, NatTrans.comp_app, rightUnitor_hom_app, whiskerRight_app,
          ConcreteCategory.hom_ofHom, Category.id_comp, hom_sub, Subtype.ext_iff,
          ContIntertwiningMap.mk_invariants_apply, ContIntertwiningMap.sub_apply, coind₁ι_toFun,
          coind₁Map_toFun, ZeroMemClass.coe_zero, sub_eq_zero] at hσ'
        have := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 hσ' g⁻¹) 1
        simpa using sub_eq_zero.2 this.symm
      rw [sub_eq_zero] at hx'
      exact congr((rep.ρ g) $hx').symm.trans this
  }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := by
    refine ⟨⟨ContinuousLinearMap.const R _ x.1, fun g ↦ ContinuousMap.ext fun a ↦
      by subst hn; exact x.2 g⟩, ?_⟩
    subst hn
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro g'
    rw [homogeneousCochains.d_eq, MultiInd.complex_d]
      -- invariants_map_hom]
    simp only [id_obj, comp_obj, ComplexShape.embeddingUp'Add_f, Nat.reduceAdd,
      HomologicalComplex.asFunctor_obj_X, ComplexShape.Embedding.restrictionFunctor_obj,
      HomologicalComplex.restriction_X, mapHomologicalComplex_obj_X, ConcreteCategory.hom_ofHom,
      ContinuousLinearMap.coe_coe, ContIntertwiningMap.mk_invariants_apply, ZeroMemClass.coe_zero,
      ContinuousMap.zero_apply]
    rw [d_succ, CategoryTheory.NatTrans.app_sub, TopRep.hom_sub]
    simp [functor, ContIntertwiningMap.sub_apply]
  left_inv x := by
    subst hn
    obtain ⟨⟨x : C(G, _), hx⟩, hx'⟩ := x
    refine Subtype.ext (Subtype.ext <| ContinuousMap.ext fun a ↦ ?_)
    have hx' : x 1 - x a = 0 :=
      congr(DFunLike.coe (F := C(G, _)) (DFunLike.coe (F := C(G, _)) ($hx').1 a) 1)
    rwa [sub_eq_zero] at hx'
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.mpr ((continuous_eval_const (F := C(G, _)) 1).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := continuous_induced_rng.mpr
    (continuous_induced_rng.mpr ((ContinuousLinearMap.const R G).cont.comp continuous_subtype_val))

set_option maxHeartbeats 400000 in -- debt, will fix later
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open ShortComplex HomologyData in
/-- `H⁰_cont(G, X) ≅ Xᴳ`. -/
noncomputable
def continuousCohomologyZeroIso : (continuousCohomology R G 0) ≅ invariants R G :=
  NatIso.ofComponents (fun X ↦ (ofIsLimitKernelFork _ (by simp) _
    (TopModuleCat.isLimitKer _)).left.homologyIso ≪≫ TopModuleCat.ofIso
      (kerHomogeneousCochainsZeroEquiv R G X _ (by simp))) fun {X Y} f ↦ by
  dsimp [continuousCohomology, HomologicalComplex.homologyMap]
  rw [Category.assoc, ← Iso.inv_comp_eq]
  rw [LeftHomologyData.leftHomologyIso_inv_naturality_assoc, Iso.inv_hom_id_assoc,
    ← cancel_epi (LeftHomologyData.π _), leftHomologyπ_naturality'_assoc]
  rfl

end ContinuousCohomology
