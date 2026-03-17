/-
Copyright (c) 2025 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.Topology.ContinuousMap.Algebra

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

@[expose] public section

open CategoryTheory Functor ContinuousMap

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

namespace ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable {R G} in
/-- The `G` representation `C(G, rep)` given a representation `rep`.
The `G` action is defined by `g • f := x ↦ g • f (g⁻¹ * x)`. -/
abbrev Iobj (rep : Action (TopModuleCat R) G) : Action (TopModuleCat R) G where
  V := .of R C(G, rep.V)
  ρ :=
  { toFun g := TopModuleCat.ofHom
      { toFun f := .comp (rep.ρ g).hom (f.comp (Homeomorph.mulLeft g⁻¹))
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp
        cont := (continuous_postcomp _).comp (continuous_precomp _) }
    map_one' := ConcreteCategory.ext (by ext; simp)
    map_mul' _ _ := ConcreteCategory.ext (by ext; simp [mul_assoc]) }

lemma Iobj_ρ_apply (rep : Action (TopModuleCat R) G) (g f x) :
    ((Iobj rep).ρ g).hom f x = (rep.ρ g).hom (f (g⁻¹ * x)) := rfl

/-- The functor taking a representation `rep` to the representation `C(G, rep)`. -/
@[simps]
def I : Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G where
  obj := Iobj
  map {M N} φ :=
  { hom := TopModuleCat.ofHom (ContinuousLinearMap.compLeftContinuous _ _ φ.hom.hom)
    comm g := by
      ext f g'
      change (M.ρ g ≫ φ.hom).hom (f (g⁻¹ * g')) = (φ.hom ≫ N.ρ g).hom (f (g⁻¹ * g'))
      rw [φ.comm] }
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (I R G).Additive where
instance : (I R G).Linear R where

/-- The constant function `rep ⟶ C(G, rep)` as a natural transformation. -/
@[simps]
def const : 𝟭 _ ⟶ I R G where
  app _ := { hom := TopModuleCat.ofHom (.const _ _), comm _ := rfl }
  naturality _ _ _ := rfl

namespace MultiInd

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The n-th functor taking `M` to `C(G, C(G,...,C(G, M)))` (with n `G`s).
These functors form a complex, see `MultiInd.complex`. -/
def functor : ℕ → Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G
  | 0     => 𝟭 _
  | n + 1 => functor n ⋙ I R G

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The differential map in `MultiInd.complex`. -/
def d : ∀ n : ℕ, functor R G n ⟶ functor R G (n + 1)
  | 0     => const R G
  | n + 1 => whiskerLeft (functor R G (n + 1)) (const R G) - (by exact whiskerRight (d n) (I R G))

lemma d_zero : d R G 0 = const R G := rfl

lemma d_succ (n : ℕ) :
    d R G (n + 1) = whiskerLeft (functor R G (n + 1)) (const R G) -
      (by exact whiskerRight (d R G n) (I R G)) := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma d_comp_d (n : ℕ) :
    d R G n ≫ d R G (n + 1) = 0 := by
  induction n with
  | zero =>
    rw [d_succ, Preadditive.comp_sub, sub_eq_zero]
    rfl
  | succ n ih =>
    rw [d_succ R G (n + 1), Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp, ← whiskerRight_comp, ih,
      Functor.whiskerRight_zero, sub_zero, sub_eq_zero]
    rfl

/-- The complex of functors whose behaviour pointwise takes an `R`-linear `G`-representation `M`
to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯`
The `G`-invariant submodules of it is the homogeneous cochains (shifted by one). -/
def complex : CochainComplex (Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G) ℕ :=
  CochainComplex.of (functor R G) (d R G) (d_comp_d R G)

end MultiInd

/-- The functor taking an `R`-linear `G`-representation to its `G`-invariant submodule. -/
def invariants : Action (TopModuleCat R) G ⥤ TopModuleCat R where
  obj M := .of R
    { carrier := { x | ∀ g : G, (M.ρ g).hom x = x }
      add_mem' hx hy g := by simp [hx g, hy g]
      zero_mem' := by simp
      smul_mem' r x hx g := by simp [hx g] : Submodule R M.V }
  map f := TopModuleCat.ofHom
    { toLinearMap := f.hom.hom.restrict fun x hx g ↦
        congr($(f.comm g) x).symm.trans congr(f.hom.hom $(hx g))
      cont := continuous_induced_rng.mpr (f.hom.hom.2.comp continuous_subtype_val) }

instance : (invariants R G).Linear R where
instance : (invariants R G).Additive where

/-- `homogeneousCochains R G` is the functor taking
an `R`-linear `G`-representation to the complex of homogeneous cochains. -/
def homogeneousCochains : Action (TopModuleCat R) G ⥤ CochainComplex (TopModuleCat R) ℕ :=
  (MultiInd.complex R G).asFunctor ⋙ (invariants R G).mapHomologicalComplex _ ⋙
    (ComplexShape.embeddingUp'Add 1 1).restrictionFunctor _

/-- `continuousCohomology R G n` is the functor taking
an `R`-linear `G`-representation to its `n`-th continuous cohomology. -/
noncomputable
def _root_.continuousCohomology (n : ℕ) : Action (TopModuleCat R) G ⥤ TopModuleCat R :=
  homogeneousCochains R G ⋙ HomologicalComplex.homologyFunctor _ _ n

set_option backward.isDefEq.respectTransparency false in
/-- The `0`-homogeneous cochains are isomorphic to `Xᴳ`. -/
def kerHomogeneousCochainsZeroEquiv
    (X : Action (TopModuleCat R) G) (n : ℕ) (hn : n = 1) :
    (((homogeneousCochains R G).obj X).d 0 n).hom.ker ≃L[R] (invariants R G).obj X where
  toFun x :=
  { val := DFunLike.coe (F := C(G, _)) x.1.1 1
    property g := by
      subst hn
      obtain ⟨⟨x : C(G, _), hx⟩, hx'⟩ := x
      have : (X.ρ g).hom (x (g⁻¹ * 1)) = x 1 := congr(DFunLike.coe (F := C(G, _)) $(hx g) 1)
      have hx' : x (g⁻¹ * 1) - x 1 = 0 :=
        congr(DFunLike.coe (F := C(G, _)) (DFunLike.coe (F := C(G, _)) ($hx').1 1) (g⁻¹ * 1))
      rw [sub_eq_zero] at hx'
      exact congr((X.ρ g).hom $hx').symm.trans this }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := by
    refine ⟨⟨ContinuousLinearMap.const R _ x.1, fun g ↦ ContinuousMap.ext fun a ↦
      by subst hn; exact x.2 g⟩, ?_⟩
    subst hn
    exact Subtype.ext (ContinuousMap.ext fun a ↦
      ContinuousMap.ext fun b ↦ show x.1 - x.1 = (0 : X.V) by simp)
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

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/
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
