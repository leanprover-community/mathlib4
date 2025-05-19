/-
Copyright (c) 2025 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Topology.ContinuousMap.Algebra

/-!

# Continuous cohomology

We define continuous cohomology as the homology of homogeneous cochains.
We define homogenous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `Action (TopModuleCat R) G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

## Main definition
- `ContinuousCohomology.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous homology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induces long exact sequences in certain scenarios.
-/

open CategoryTheory ContinuousMap

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

namespace ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable {R G} in
/-- The `G` representation `C(G, rep)` given a representation `rep`.
The `G` action is defined by `g • f := x ↦ f (g⁻¹ * x)`. -/
abbrev Iobj (rep : Action (TopModuleCat R) G) : Action (TopModuleCat R) G where
  V := .of R C(G, rep.V)
  ρ :=
  { toFun g := TopModuleCat.ofHom
      { toFun f := .comp (rep.ρ g).hom (f.comp (Homeomorph.mulLeft g⁻¹))
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp
        cont := ((continuous_postcomp _).comp (continuous_precomp _)) }
    map_one' := ConcreteCategory.ext (by ext; simp)
    map_mul' _ _ := ConcreteCategory.ext (by ext; simp [mul_assoc]) }

/-- The functor taking a representation `rep` to the representation `C(G, rep)`. -/
@[simps]
def I : Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G where
  obj := Iobj
  map {M N} φ :=
  { hom := TopModuleCat.ofHom (ContinuousLinearMap.compLeftContinuous _ _ φ.hom.hom)
    comm g := by
      ext f g'
      show (M.ρ g ≫ φ.hom).hom (f (g⁻¹ * g')) = (φ.hom ≫ N.ρ g).hom (f (g⁻¹ * g'))
      rw [φ.comm] }
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (I R G).Additive := ⟨by tauto⟩
instance : (I R G).Linear R := ⟨by tauto⟩

/-- The constant function `rep ⟶ C(G, rep)` as a natural transformation. -/
@[simps]
def const : 𝟭 _ ⟶ I R G where
  app _ := { hom := TopModuleCat.ofHom (.const _ _), comm _ := rfl }
  naturality _ _ _ := rfl

namespace MultiInd

/-- The n-th functor taking `M` to `C(G, C(G,...,C(G, M)))` (with n `G`s).
These functors form a complex, see `MultiInd.complex`. -/
def functor : ℕ → Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G
  | 0     => 𝟭 _
  | n + 1 => functor n ⋙ I R G

/-- The differential map in `MultiInd.complex`. -/
def d : ∀ n : ℕ, functor R G n ⟶ functor R G (n + 1)
  | 0     => const R G
  | n + 1 => whiskerLeft (functor R G (n + 1)) (const R G) - (by exact whiskerRight (d n) (I R G))

lemma d_zero : d R G 0 = const R G := rfl

lemma d_succ (n : ℕ) :
    d R G (n + 1) = whiskerLeft (functor R G (n + 1)) (const R G) -
      (by exact whiskerRight (d R G n) (I R G)) := rfl

@[simp]
lemma whiskerRight_zero {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (H : D ⥤ E) [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    [H.PreservesZeroMorphisms] :
    whiskerRight (0 : F ⟶ G) H = 0 := by aesop_cat

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
    rw [Preadditive.sub_comp, ← whiskerRight_comp, ih, whiskerRight_zero, sub_zero, sub_eq_zero]
    rfl

/-- The complex of functors taking `M` to `C(G, C(G,...,C(G, M)))`. -/
def complex : CochainComplex (Action (TopModuleCat R) G ⥤ Action (TopModuleCat R) G) ℕ where
  X := functor R G
  d i j := if h : j = i + 1 then d R G i ≫ eqToHom (by subst h; rfl) else 0
  d_comp_d' _ _ _ h₁ h₂ := by subst h₁ h₂; simp

end MultiInd

/-- The functor taking an `R`-linear `G`-representation `M` to complex of representations
whose n-th component is `C(G, C(G,...,C(G, M)))` (with n `G`s).
The `G`-invariant submodule of it is the homogeneous cochains. -/
def multiInd : Action (TopModuleCat R) G ⥤ CochainComplex (Action (TopModuleCat R) G) ℕ where
  obj M := (((evaluation _ _).obj M).mapHomologicalComplex _).obj (MultiInd.complex R G)
  map {M N} f := (NatTrans.mapHomologicalComplex ((evaluation _ _).map f) _).app _

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
  multiInd R G ⋙ (invariants R G).mapHomologicalComplex _

/-- `continuousCohomology R G n` is the functor taking
an `R`-linear `G`-representation to its `n`-th continuous homology. -/
noncomputable
def _root_.continuousCohomology (n : ℕ) : Action (TopModuleCat R) G ⥤ TopModuleCat R :=
  homogeneousCochains R G ⋙ HomologicalComplex.homologyFunctor _ _ n

end ContinuousCohomology
