/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # The sheaf of smooth functions on a manifold

The sheaf of `𝕜`-smooth functions from a manifold `M` to a manifold `N` can be defined as a sheaf of
types using the construction `StructureGroupoid.LocalInvariantProp.sheaf` from the file
`Mathlib.Geometry.Manifold.Sheaf.Basic`.  In this file we write that down (a one-liner), then do the
work of upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings] when `N`
carries more algebraic structure.  For example, if `N` is `𝕜` then the sheaf of smooth functions
from `M` to `𝕜` is a sheaf of commutative rings, the *structure sheaf* of `M`.

## Main definitions

* `smooth_sheaf`: The sheaf of smooth functions from `M` to `N`, as a sheaf of types
* `smooth_sheaf.eval`: Canonical map onto `N` from the stalk of `smooth_sheaf IM I M N` at `x`,
  given by evaluating sections at `x`
* `smooth_sheaf_Group`, `smooth_sheaf_CommGroup`, `smooth_sheaf_Ring`, `smooth_sheaf_CommRing`: The
  sheaf of smooth functions into a [Lie group]/[abelian Lie group]/[smooth ring]/[smooth commutative
  ring], as a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
* `smooth_sheaf_CommGroup.comp_left`: For a manifold `M` and a smooth homomorphism `φ` between
  abelian Lie groups `A`, `A'`, the 'postcomposition-by-`φ`' morphism of sheaves from
  `smooth_sheaf_CommGroup IM I M A` to `smooth_sheaf_CommGroup IM I' M A'`

## TODO

There are variants of `smooth_sheaf_CommGroup.comp_left` for `GroupCat`, `RingCat`, `CommRingCat`;
this is just boilerplate and can be added as needed.

The canonical "evaluation" map `smooth_sheaf.eval` from the stalk at `x:M` of the sheaf of smooth
functions `M → N` should be upgraded in the presence of algebraic structure on `N`: a group
homomorphism for `smooth_sheaf_Group` and `smooth_sheaf_CommGroup`, a ring homomorphism for
`smooth_sheaf_Ring` and `smooth_sheaf_CommRing`. Also, one wants to identify as types the stalk at
`x` of `smooth_sheaf_Group` (and similarly for the other algebraic categories) with the stalk at
`x` of `smooth_sheaf`.  These tasks require engaging with the colimits API in the category theory
library, but should not be particularly hard.

Currently there is a universe restriction: one can consider the sheaf of smooth functions from `M`
to `N` only if `M` and `N` are in the same universe.  For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, and there is WIP (as of June 2023)
to fix this.  See
https://github.com/leanprover-community/mathlib/pull/19153
and cross-references there.
-/


noncomputable section
open scoped Manifold
open TopologicalSpace Opposite

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E H')
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N G A A' R : Type u) [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace G] [ChartedSpace H G] [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace A'] [ChartedSpace H' A'] [TopologicalSpace R] [ChartedSpace H R]

section TypeCat

/-- The sheaf of smooth functions from `M` to `N`, as a sheaf of types. -/
def smooth_sheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp IM I ⊤).sheaf M N

variable {M}

instance smooth_sheaf.has_coe_to_fun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smooth_sheaf IM I M N).val.obj U) (fun _ ↦ ↑(unop U) → N) :=
  (contDiffWithinAt_localInvariantProp IM I ⊤).sheafHasCoeToFun _ _ _

/-- The object of `smooth_sheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : Opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to `N`.  This is not
just a "moral" equality but a literal and definitional equality! -/
lemma smooth_sheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (smooth_sheaf IM I M N).val.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯ := rfl

/-- Canonical map from the stalk of `smooth_sheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`. -/
def smooth_sheaf.eval (x : M) : (smooth_sheaf IM I M N).presheaf.stalk x → N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

/-- The `eval` map is surjective at `x`. -/
lemma smooth_sheaf.eval_surjective (x : M) : Function.Surjective (smooth_sheaf.eval IM I N x) := by
  apply TopCat.stalkToFiber_surjective
  intros n
  exact ⟨⊤, fun _ ↦ n, smooth_const, rfl⟩

variable {IM I N}

@[simp] lemma smooth_sheaf.eval_germ (U : Opens (TopCat.of M)) (x : U)
    (f : (smooth_sheaf IM I M N).val.obj (op U)) :
    smooth_sheaf.eval IM I N (x : TopCat.of M) ((smooth_sheaf IM I M N).presheaf.germ x f)
    = f x :=
  TopCat.stalkToFiber_germ _ U x f

lemma smooth_sheaf.smooth_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (smooth_sheaf IM I M N).val.obj U) :
    Smooth IM I f :=
(contDiffWithinAt_localInvariantProp IM I ⊤).section_spec _ _ _ _

end TypeCat

section LieAddGroup
variable [AddGroup G] [LieAddGroup I G]

instance (U : (Opens (TopCat.of M))ᵒᵖ) : AddGroup ((smooth_sheaf IM I M G).val.obj U) :=
  (SmoothMap.addGroup : AddGroup C^∞⟮IM, (unop U : Opens M); I, G⟯)

/-- The presheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a presheaf
of additive groups. -/
def smooth_presheaf_AddGroup : TopCat.Presheaf AddGroupCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ AddGroupCat.of ((smooth_sheaf IM I M G).val.obj U)
    map := fun h ↦ AddGroupCat.ofHom <|
      SmoothMap.restrictAddMonoidHom IM I G <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

end LieAddGroup

section LieGroup
variable [Group G] [LieGroup I G]

@[to_additive existing]
instance (U : (Opens (TopCat.of M))ᵒᵖ) : Group ((smooth_sheaf IM I M G).val.obj U) :=
  (SmoothMap.group : Group C^∞⟮IM, (unop U : Opens M); I, G⟯)

/-- The presheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a presheaf of groups.
-/
@[to_additive existing]
def smooth_presheaf_Group : TopCat.Presheaf GroupCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ GroupCat.of ((smooth_sheaf IM I M G).val.obj U)
    map := fun h ↦ GroupCat.ofHom <|
      SmoothMap.restrictMonoidHom IM I G <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive "The sheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
sheaf of additive groups."]
noncomputable def smooth_sheaf_Group : TopCat.Sheaf GroupCat.{u} (TopCat.of M) :=
  { val := smooth_presheaf_Group IM I M G
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget GroupCat)]
      exact CategoryTheory.Sheaf.cond (smooth_sheaf IM I M G) }

end LieGroup

section AddCommLieGroup
variable [AddCommGroup A] [AddCommGroup A'] [LieAddGroup I A] [LieAddGroup I' A']

instance (U : (Opens (TopCat.of M))ᵒᵖ) : AddCommGroup ((smooth_sheaf IM I M A).val.obj U) :=
  (SmoothMap.addCommGroup : AddCommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯)

/-- The presheaf of smooth functions from `M` to `A`, for `A` an additive abelian Lie group, as a
presheaf of additive abelian groups. -/
def smooth_presheaf_AddCommGroup : TopCat.Presheaf AddCommGroupCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ AddCommGroupCat.of ((smooth_sheaf IM I M A).val.obj U)
    map := fun h ↦ AddCommGroupCat.ofHom <|
      SmoothMap.restrictAddMonoidHom IM I A <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

end AddCommLieGroup

section CommLieGroup
variable [CommGroup A] [CommGroup A'] [LieGroup I A] [LieGroup I' A']

@[to_additive existing]
instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommGroup ((smooth_sheaf IM I M A).val.obj U) :=
  (SmoothMap.commGroup : CommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯)

/-- The presheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive existing]
def smooth_presheaf_CommGroup : TopCat.Presheaf CommGroupCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommGroupCat.of ((smooth_sheaf IM I M A).val.obj U)
    map := fun h ↦ CommGroupCat.ofHom <|
      SmoothMap.restrictMonoidHom IM I A <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive "The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups."]
noncomputable def smooth_sheaf_CommGroup : TopCat.Sheaf CommGroupCat.{u} (TopCat.of M) :=
  { val := smooth_presheaf_CommGroup IM I M A
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommGroupCat)]
      exact CategoryTheory.Sheaf.cond (smooth_sheaf IM I M A) }

/-- For a manifold `M` and a smooth homomorphism `φ` between abelian Lie groups `A`, `A'`, the
'left-composition-by-`φ`' morphism of sheaves from `smooth_sheaf_CommGroup IM I M A` to
`smooth_sheaf_CommGroup IM I' M A'`. -/
def smooth_sheaf_CommGroup.comp_left (φ : A →* A') (hφ : Smooth I I' φ) :
    smooth_sheaf_CommGroup IM I M A ⟶ smooth_sheaf_CommGroup IM I' M A' :=
  CategoryTheory.Sheaf.Hom.mk <|
  { app := fun _ ↦ CommGroupCat.ofHom <| SmoothMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ ↦ rfl }

end CommLieGroup

section AddCommLieGroup
variable [AddCommGroup A] [AddCommGroup A'] [LieAddGroup I A] [LieAddGroup I' A']

/-- For a manifold `M` and a smooth homomorphism `φ` between abelian additive Lie groups
`A`, `A'`, the 'left-composition-by-`φ`' morphism of sheaves from
`smooth_sheaf_AddCommGroup IM I M A` to `smooth_sheaf_AddCommGroup IM I' M A'`. -/
def smooth_sheaf_AddCommGroup.comp_left (φ : A →+ A') (hφ : Smooth I I' φ) :
    smooth_sheaf_AddCommGroup IM I M A ⟶ smooth_sheaf_AddCommGroup IM I' M A' :=
  CategoryTheory.Sheaf.Hom.mk <|
  { app := fun _ ↦ AddCommGroupCat.ofHom <| SmoothMap.compLeftAddMonoidHom _ _ φ hφ
    naturality := fun _ _ _ ↦ rfl }

attribute [to_additive existing] smooth_sheaf_CommGroup.comp_left

end AddCommLieGroup

section SmoothRing
variable [Ring R] [SmoothRing I R]

instance (U : (Opens (TopCat.of M))ᵒᵖ) : Ring ((smooth_sheaf IM I M R).val.obj U) :=
  (SmoothMap.ring : Ring C^∞⟮IM, (unop U : Opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
def smooth_presheaf_Ring : TopCat.Presheaf RingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ RingCat.of ((smooth_sheaf IM I M R).val.obj U)
    map := fun h ↦ RingCat.ofHom <|
      SmoothMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a sheaf of
rings. -/
def smooth_sheaf_Ring : TopCat.Sheaf RingCat.{u} (TopCat.of M) :=
  { val := smooth_presheaf_Ring IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
      exact CategoryTheory.Sheaf.cond (smooth_sheaf IM I M R) }

end SmoothRing

section SmoothCommRing
variable [CommRing R] [SmoothRing I R]

instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((smooth_sheaf IM I M R).val.obj U) :=
  (SmoothMap.commRing : CommRing C^∞⟮IM, (unop U : Opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a
presheaf of commutative rings. -/
def smooth_presheaf_CommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommRingCat.of ((smooth_sheaf IM I M R).val.obj U)
    map := fun h ↦ CommRingCat.ofHom <|
      SmoothMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a sheaf of
commutative rings. -/
def smooth_sheaf_CommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) :=
  { val := smooth_presheaf_CommRing IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommRingCat)]
      exact CategoryTheory.Sheaf.cond (smooth_sheaf IM I M R) }

-- sanity check: applying the `CommRingCat`-to-`TypeCat` forgetful functor to the sheaf-of-rings of
-- smooth functions gives the sheaf-of-types of smooth functions.
example : (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)).obj
    (smooth_sheaf_CommRing IM I M R) = (smooth_sheaf IM I M R) := rfl

end SmoothCommRing
