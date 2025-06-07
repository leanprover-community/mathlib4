/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Adam Topaz
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Sheaf.Basic

/-! # The sheaf of smooth functions on a manifold

The sheaf of `𝕜`-smooth functions from a manifold `M` to a manifold `N` can be defined as a sheaf of
types using the construction `StructureGroupoid.LocalInvariantProp.sheaf` from the file
`Mathlib/Geometry/Manifold/Sheaf/Basic.lean`.  In this file we write that down (a one-liner), then
do the work of upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
when `N` carries more algebraic structure.  For example, if `N` is `𝕜` then the sheaf of smooth
functions from `M` to `𝕜` is a sheaf of commutative rings, the *structure sheaf* of `M`.

## Main definitions

* `smoothSheaf`: The sheaf of smooth functions from `M` to `N`, as a sheaf of types
* `smoothSheaf.eval`: Canonical map onto `N` from the stalk of `smoothSheaf IM I M N` at `x`,
  given by evaluating sections at `x`
* `smoothSheafGroup`, `smoothSheafCommGroup`, `smoothSheafRing`, `smoothSheafCommRing`: The
  sheaf of smooth functions into a [Lie group]/[abelian Lie group]/[smooth ring]/[smooth commutative
  ring], as a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
* `smoothSheafCommRing.forgetStalk`: Identify the stalk at a point of the sheaf-of-commutative-rings
  of functions from `M` to `R` (for `R` a smooth ring) with the stalk at that point of the
  corresponding sheaf of types.
* `smoothSheafCommRing.eval`: upgrade `smoothSheaf.eval` to a ring homomorphism when considering the
  sheaf of smooth functions into a smooth commutative ring
* `smoothSheafCommGroup.compLeft`: For a manifold `M` and a smooth homomorphism `φ` between
  abelian Lie groups `A`, `A'`, the 'postcomposition-by-`φ`' morphism of sheaves from
  `smoothSheafCommGroup IM I M A` to `smoothSheafCommGroup IM I' M A'`

# Main results

* `smoothSheaf.eval_surjective`: `smoothSheaf.eval` is surjective.
* `smoothSheafCommRing.eval_surjective`: `smoothSheafCommRing.eval` is surjective.

## TODO

There are variants of `smoothSheafCommGroup.compLeft` for `Grp`, `RingCat`, `CommRingCat`;
this is just boilerplate and can be added as needed.

Similarly, there are variants of `smoothSheafCommRing.forgetStalk` and `smoothSheafCommRing.eval`
for `Grp`, `CommGrp` and `RingCat` which can be added as needed.

Currently there is a universe restriction: one can consider the sheaf of smooth functions from `M`
to `N` only if `M` and `N` are in the same universe.  For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, which are not sufficiently
universe polymorphic.  A direct attempt to generalize the universes worked in Lean 3 but was
reverted because it was hard to port to Lean 4, see
https://github.com/leanprover-community/mathlib/pull/19230
The current (Oct 2023) proposal to permit these generalizations is to use the new `UnivLE`
typeclass, and some (but not all) of the underlying category theory constructions have now been
generalized by this method: see https://github.com/leanprover-community/mathlib4/pull/5724,
https://github.com/leanprover-community/mathlib4/pull/5726.
-/


noncomputable section
open TopologicalSpace Opposite
open scoped ContDiff

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
def smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

variable {M}

instance smoothSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheaf IM I M N).presheaf.obj U) (fun _ ↦ ↑(unop U) → N) :=
  (contDiffWithinAt_localInvariantProp ∞).sheafHasCoeToFun _ _ _

open Manifold in
/-- The object of `smoothSheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : Opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to `N`.  This is not
just a "moral" equality but a literal and definitional equality! -/
lemma smoothSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (smoothSheaf IM I M N).presheaf.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯ := rfl

/-- Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`. -/
def smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x → N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

/-- Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`, considered as a morphism in the category of types. -/
def smoothSheaf.evalHom (x : TopCat.of M) : (smoothSheaf IM I M N).presheaf.stalk x ⟶ N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

open CategoryTheory Limits

/-- Given manifolds `M`, `N` and an open neighbourhood `U` of a point `x : M`, the evaluation-at-`x`
map to `N` from smooth functions from  `U` to `N`. -/
def smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x)
    (i : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U.obj)) : N :=
  i.1 ⟨x, U.2⟩

@[simp, reassoc, elementwise] lemma smoothSheaf.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M N).val) U ≫
    smoothSheaf.evalHom IM I N x =
    smoothSheaf.evalAt _ _ _ _ _ :=
  colimit.ι_desc _ _

/-- The `eval` map is surjective at `x`. -/
lemma smoothSheaf.eval_surjective (x : M) : Function.Surjective (smoothSheaf.eval IM I N x) := by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ ↦ n, contMDiff_const, rfl⟩

instance [Nontrivial N] (x : M) : Nontrivial ((smoothSheaf IM I M N).presheaf.stalk x) :=
  (smoothSheaf.eval_surjective IM I N x).nontrivial

variable {IM I N}

@[simp] lemma smoothSheaf.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheaf IM I M N).presheaf.obj (op U)) :
    smoothSheaf.eval IM I N (x : M) ((smoothSheaf IM I M N).presheaf.germ U x hx f) = f ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ∞).localPredicate M N) _ _ _ _

lemma smoothSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (smoothSheaf IM I M N).presheaf.obj U) :
    ContMDiff IM I ∞ f :=
  (contDiffWithinAt_localInvariantProp ∞).section_spec _ _ _ _

@[deprecated (since := "2024-11-21")]
alias smoothSheaf.smooth_section := smoothSheaf.contMDiff_section

end TypeCat

section LieGroup
variable [Group G] [LieGroup I ∞ G]

open Manifold in
@[to_additive]
noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Group ((smoothSheaf IM I M G).presheaf.obj U) :=
  (ContMDiffMap.group : Group C^∞⟮IM, (unop U : Opens M); I, G⟯)

/-- The presheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a presheaf of groups.
-/
@[to_additive "The presheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
presheaf of additive groups."]
noncomputable def smoothPresheafGroup : TopCat.Presheaf Grp.{u} (TopCat.of M) :=
  { obj := fun U ↦ Grp.of ((smoothSheaf IM I M G).presheaf.obj U)
    map := fun h ↦ Grp.ofHom <|
      ContMDiffMap.restrictMonoidHom IM I G <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive "The sheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
sheaf of additive groups."]
noncomputable def smoothSheafGroup : TopCat.Sheaf Grp.{u} (TopCat.of M) :=
  { val := smoothPresheafGroup IM I M G
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Grp)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M G) }

end LieGroup

section CommLieGroup
variable [CommGroup A] [CommGroup A'] [LieGroup I ∞ A] [LieGroup I' ∞ A']

open Manifold in
@[to_additive] noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommGroup ((smoothSheaf IM I M A).presheaf.obj U) :=
  (ContMDiffMap.commGroup : CommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯)

/-- The presheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive "The presheaf of smooth functions from `M` to `A`, for `A` an additive abelian Lie
group, as a presheaf of additive abelian groups."]
noncomputable def smoothPresheafCommGroup : TopCat.Presheaf CommGrp.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommGrp.of ((smoothSheaf IM I M A).presheaf.obj U)
    map := fun h ↦ CommGrp.ofHom <|
      ContMDiffMap.restrictMonoidHom IM I A <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive "The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups."]
noncomputable def smoothSheafCommGroup : TopCat.Sheaf CommGrp.{u} (TopCat.of M) :=
  { val := smoothPresheafCommGroup IM I M A
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommGrp)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M A) }

/-- For a manifold `M` and a smooth homomorphism `φ` between abelian Lie groups `A`, `A'`, the
'left-composition-by-`φ`' morphism of sheaves from `smoothSheafCommGroup IM I M A` to
`smoothSheafCommGroup IM I' M A'`. -/
@[to_additive "For a manifold `M` and a smooth homomorphism `φ` between abelian additive Lie groups
`A`, `A'`, the 'left-composition-by-`φ`' morphism of sheaves from `smoothSheafAddCommGroup IM I M A`
to `smoothSheafAddCommGroup IM I' M A'`."]
noncomputable def smoothSheafCommGroup.compLeft (φ : A →* A') (hφ : ContMDiff I I' ∞ φ) :
    smoothSheafCommGroup IM I M A ⟶ smoothSheafCommGroup IM I' M A' :=
  CategoryTheory.Sheaf.Hom.mk <|
  { app := fun _ ↦ CommGrp.ofHom <| ContMDiffMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ ↦ rfl }

end CommLieGroup

section ContMDiffRing
variable [Ring R] [ContMDiffRing I ∞ R]

open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : Ring ((smoothSheaf IM I M R).presheaf.obj U) :=
  (ContMDiffMap.ring : Ring C^∞⟮IM, (unop U : Opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
def smoothPresheafRing : TopCat.Presheaf RingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ RingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a sheaf of
rings. -/
def smoothSheafRing : TopCat.Sheaf RingCat.{u} (TopCat.of M) :=
  { val := smoothPresheafRing IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M R) }

end ContMDiffRing

section SmoothCommRing
variable [CommRing R] [ContMDiffRing I ∞ R]

open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((smoothSheaf IM I M R).presheaf.obj U) :=
  (ContMDiffMap.commRing : CommRing C^∞⟮IM, (unop U : Opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a
presheaf of commutative rings. -/
def smoothPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ CommRingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a sheaf of
commutative rings. -/
def smoothSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) :=
  { val := smoothPresheafCommRing IM I M R
    cond := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommRingCat)]
      exact CategoryTheory.Sheaf.cond (smoothSheaf IM I M R) }

-- sanity check: applying the `CommRingCat`-to-`TypeCat` forgetful functor to the sheaf-of-rings of
-- smooth functions gives the sheaf-of-types of smooth functions.
example : (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj
    (smoothSheafCommRing IM I M R) = (smoothSheaf IM I M R) := rfl

instance smoothSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheafCommRing IM I M R).presheaf.obj U) (fun _ ↦ ↑(unop U) → R) :=
  (contDiffWithinAt_localInvariantProp ∞).sheafHasCoeToFun _ _ _

open CategoryTheory Limits

/-- Identify the stalk at a point of the sheaf-of-commutative-rings of functions from `M` to `R`
(for `R` a smooth ring) with the stalk at that point of the corresponding sheaf of types. -/
def smoothSheafCommRing.forgetStalk (x : TopCat.of M) :
    ((smoothSheafCommRing IM I M R).presheaf.stalk x).carrier ≅
    (smoothSheaf IM I M R).presheaf.stalk x :=
  preservesColimitIso (forget _) _

@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_hom (x : TopCat.of M) (U) :
    CategoryStruct.comp
      (Z := (smoothSheaf IM I M R).presheaf.stalk x)
      (DFunLike.coe
        (α := (((smoothSheafCommRing IM I M R).presheaf.obj
          (op ((OpenNhds.inclusion x).obj U.unop)))))
        (colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheafCommRing IM I M R).presheaf) U).hom)
      (forgetStalk IM I M R x).hom =
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U :=
  ι_preservesColimitIso_hom (forget CommRingCat) _ _

@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_inv (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U ≫
    (smoothSheafCommRing.forgetStalk IM I M R x).inv =
    ⇑(colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheafCommRing IM I M R).presheaf) U) := by
  rw [Iso.comp_inv_eq, ← smoothSheafCommRing.ι_forgetStalk_hom]
  simp_rw [Functor.comp_obj, Functor.op_obj]

/-- Given a smooth commutative ring `R` and a manifold `M`, and an open neighbourhood `U` of a point
`x : M`, the evaluation-at-`x` map to `R` from smooth functions from  `U` to `R`. -/
def smoothSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (smoothSheafCommRing IM I M R).presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

/-- Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at `x` to `R`,
given by evaluating sections at `x`, considered as a morphism in the category of commutative rings.
-/
def smoothSheafCommRing.evalHom (x : TopCat.of M) :
    (smoothSheafCommRing IM I M R).presheaf.stalk x ⟶ CommRingCat.of R := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U ↦ ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · aesop_cat

/-- Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at `x` to `R`,
given by evaluating sections at `x`. -/
def smoothSheafCommRing.eval (x : M) : (smoothSheafCommRing IM I M R).presheaf.stalk x →+* R :=
  (smoothSheafCommRing.evalHom IM I M R x).hom

@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ smoothSheafCommRing.evalHom IM I M R x =
    smoothSheafCommRing.evalAt _ _ _ _ _ _ :=
  colimit.ι_desc _ _

@[simp] lemma smoothSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.evalHom IM I M R (x : TopCat.of M)
      ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  congr_arg (fun a ↦ a f) <| smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩

@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_inv_comp_eval
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).inv ≫
     (DFunLike.coe (smoothSheafCommRing.evalHom IM I M R x).hom) =
    smoothSheaf.evalHom _ _ _ _ := by
  apply Limits.colimit.hom_ext
  intro U
  show (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc, smoothSheaf.ι_evalHom]
  ext x
  exact CategoryTheory.congr_fun (smoothSheafCommRing.ι_evalHom ..) x

@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_hom_comp_evalHom
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).hom ≫ (smoothSheaf.evalHom IM I R x) =
      ⇑(smoothSheafCommRing.evalHom _ _ _ _ _) := by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]

lemma smoothSheafCommRing.eval_surjective (x) :
    Function.Surjective (smoothSheafCommRing.eval IM I M R x) := by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply

instance [Nontrivial R] (x : M) : Nontrivial ((smoothSheafCommRing IM I M R).presheaf.stalk x) :=
  (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial

variable {IM I M R}

@[simp] lemma smoothSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.eval IM I M R x ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  smoothSheafCommRing.evalHom_germ IM I M R U x hx f

end SmoothCommRing
