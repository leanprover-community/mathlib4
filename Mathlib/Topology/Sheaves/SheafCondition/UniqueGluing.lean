/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.CategoryTheory.Limits.Shapes.Types

#align_import topology.sheaves.sheaf_condition.unique_gluing from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `MonCat`, `AddCommGroupCat`, `RingCat`, `CommRingCat` etc. are all examples of
this kind of category.

A presheaf `F : presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (supr U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (supr U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of pairwise intersections. Our approach is as follows: First, we show them to be equivalent
for `Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`Mathlib/Topology/Sheaves/Forget.lean`.

-/

noncomputable section

open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
  TopologicalSpace TopologicalSpace.Opens Opposite

universe v u x

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

namespace TopCat

namespace Presheaf

section

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable {X : TopCat.{x}} (F : Presheaf C X) {ι : Type x} (U : ι → Opens X)

/-- A family of sections `sf` is compatible, if the restrictions of `sf i` and `sf j` to `U i ⊓ U j`
agree, for all `i` and `j`
-/
def IsCompatible (sf : ∀ i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_compatible TopCat.Presheaf.IsCompatible

/-- A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
for all `i`
-/
def IsGluing (sf : ∀ i : ι, F.obj (op (U i))) (s : F.obj (op (iSup U))) : Prop :=
  ∀ i : ι, F.map (Opens.leSupr U i).op s = sf i
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_gluing TopCat.Presheaf.IsGluing

/--
The sheaf condition in terms of unique gluings. A presheaf `F : presheaf C X` satisfies this sheaf
condition if and only if, for every compatible family of sections `sf : Π i : ι, F.obj (op (U i))`,
there exists a unique gluing `s : F.obj (op (supr U))`.

We prove this to be equivalent to the usual one below in
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`
-/
def IsSheafUniqueGluing : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X) (sf : ∀ i : ι, F.obj (op (U i))),
    IsCompatible F U sf → ∃! s : F.obj (op (iSup U)), IsGluing F U sf s
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_unique_gluing TopCat.Presheaf.IsSheafUniqueGluing

end

section TypeValued

variable {X : TopCat.{x}} {F : Presheaf (Type u) X} {ι : Type x} {U : ι → Opens X}

/-- Given sections over a family of open sets, extend it to include
  sections over pairwise intersections of the open sets. -/
def objPairwiseOfFamily (sf : ∀ i, F.obj (op (U i))) :
    ∀ i, ((Pairwise.diagram U).op ⋙ F).obj i
  | ⟨Pairwise.single i⟩ => sf i
  | ⟨Pairwise.pair i j⟩ => F.map (infLELeft (U i) (U j)).op (sf i)

/-- Given a compatible family of sections over open sets, extend it to a
  section of the functor `(Pairwise.diagram U).op ⋙ F`. -/
def IsCompatible.sectionPairwise {sf} (h : IsCompatible F U sf) :
    ((Pairwise.diagram U).op ⋙ F).sections := by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i|⟨i,j⟩) (i'|⟨i',j'⟩) (_|_|_|_)
  · exact congr_fun (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact congr_fun (G.map_id <| op <| Pairwise.pair i j) _

theorem isGluing_iff_pairwise {sf s} : IsGluing F U sf s ↔
    ∀ i, (F.mapCone (Pairwise.cocone U).op).π.app i s = objPairwiseOfFamily sf i := by
  refine ⟨fun h ↦ ?_, fun h i ↦ h (op <| Pairwise.single i)⟩
  rintro (i|⟨i,j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)

variable (F)

/-- For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
usual sheaf condition.
-/
theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing := by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U ↦ ⟨fun h sf cpt ↦ ?_, fun h s hs ↦ ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i ↦ s <| op <| Pairwise.single i) fun i j ↦
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert h; ext (i|⟨i,j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing_types TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types

#noalign Top.presheaf.pi_opens_iso_sections_family
#noalign Top.presheaf.compatible_iff_left_res_eq_right_res
#noalign Top.presheaf.is_gluing_iff_eq_res
#noalign Top.presheaf.is_sheaf_unique_gluing_of_is_sheaf_types

/-- The usual sheaf condition can be obtained from the sheaf condition
in terms of unique gluings.
-/
theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf :=
  (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_of_is_sheaf_unique_gluing_types TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types

end TypeValued

section

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable [HasLimits C] [(forget C).ReflectsIsomorphisms] [PreservesLimits (forget C)]
variable {X : TopCat.{v}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

/-- For presheaves valued in a concrete category, whose forgetful functor reflects isomorphisms and
preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one.
-/
theorem isSheaf_iff_isSheafUniqueGluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.trans (isSheaf_iff_isSheaf_comp (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing

end

end Presheaf

namespace Sheaf

open Presheaf

open CategoryTheory

section

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable [HasLimits C] [(ConcreteCategory.forget (C := C)).ReflectsIsomorphisms]
variable [PreservesLimits (ConcreteCategory.forget (C := C))]
variable {X : TopCat.{v}} (F : Sheaf C X) {ι : Type v} (U : ι → Opens X)

/-- A more convenient way of obtaining a unique gluing of sections for a sheaf.
-/
theorem existsUnique_gluing (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op (iSup U)), IsGluing F.1 U sf s :=
  (isSheaf_iff_isSheafUniqueGluing F.1).mp F.cond U sf h
set_option linter.uppercaseLean3 false in
#align Top.sheaf.exists_unique_gluing TopCat.Sheaf.existsUnique_gluing

/-- In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem existsUnique_gluing' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (sf : ∀ i : ι, F.1.obj (op (U i))) (h : IsCompatible F.1 U sf) :
    ∃! s : F.1.obj (op V), ∀ i : ι, F.1.map (iUV i).op s = sf i := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← comp_apply, ← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← comp_apply, ← F.1.map_comp]
    · rw [eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl, F.1.map_id, id_apply]
    · convert gl'_spec i
set_option linter.uppercaseLean3 false in
#align Top.sheaf.exists_unique_gluing' TopCat.Sheaf.existsUnique_gluing'

@[ext]
theorem eq_of_locally_eq (s t : F.1.obj (op (iSup U)))
    (h : ∀ i, F.1.map (Opens.leSupr U i).op s = F.1.map (Opens.leSupr U i).op t) : s = t := by
  let sf : ∀ i : ι, F.1.obj (op (U i)) := fun i => F.1.map (Opens.leSupr U i).op s
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [sf, ← comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  trans gl
  · apply gl_uniq
    intro i
    rfl
  · symm
    apply gl_uniq
    intro i
    rw [← h]
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq TopCat.Sheaf.eq_of_locally_eq

/-- In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem eq_of_locally_eq' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (s t : F.1.obj (op V)) (h : ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) : s = t := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← comp_apply, ← F.1.map_comp, eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl,
      F.1.map_id, id_apply]
  apply eq_of_locally_eq
  intro i
  rw [← comp_apply, ← comp_apply, ← F.1.map_comp]
  convert h i
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq' TopCat.Sheaf.eq_of_locally_eq'

theorem eq_of_locally_eq₂ {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V ≤ U₁ ⊔ U₂)
    (s t : F.1.obj (op V)) (h₁ : F.1.map i₁.op s = F.1.map i₁.op t)
    (h₂ : F.1.map i₂.op s = F.1.map i₂.op t) : s = t := by
  classical
    fapply F.eq_of_locally_eq' fun t : ULift Bool => if t.1 then U₁ else U₂
    · exact fun i => if h : i.1 then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
    · refine le_trans hcover ?_
      rw [sup_le_iff]
      constructor
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up true)
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up false)
    · rintro ⟨_ | _⟩
      any_goals exact h₁
      any_goals exact h₂
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq₂ TopCat.Sheaf.eq_of_locally_eq₂

end

theorem objSupIsoProdEqLocus_inv_eq_iff {X : TopCat.{u}} (F : X.Sheaf CommRingCat.{u})
    {U V W UW VW : Opens X} (e : W ≤ U ⊔ V) (x) (y : F.1.obj (op W))
    (h₁ : UW = U ⊓ W) (h₂ : VW = V ⊓ W) :
    F.1.map (homOfLE e).op ((F.objSupIsoProdEqLocus U V).inv x) = y ↔
    F.1.map (homOfLE (h₁ ▸ inf_le_left : UW ≤ U)).op x.1.1 =
      F.1.map (homOfLE <| h₁ ▸ inf_le_right).op y ∧
    F.1.map (homOfLE (h₂ ▸ inf_le_left : VW ≤ V)).op x.1.2 =
      F.1.map (homOfLE <| h₂ ▸ inf_le_right).op y := by
  subst h₁ h₂
  constructor
  · rintro rfl
    rw [← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
    -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
    repeat rw [← comp_apply]
    simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp, and_self]
  · rintro ⟨e₁, e₂⟩
    refine F.eq_of_locally_eq₂
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) (homOfLE (inf_le_right : V ⊓ W ≤ W)) ?_ _ _ ?_ ?_
    · rw [← inf_sup_right]
      exact le_inf e le_rfl
    · rw [← e₁, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
      -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]
    · rw [← e₂, ← TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]
      -- `simp` doesn't see through the type equality of objects in `CommRingCat`, so use `rw` #8386
      repeat rw [← comp_apply]
      simp only [← Functor.map_comp, ← op_comp, Category.assoc, homOfLE_comp]

end Sheaf

end TopCat
