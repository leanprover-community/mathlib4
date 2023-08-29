/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Topology.Sheaves.Forget
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Types

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
in terms of equalizers. Our approach is as follows: First, we show them to be equivalent for
`Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`Mathlib/Topology/Sheaves/Forget.lean`.

-/

noncomputable section

open TopCat TopCat.Presheaf TopCat.Presheaf.SheafConditionEqualizerProducts CategoryTheory
  CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

universe v u x

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

namespace TopCat

namespace Presheaf

section

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.funLike

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

variable {X : TopCat.{x}} (F : Presheaf (Type u) X) {ι : Type x} (U : ι → Opens X) [UnivLE.{x, u}]

/-- For presheaves of types, terms of `piOpens F U` are just families of sections.
-/
def piOpensIsoSectionsFamily : piOpens F U ≃ ∀ i : ι, F.obj (op (U i)) :=
  (Types.UnivLE.productIso _).toEquiv.trans (equivShrink _).symm
set_option linter.uppercaseLean3 false in
#align Top.presheaf.pi_opens_iso_sections_family TopCat.Presheaf.piOpensIsoSectionsFamily

@[simp]
theorem piOpensIsoSectionsFamily_apply (sf : piOpens F U) (i : ι) :
    piOpensIsoSectionsFamily F U sf i = Pi.π (fun i => F.obj (op (U i))) i sf := by
  simp [piOpensIsoSectionsFamily]
  -- 🎉 no goals

/-- Under the isomorphism `piOpensIsoSectionsFamily`, compatibility of sections is the same
as being equalized by the arrows `leftRes` and `rightRes` of the equalizer diagram.
-/
theorem compatible_iff_leftRes_eq_rightRes (sf : piOpens F U) :
    IsCompatible F U (piOpensIsoSectionsFamily F U sf) ↔
    leftRes F U sf = rightRes F U sf := by
  constructor <;> intro h
  -- ⊢ IsCompatible F U (↑(piOpensIsoSectionsFamily F U) sf) → leftRes F U sf = rig …
                  -- ⊢ leftRes F U sf = rightRes F U sf
                  -- ⊢ IsCompatible F U (↑(piOpensIsoSectionsFamily F U) sf)
  · -- Porting note : Lean can't use `Types.limit_ext'` as an `ext` lemma
    refine Types.limit_ext _ _ _ fun ⟨i, j⟩ => ?_
    -- ⊢ limit.π (Discrete.functor fun p => F.obj (op (U p.fst ⊓ U p.snd))) { as := ( …
    rw [leftRes, Types.Limit.lift_π_apply, Fan.mk_π_app, rightRes, Types.Limit.lift_π_apply,
      Fan.mk_π_app]
    simpa using h i j
    -- 🎉 no goals
  · intro i j
    -- ⊢ ↑(F.map (infLELeft (U i) (U j)).op) (↑(piOpensIsoSectionsFamily F U) sf i) = …
    convert congr_arg (Limits.Pi.π (fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))) (i, j)) h
    -- ⊢ ↑(F.map (infLELeft (U i) (U j)).op) (↑(piOpensIsoSectionsFamily F U) sf i) = …
    · rw [leftRes, Types.pi_lift_π_apply, piOpensIsoSectionsFamily_apply]
      -- ⊢ ↑(F.map (infLELeft (U i) (U j)).op) (Pi.π (fun i => F.obj (op (U i))) i sf)  …
      rfl
      -- 🎉 no goals
    · rw [rightRes, Types.pi_lift_π_apply]
      -- ⊢ ↑(F.map (infLERight (U i) (U j)).op) (↑(piOpensIsoSectionsFamily F U) sf j)  …
      simp only [piOpensIsoSectionsFamily_apply]
      -- ⊢ ↑(F.map (infLERight (U i) (U j)).op) (Pi.π (fun i => F.obj (op (U i))) j sf) …
      rfl
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.compatible_iff_left_res_eq_right_res TopCat.Presheaf.compatible_iff_leftRes_eq_rightRes

/-- Under the isomorphism `piOpensIsoSectionsFamily`, being a gluing of a family of
sections `sf` is the same as lying in the preimage of `res` (the leftmost arrow of the
equalizer diagram).
-/
@[simp]
theorem isGluing_iff_eq_res (sf : piOpens F U) (s : F.obj (op (iSup U))) :
    IsGluing F U (piOpensIsoSectionsFamily F U sf) s ↔ res F U s = sf := by
  constructor <;> intro h
  -- ⊢ IsGluing F U (↑(piOpensIsoSectionsFamily F U) sf) s → res F U s = sf
                  -- ⊢ res F U s = sf
                  -- ⊢ IsGluing F U (↑(piOpensIsoSectionsFamily F U) sf) s
  · -- Porting note : Lean can't use `Types.limit_ext'` as an `ext` lemma
    refine Types.limit_ext _ _ _ fun ⟨i⟩ => ?_
    -- ⊢ limit.π (Discrete.functor fun i => F.obj (op (U i))) { as := i } (res F U s) …
    rw [res, Types.Limit.lift_π_apply, Fan.mk_π_app]
    -- ⊢ F.map (leSupr U { as := i }.as).op s = limit.π (Discrete.functor fun i => F. …
    simpa using h i
    -- 🎉 no goals
  · intro i
    -- ⊢ ↑(F.map (leSupr U i).op) s = ↑(piOpensIsoSectionsFamily F U) sf i
    convert congr_arg (Limits.Pi.π (fun i : ι => F.obj (op (U i))) i) h
    -- ⊢ ↑(F.map (leSupr U i).op) s = Pi.π (fun i => F.obj (op (U i))) i (res F U s)
    rw [res, Types.pi_lift_π_apply]
    -- ⊢ ↑(F.map (leSupr U i).op) s = F.map (leSupr U i).op s
    · rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_gluing_iff_eq_res TopCat.Presheaf.isGluing_iff_eq_res

/-- The "equalizer" sheaf condition can be obtained from the sheaf condition
in terms of unique gluings.
-/
theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf := by
  rw [isSheaf_iff_isSheafEqualizerProducts]
  -- ⊢ IsSheafEqualizerProducts F
  intro ι U
  -- ⊢ Nonempty (IsLimit (fork F U))
  refine' ⟨Fork.IsLimit.mk' _ _⟩
  -- ⊢ (s : Fork (leftRes F U) (rightRes F U)) → { l // l ≫ Fork.ι (fork F U) = For …
  intro s
  -- ⊢ { l // l ≫ Fork.ι (fork F U) = Fork.ι s ∧ ∀ {m : ((Functor.const WalkingPara …
  have h_compatible :
    ∀ x : s.pt, F.IsCompatible U (piOpensIsoSectionsFamily F U (s.ι x)) := by
    intro x
    rw [compatible_iff_leftRes_eq_rightRes]
    convert congr_fun s.condition x
  choose m m_spec m_uniq using fun x : s.pt =>
    Fsh U (piOpensIsoSectionsFamily F U (s.ι x)) (h_compatible x)
  refine' ⟨m, _, _⟩
  -- ⊢ m ≫ Fork.ι (fork F U) = Fork.ι s
  · -- Porting note : `ext` can't see `limit.hom_ext` applies here:
    -- See https://github.com/leanprover-community/mathlib4/issues/5229
    refine limit.hom_ext fun ⟨i⟩ => funext fun x => ?_
    -- ⊢ ((m ≫ Fork.ι (fork F U)) ≫ limit.π (Discrete.functor fun i => F.obj (op (U i …
    simp [res]
    -- ⊢ F.map (leSupr U i).op (m x) = limit.π (Discrete.functor fun i => F.obj (op ( …
    simpa using m_spec x i
    -- 🎉 no goals
  · intro l hl
    -- ⊢ l = m
    ext x
    -- ⊢ l x = m x
    apply m_uniq
    -- ⊢ IsGluing F U (↑(piOpensIsoSectionsFamily F U) (Fork.ι s x)) (l x)
    rw [isGluing_iff_eq_res]
    -- ⊢ res F U (l x) = Fork.ι s x
    exact congr_fun hl x
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_of_is_sheaf_unique_gluing_types TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types

/-- The sheaf condition in terms of unique gluings can be obtained from the usual
"equalizer" sheaf condition.
-/
theorem isSheafUniqueGluing_of_isSheaf_types (Fsh : F.IsSheaf) : F.IsSheafUniqueGluing := by
  rw [isSheaf_iff_isSheafEqualizerProducts] at Fsh
  -- ⊢ IsSheafUniqueGluing F
  intro ι U sf hsf
  -- ⊢ ∃! s, IsGluing F U sf s
  let sf' := (piOpensIsoSectionsFamily F U).symm sf
  -- ⊢ ∃! s, IsGluing F U sf s
  have hsf' : leftRes F U sf' = rightRes F U sf' := by
    rwa [← compatible_iff_leftRes_eq_rightRes F U sf', Equiv.apply_symm_apply]
  choose s s_spec s_uniq using Types.unique_of_type_equalizer _ _ (Fsh U).some sf' hsf'
  -- ⊢ ∃! s, IsGluing F U sf s
  use s
  -- ⊢ (fun s => IsGluing F U sf s) s ∧ ∀ (y : (forget (Type u)).obj (F.obj (op (iS …
  dsimp
  -- ⊢ IsGluing F U sf s ∧ ∀ (y : (forget (Type u)).obj (F.obj (op (iSup U)))), IsG …
  constructor
  -- ⊢ IsGluing F U sf s
  · convert (isGluing_iff_eq_res F U sf' _).mpr s_spec
    -- ⊢ sf = ↑(piOpensIsoSectionsFamily F U) sf'
    simp only [Equiv.apply_symm_apply]
    -- 🎉 no goals
  · intro y hy
    -- ⊢ y = s
    apply s_uniq
    -- ⊢ res F U y = sf'
    rw [← isGluing_iff_eq_res F U]
    -- ⊢ IsGluing F U (↑(piOpensIsoSectionsFamily F U) sf') y
    convert hy
    -- ⊢ ↑(piOpensIsoSectionsFamily F U) sf' = sf
    simp only [Equiv.apply_symm_apply]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_unique_gluing_of_is_sheaf_types TopCat.Presheaf.isSheafUniqueGluing_of_isSheaf_types

/-- For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
usual sheaf condition in terms of equalizer diagrams.
-/
theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.intro (isSheafUniqueGluing_of_isSheaf_types F) (isSheaf_of_isSheafUniqueGluing_types F)
set_option linter.uppercaseLean3 false in
#align Top.presheaf.is_sheaf_iff_is_sheaf_unique_gluing_types TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types

end TypeValued

section

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.funLike

variable [HasLimits C] [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable {X : TopCat.{v}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

/-- For presheaves valued in a concrete category, whose forgetful functor reflects isomorphisms and
preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one
in terms of equalizer diagrams.
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

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.funLike

variable [HasLimits C] [ReflectsIsomorphisms (ConcreteCategory.forget (C := C))]

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
  -- ⊢ ∃! s, ∀ (i : ι), ↑(F.val.map (iUV i).op) s = sf i
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  -- ⊢ ∃! s, ∀ (i : ι), ↑(F.val.map (iUV i).op) s = sf i
  refine' ⟨F.1.map (eqToHom V_eq_supr_U).op gl, _, _⟩
  -- ⊢ (fun s => ∀ (i : ι), ↑(F.val.map (iUV i).op) s = sf i) (↑(F.val.map (eqToHom …
  · intro i
    -- ⊢ ↑(F.val.map (iUV i).op) (↑(F.val.map (eqToHom V_eq_supr_U).op) gl) = sf i
    rw [← comp_apply, ← F.1.map_comp]
    -- ⊢ ↑(F.val.map ((eqToHom V_eq_supr_U).op ≫ (iUV i).op)) gl = sf i
    exact gl_spec i
    -- 🎉 no goals
  · intro gl' gl'_spec
    -- ⊢ gl' = ↑(F.val.map (eqToHom V_eq_supr_U).op) gl
    convert congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
    -- ⊢ gl' = ↑(F.val.map (eqToHom V_eq_supr_U).op) (↑(F.val.map (eqToHom (_ : iSup  …
      rw [← comp_apply, ← F.1.map_comp]
      -- ⊢ gl' = ↑(F.val.map ((eqToHom (_ : iSup U = V)).op ≫ (eqToHom V_eq_supr_U).op) …
      -- ⊢ ↑(F.val.map ((eqToHom (_ : iSup U = V)).op ≫ (leSupr U i).op)) gl' = sf i
    · rw [eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl, F.1.map_id, id_apply]
      -- 🎉 no goals
    · convert gl'_spec i
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.sheaf.exists_unique_gluing' TopCat.Sheaf.existsUnique_gluing'

@[ext]
theorem eq_of_locally_eq (s t : F.1.obj (op (iSup U)))
    (h : ∀ i, F.1.map (Opens.leSupr U i).op s = F.1.map (Opens.leSupr U i).op t) : s = t := by
  let sf : ∀ i : ι, F.1.obj (op (U i)) := fun i => F.1.map (Opens.leSupr U i).op s
  -- ⊢ s = t
  have sf_compatible : IsCompatible _ U sf := by
    intro i j
    simp_rw [← comp_apply, ← F.1.map_comp]
    rfl
  obtain ⟨gl, -, gl_uniq⟩ := F.existsUnique_gluing U sf sf_compatible
  -- ⊢ s = t
  trans gl
  -- ⊢ s = gl
  · apply gl_uniq
    -- ⊢ IsGluing F.val U sf s
    intro i
    -- ⊢ ↑(F.val.map (leSupr U i).op) s = sf i
    rfl
    -- 🎉 no goals
  · symm
    -- ⊢ t = gl
    apply gl_uniq
    -- ⊢ IsGluing F.val U sf t
    intro i
    -- ⊢ ↑(F.val.map (leSupr U i).op) t = sf i
    rw [← h]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq TopCat.Sheaf.eq_of_locally_eq

/-- In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
theorem eq_of_locally_eq' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (s t : F.1.obj (op V)) (h : ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) : s = t := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  -- ⊢ s = t
  suffices F.1.map (eqToHom V_eq_supr_U.symm).op s = F.1.map (eqToHom V_eq_supr_U.symm).op t by
    convert congr_arg (F.1.map (eqToHom V_eq_supr_U).op) this <;>
    rw [← comp_apply, ← F.1.map_comp, eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl,
      F.1.map_id, id_apply]
  apply eq_of_locally_eq
  -- ⊢ ∀ (i : ι), ↑(F.val.map (leSupr U i).op) (↑(F.val.map (eqToHom (_ : iSup U =  …
  intro i
  -- ⊢ ↑(F.val.map (leSupr U i).op) (↑(F.val.map (eqToHom (_ : iSup U = V)).op) s)  …
  rw [← comp_apply, ← comp_apply, ← F.1.map_comp]
  -- ⊢ ↑(F.val.map ((eqToHom (_ : iSup U = V)).op ≫ (leSupr U i).op)) s = ↑(F.val.m …
  convert h i
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq' TopCat.Sheaf.eq_of_locally_eq'

theorem eq_of_locally_eq₂ {U₁ U₂ V : Opens X} (i₁ : U₁ ⟶ V) (i₂ : U₂ ⟶ V) (hcover : V ≤ U₁ ⊔ U₂)
    (s t : F.1.obj (op V)) (h₁ : F.1.map i₁.op s = F.1.map i₁.op t)
    (h₂ : F.1.map i₂.op s = F.1.map i₂.op t) : s = t := by
  classical
    fapply F.eq_of_locally_eq' fun t : ULift Bool => if t.1 then U₁ else U₂
    · exact fun i => if h : i.1 then eqToHom (if_pos h) ≫ i₁ else eqToHom (if_neg h) ≫ i₂
    · refine' le_trans hcover _
      rw [sup_le_iff]
      constructor
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up True)
      · convert le_iSup (fun t : ULift Bool => if t.1 then U₁ else U₂) (ULift.up False)
    · rintro ⟨_ | _⟩
      any_goals exact h₁
      any_goals exact h₂
set_option linter.uppercaseLean3 false in
#align Top.sheaf.eq_of_locally_eq₂ TopCat.Sheaf.eq_of_locally_eq₂

end

end Sheaf

end TopCat
