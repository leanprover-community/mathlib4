/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
import Mathlib.CategoryTheory.Category.Quiv.AsFunctor.Defs
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Filtered.Level.Presheaves
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

import Mathlib.Tactic.LiftLets

/-!
  # Colimits in `Quiv.{v, u}`

  In `AsFunctor.Defs`, we showed that `Quiv.{v, u}` is equivalent to the full subcategory of
  `WalkingQuiver ⥤ Type max v u` which are `u`-small and locally `v`-small.

  However, precisely because `Quiv.{v, u}` is no longer equivalent to the entire presheaf
  category, it is no longer equivalent to its own cocompletion. Concretely, any colimit that
  identifies a `u`-sized collection of vertices has the potential to introduce a pair of vertices
  with a `max u v`-sized type of edges between them.

  As such, if `v ≤ u`, then `Quiv.{v, u}` has all `u`-small colimits. In addition, `Quiv.{v, u}`
  always has all coproducts, as well as all `u`-filtered colimits.
-/
namespace CategoryTheory.Quiv

open Limits PresheafWalkingQuiver ObjectProperty
universe w v u w'


variable [UnivLE.{w, v}] [UnivLE.{w, u}] {J : Type w}
         (F : Discrete J ⥤ Quiv.{v, u})

-- /--
-- We explicitly construct the coproduct of a family of objects in `Quiv.{v, u}` in functor form. -/
-- @[simps]
-- noncomputable def coprodAsFunctor : WalkingQuiver ⥤ Type max w v u where
--   obj
--     | 0 => Σ (j : Discrete J), ULift.{v} (F.obj j)
--     | 1 => Σ (j : Discrete J), (s t : ULift.{v} (F.obj j)) × (s.1 ⟶ t.1)
--   map
--     | .id _ => id
--     | .source => fun je ↦ ⟨je.1, ⟨je.2.1.1⟩⟩
--     | .target => fun je ↦ ⟨je.1, ⟨je.2.2.1.1⟩⟩
--   map_id q₀ := by
--     cases q₀ with
--     | zero => ext1 ⟨j, ⟨x⟩⟩; simp
--     | one => ext1 ⟨j, s, t, e⟩; simp
--   map_comp {X Y Z} f g := by
--     cases f
--     case source | target =>
--       cases g; ext1 ⟨j, s, t, e⟩; simp
--     case id =>
--       rw [WalkingQuiver.id_def, Category.id_comp]
--       ext; simp

-- namespace coprodAsFunctor

-- def vertexEquiv : Vertex (coprodAsFunctor F) ≃ (Σ j : J, F.obj ⟨j⟩) :=
--   discreteEquiv.sigmaCongr fun _ ↦ Equiv.ulift

-- noncomputable def vertexEquivShrink :
--     Vertex (coprodAsFunctor F) ≃ (Σ j : Shrink.{u} J, F.obj ⟨equivShrink _ |>.symm j⟩) :=
--   vertexEquiv F |>.trans <| equivShrink _|>.sigmaCongrLeft'

-- -- @[simps?! +simpRhs]
-- noncomputable def edgeEquiv (j : Discrete J) (X Y : F.obj j) :
--     Edge (coprodAsFunctor F) ⟨j, ⟨X⟩⟩ ⟨j, ⟨Y⟩⟩ ≃ (X ⟶ Y) where
--   toFun := fun ⟨⟨j', s, t, e⟩, hs, ht⟩ ↦
--     have : j = j' := by simp at hs; exact hs.1.symm
--     let ε := eqToIso (congrArg F.obj this)
--     Quiver.homOfEq (ε.inv.map e) (by cases this; simpa using hs) (by cases this; simpa using ht)
--   invFun f := ⟨⟨j, ⟨X⟩, ⟨Y⟩, f⟩, rfl, rfl⟩
--   left_inv := by
--     rintro ⟨⟨j', s, t, e⟩, hs, ht⟩
--     simp only [coprodAsFunctor_obj, coprodAsFunctor_map, Sigma.mk.injEq] at hs
--     rcases hs with ⟨rfl, hs⟩
--     simp at hs ht; subst hs ht
--     ext
--     simp
--   right_inv f := by simp

-- omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
-- lemma edgeEmpty {j j' : Discrete J} (h : j ≠ j') (X Y):
--     IsEmpty (Edge (coprodAsFunctor F) ⟨j, ⟨X⟩⟩ ⟨j', ⟨Y⟩⟩) := by
--   contrapose! h
--   rw [not_isEmpty_iff] at h
--   rcases h with ⟨⟨⟨j₀, s, t, e⟩, hs, ht⟩⟩
--   simp at hs ht
--   exact hs.1.symm.trans ht.1



-- omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
-- @[simp] lemma naturality_src_sigma (j : Discrete J)
--     (e : ((F ⋙ quivEquiv.functor).obj j).obj.obj 1) :
--     @src (coprodAsFunctor F) ⟨j, e⟩ = ⟨j, src e⟩ := by
--   rcases e with ⟨s, t, e⟩
--   apply Sigma.ext
--   · simp
--   · rw [heq_eq_eq]
--     simp only [ULift.up_down]; rfl


-- omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
-- @[simp] lemma naturality_tgt_sigma (j : Discrete J)
--     (e : ((F ⋙ quivEquiv.functor).obj j).obj.obj 1) :
--     @tgt (coprodAsFunctor F) ⟨j, e⟩ = ⟨j, tgt e⟩ := by
--   rcases e with ⟨s, t, e⟩
--   apply Sigma.ext
--   · simp
--   · rw [heq_eq_eq]
--     simp only [ULift.up_down]; rfl

-- open Classical in
-- instance instSmallAsQuiv : SmallAsQuiv.{v, u} (coprodAsFunctor.{w} F) where
--   small_vertex := ⟨⟨_, ⟨vertexEquivShrink F⟩⟩⟩
--   small_edge := fun ⟨j, ⟨X⟩⟩ ⟨j', ⟨Y⟩⟩ ↦ by
--     if h : j = j' then
--       cases h
--       exact ⟨⟨_, ⟨edgeEquiv F j X Y⟩⟩⟩
--     else
--       have := edgeEmpty F h X Y
--       infer_instance

-- noncomputable abbrev coprodCocone : Cocone (F ⋙ quivEquiv.functor) where
--   pt := ⟨coprodAsFunctor.{w} F, inferInstance⟩
--   ι := Discrete.natTrans fun j ↦ {
--       app
--         | 0 => fun X ↦ ⟨j, ⟨X.1⟩⟩
--         | 1 => fun e ↦ ⟨j, ⟨.up (hom e).1.1.1, .up (hom e).1.2.1.1, (hom e).1.2.2⟩⟩,
--       naturality
--         | _, _, .id _ => by ext; simp
--         | _, _, .source => by
--             ext e
--             simp_rw [types_comp_apply, ← src.eq_def]
--             rw [naturality_src_sigma]
--             simp [ULift.up_down]; rfl
--         | _, _, .target => by
--             ext e
--             simp_rw [types_comp_apply, ← tgt.eq_def]
--             rw [naturality_tgt_sigma]
--             simp [ULift.up_down]; rfl}

-- noncomputable def coprodCocone_isCoproduct :
--     IsColimit (fullSubcategoryInclusion _ |>.mapCocone <| coprodCocone F) := by
--   apply evaluationJointlyReflectsColimits
--   intro m; cases m with
--   | zero =>
--       fconstructor
--       · exact fun ⟨pt, ⟨ι, nat⟩⟩ jp ↦ ι jp.1 ⟨jp.2.1⟩
--       · rintro ⟨pt, ι⟩ j
--         ext p
--         simp [ULift.up_down] at p ⊢
--       · rintro ⟨pt, ι⟩ ι hι
--         ext ⟨j, ⟨p⟩⟩
--         conv at hι =>
--           ext j
--           erw [funext_iff]
--           ext p
--           rw [types_comp_apply]
--         simp [funext_iff, types_comp_apply] at ι p hι ⊢
--         exact hι j ⟨p⟩
--   | one =>
--       fconstructor
--       · exact fun ⟨pt, ⟨ι, nat⟩⟩ je ↦ ι je.1 ⟨je.2⟩
--       · rintro ⟨pt, ι⟩ j
--         ext ⟨s, t, e⟩
--         simp
--       · rintro ⟨pt, ι⟩ π hπ
--         ext ⟨j, e⟩
--         simp [funext_iff, types_comp_apply] at π hπ ⊢
--         exact hπ j e

-- end coprodAsFunctor
-- open coprodAsFunctor
-- def shrinkPiIsProd : (Π j : J, F.obj ⟨j⟩)

-- noncomputable def prod :=
--   let vIso := Types.productIso.{w, max v u} (fun j ↦ (F.obj ⟨j⟩).α)
--   combineCones (F ⋙ asOfFunctor.functor ⋙ fullSubcategoryInclusion _)
--     fun | 0 => (Π j : Shrink.{u} J, F.obj ⟨equivShrink _ |>.symm j⟩)
#check small_sigma

#check Types.coproductIso_mk_comp_inv

omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
@[simp]
lemma Types.coproductIso_mk_comp_inv_apply {J : Type v} (F : J → Type (max v u)) (j : J) (x : F j) :
    (Types.coproductIso F).inv ⟨j, x⟩ = Sigma.ι F j x := rfl

omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
@[simp]
lemma Types.coproductIso_mk_comp_inv_apply' {J : Type v} (F : J → Type (max v u))
    (jx : (j : J) × (F j)) : (Types.coproductIso F).inv jx = Sigma.ι F jx.1 jx.2 := rfl

omit [UnivLE.{w, v}] in
lemma smallAsQuivClosedUnderCoproducts :
    ClosedUnderColimitsOfShape (Discrete J) SmallAsQuiv.{v, u, max w v u} :=
  closedUnderColimitsOfShape_of_colimit fun {F} [_] hF ↦
    -- let F' := Discrete.functor (F.obj ∘ Discrete.mk)
    let ι : ∐ (F.obj ⟨·⟩) ≅ colimit F :=
      eqToIso (colim_obj _).symm ≪≫ colim.mapIso (Discrete.natIsoFunctor).symm ≪≫
        eqToIso (colim_obj _)
    let ε q₀ : (∐ (F.obj ⟨·⟩)).obj q₀ ≅ (j : J) × (F.obj { as := j }).obj q₀ :=
      sigmaObjIso _ q₀ ≪≫ Types.coproductIso _
    prop_of_iso _ ι {
      small_vertex := by
        rw [small_congr (ε 0).toEquiv]
        have h j := hF ⟨j⟩ |>.small_vertex
        infer_instance
      small_edge := by
        unfold Vertex Edge
        rw [Equiv.forall₂_congr (ε 0).toEquiv (ε 0).toEquiv
          (q := fun s t ↦
            Small.{v} { e // src e = (ε 0).toEquiv.symm s ∧ tgt e = (ε 0).toEquiv.symm t })
          fun {s t} ↦ by simp]
        rintro ⟨j, s⟩ ⟨j', t⟩
        rw [small_congr (Equiv.subtypeEquivOfSubtype' (ε 1).toEquiv)]
        simp [ε]
        simp_rw [← types_comp_apply _ (sigmaObjIso (F.obj ⟨·⟩) _).inv, ι_comp_sigmaObjIso_inv,
        Sigma.ι, naturality_src, naturality_tgt, ← Sigma.ι.eq_def,  ← ι_comp_sigmaObjIso_inv,
        types_comp_apply, ← Types.coproductIso_mk_comp_inv_apply (F.obj ⟨·⟩ |>.obj 0),
        Function.Injective.eq_iff (mono_iff_injective (Iso.inv _) |>.mp inferInstance)]
        by_cases h : j = j'
        · cases h
          have {p q r s} : ((p ∧ q) ∧ (r ∧ s)) = ((p ∧ r) ∧ q ∧ s) := by ac_rfl
          simp_rw [Sigma.ext_iff, this, and_self]
          -- let ε : {e : Σ j, (F.obj j).obj 1 // e.1 = j ∧ HEq (src e.2) s ∧ HEq (tgt e.2) t} ≃
          --   (j : J)
          rw [small_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm,
          small_congr (Equiv.subtypeEquivOfSubtype' <| Equiv.sigmaSubtype j)]
          simp
          infer_instance
        · rw [small_congr (Equiv.subtypeEquivRight (q := fun _ ↦ False) ?h)]
          · infer_instance
          · rintro ⟨j, x⟩
            simp only [Sigma.mk.injEq, iff_false, not_and, and_imp, ε]
            rintro rfl h₂ rfl
            contradiction }

instance (F : J → WalkingQuiver ⥤ Type max w v u) [∀ j, SmallAsQuiv.{v, u} (F j)] :
    SmallAsQuiv.{v, u} (∐ F) :=
  smallAsQuivClosedUnderCoproducts.{w, v, u}.colimit
    fun ⟨j⟩ ↦ inferInstanceAs <| SmallAsQuiv.{v, u} (F j)

section
variable (J : Type w) [Category.{w} J] (C : Type u) [Category.{v} C]
         {F : J ⥤ WalkingQuiver ⥤ Type max w v u}
omit [UnivLE.{w, v}]

/-- `SmallAsQuiv.{v, u}` is closed under arbitrary colimits if `UnivLE.{u, v}`.

(It is *not* closed under arbitrary colimits in general, because colimits may
identify vertices without identifying their edges and thus may produce hom-types
of size `max v u`. -/
lemma smallAsQuivClosedUnderColimits_ofSmall [UnivLE.{u, v}] :
    ClosedUnderColimitsOfShape J SmallAsQuiv.{v, u, max w v u} := fun F ι hι hF ↦ by
  suffices ∃ (π : ∐ F.obj ⟶ colimit F), Epi π by
    obtain ⟨π, hπ⟩ := this
    let π' := π ≫ (hι.coconePointUniqueUpToIso (colimit.isColimit F)).inv
    convert smallAsQuiv_ofEpi_ofSmall.{max w v u} π'
    -- apply smallAsQuivClosedUnderCoproducts.{w}.colimit
    -- rintro ⟨j⟩
    -- simpa using hF j
  use Limits.colimitQuotientCoproduct F
  infer_instance


instance : HasCoproducts.{w} SmallAsQuivSubcategory.{v, u, max w v u} := fun _ ↦
  hasColimitsOfShape_of_closedUnderColimits <| smallAsQuivClosedUnderCoproducts

instance [UnivLE.{u, v}] : HasColimitsOfSize.{w, w} SmallAsQuivSubcategory.{v, u, max w v u} where
  has_colimits_of_shape J _ :=
    hasColimitsOfShape_of_closedUnderColimits <| smallAsQuivClosedUnderColimits_ofSmall J


/-- The category of quivers has all coproducts. -/
instance : HasCoproducts.{w} Quiv.{v, u} := fun _ ↦
  Adjunction.hasColimitsOfShape_of_equivalence quivEquiv.functor.{w, v, u}

/-- The category of quivers has all colimits when `UnivLE.{u, v}`. -/
instance [UnivLE.{u, v}] : HasColimitsOfSize.{w, w} Quiv.{v, u} :=
  Adjunction.has_colimits_of_equivalence quivEquiv.functor.{w, v, u}

end

end CategoryTheory.Quiv
