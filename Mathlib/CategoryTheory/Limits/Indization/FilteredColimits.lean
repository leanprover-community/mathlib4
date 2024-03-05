/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Indization.IndObject
import Mathlib.Logic.Small.Set

/-!
# Ind-objects are closed under filtered colimits
-/

universe v v₁ u u₁

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

namespace IndizationClosedUnderFilteredColimitsAux

variable {I : Type v} [SmallCategory I] [IsFiltered I] (F : I ⥤ Cᵒᵖ ⥤ Type v)
  (hF : ∀ i, IsIndObject (F.obj i))

variable {J : Type v} [SmallCategory J] [FinCategory J]

variable (G : J ⥤ CostructuredArrow yoneda (colimit F))

-- We introduce notation for the functor `J ⥤ Over (colimit F)` induced by `G`.
local notation "𝒢" =>
  Functor.op G ⋙ Functor.op (CostructuredArrow.toOver yoneda (Cocone.pt (colimit.cocone F)))

section Interchange

/-!
We start by stating the key interchange property `exists_nonempty_limit_obj_of_is_colimit`. It
consists of pulling out a colimit out of a hom functor and interchanging a filtered colimit with
a finite limit.
-/

variable {K : Type v} [SmallCategory K] (H : K ⥤ Over (colimit.cocone F).pt)

/-- (implementation) Pulling out a colimit out of a hom functor is one half of the key lemma. Note
    that all of the heavy lifting actually happens in `CostructuredArrow.toOverCompYonedaColimit`
    and `yonedaYonedaColimit`. -/
noncomputable def compYonedaColimitIsoColimitCompYoneda :
    𝒢 ⋙ yoneda.obj (colimit H) ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := calc
  𝒢 ⋙ yoneda.obj (colimit H) ≅ 𝒢 ⋙ colimit (H ⋙ yoneda) :=
        isoWhiskerLeft G.op (CostructuredArrow.toOverCompYonedaColimit H)
  _ ≅ 𝒢 ⋙ (H ⋙ yoneda).flip ⋙ colim := isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip ⋙ colim := Iso.refl _
  _ ≅ colimit (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) := (colimitIsoFlipCompColim _).symm

theorem exists_nonempty_limit_obj_of_colimit [IsFiltered K]
    (h : Nonempty <| limit <| 𝒢 ⋙ yoneda.obj (colimit H)) :
    ∃ k, Nonempty <| limit <| 𝒢 ⋙ yoneda.obj (H.obj k) := by
  obtain ⟨t⟩ := h
  let t₂ := limMap (compYonedaColimitIsoColimitCompYoneda F G H).hom t
  let t₃ := (colimitLimitIsoMax (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip).inv t₂
  obtain ⟨k, y, -⟩ := Types.jointly_surjective'.{v, max u v} t₃
  refine ⟨k, ⟨?_⟩⟩
  let z := (limitObjIsoLimitCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢).flip k).hom y
  let y := flipCompEvaluation (H ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj 𝒢) k
  exact (lim.mapIso y).hom z

theorem exists_nonempty_limit_obj_of_isColimit [IsFiltered K] {c : Cocone H} (hc : IsColimit c)
    (T : Over (colimit.cocone F).pt) (hT : c.pt ≅ T)
    (h : Nonempty <| limit <| 𝒢 ⋙ yoneda.obj T) :
    ∃ k, Nonempty <| limit <| 𝒢 ⋙ yoneda.obj (H.obj k) := by
  refine exists_nonempty_limit_obj_of_colimit F G H ?_
  suffices T ≅ colimit H from Nonempty.map (lim.map (whiskerLeft 𝒢 (yoneda.map this.hom))) h
  refine hT.symm ≪≫ IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

end Interchange

theorem step₁ : Nonempty <| limit <| 𝒢 ⋙ yoneda.obj (Over.mk (𝟙 (colimit F))) :=
  ⟨Types.Limit.mk _ (fun j => Over.mkIdTerminal.from _) (by simp)⟩

noncomputable def myBetterFunctor : I ⥤ Jᵒᵖ ⥤ Type (max u v) :=
  (colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ yoneda ⋙
    (whiskeringLeft _ _ _).obj 𝒢

theorem step₇ : ∃ i, Nonempty <| limit <| (myBetterFunctor F G).obj i :=
  exists_nonempty_limit_obj_of_isColimit F G ((colimit.cocone F).toCostructuredArrow ⋙ CostructuredArrow.toOver _ _)
    (Over.isColimitToOver (colimit.isColimit F)) _ (Iso.refl _) (step₁ F G)

noncomputable def i : I := (step₇ F G).choose

theorem step₈ : Nonempty <| limit <| (myBetterFunctor F G).obj (i F G) :=
  (step₇ F G).choose_spec

abbrev K : Type v := (hF (i F G)).presentation.I

noncomputable def Kc : Cocone ((hF (i F G)).presentation.F ⋙ yoneda) :=
  (hF (i F G)).presentation.cocone

noncomputable def Kcl : IsColimit (Kc F hF G) :=
  (hF (i F G)).presentation.coconeIsColimit

lemma Kcpt : (Kc F hF G).pt = F.obj (i F G) := rfl

noncomputable def mappedCone := (Over.map (colimit.ι F (i F G))).mapCocone (Kc F hF G).toOver

lemma mappedCone_pt : (mappedCone F hF G).pt = Over.mk (colimit.ι F (i F G)) :=
  rfl

noncomputable def isColimitTo : IsColimit (Kc F hF G).toOver :=
  Over.isColimitToOver <| Kcl F hF G

noncomputable def isColimitMappedCone : IsColimit (mappedCone F hF G) :=
  isColimitOfPreserves (Over.map (colimit.ι F (i F G))) (isColimitTo F hF G)

noncomputable def indexing : (hF (i F G)).presentation.I ⥤ Over (colimit.cocone F).pt :=
  (Cocone.toCostructuredArrow (Kc F hF G) ⋙
        CostructuredArrow.toOver ((IsIndObject.presentation _).F ⋙ yoneda) (Kc F hF G).pt) ⋙
      Over.map (colimit.ι F (i F G))

theorem step₁₁ : ∃ k, Nonempty <| limit <| 𝒢 ⋙ yoneda.obj ((indexing F hF G).obj k) :=
  exists_nonempty_limit_obj_of_isColimit F G (indexing F hF G) (isColimitMappedCone F hF G) _ (Iso.refl _) (step₈ F G)

noncomputable def k : K F hF G := (step₁₁ F hF G).choose

theorem step₁₂ : Nonempty <| limit <| 𝒢 ⋙ yoneda.obj ((indexing F hF G).obj (k F hF G)) :=
  (step₁₁ F hF G).choose_spec

theorem bla : ((Over.map (colimit.ι F (i F G))).toPrefunctor.obj
          ((CostructuredArrow.toOver ((IsIndObject.presentation _).F ⋙ yoneda) (Kc F hF G).pt).toPrefunctor.obj
            (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))) =
          (CostructuredArrow.toOver yoneda (colimit F)).toPrefunctor.obj
    ((CostructuredArrow.pre (IsIndObject.presentation _).F yoneda (colimit F)).toPrefunctor.obj
      ((CostructuredArrow.map (colimit.ι F (i F G))).toPrefunctor.obj
        (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))) := by
  rfl

theorem isFiltered : IsFiltered (CostructuredArrow yoneda (colimit F)) := by
  refine IsFiltered.iff_nonempty_limit.mpr (fun {J _ _} G => ?_)
  have t := step₁₂ F hF G
  dsimp [indexing] at t
  rw [bla F hF G] at t
  let q := Yoneda.natIsoOfFullyFaithful.{v, max u v} (CostructuredArrow.toOver yoneda (colimit F))
  obtain ⟨t'⟩ := Nonempty.map (limMap (isoWhiskerLeft G.op (q _)).hom) t
  let v := preservesLimitIso uliftFunctor.{max u v, v} (G.op ⋙
    yoneda.toPrefunctor.obj
        ((CostructuredArrow.pre (IsIndObject.presentation _).F yoneda (colimit F)).toPrefunctor.obj
          ((CostructuredArrow.map (colimit.ι F (i F G))).toPrefunctor.obj
            (CostructuredArrow.mk ((Kc F hF G).ι.app (k F hF G))))))
  let t₂ := v.inv t'
  exact ⟨_, ⟨t₂.down⟩⟩

end IndizationClosedUnderFilteredColimitsAux

theorem isIndObject_colimit (I : Type v) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Cᵒᵖ ⥤ Type v) (hF : ∀ i, IsIndObject (F.obj i)) : IsIndObject (colimit F) := by
  have : IsFiltered (CostructuredArrow yoneda (colimit F)) :=
    IndizationClosedUnderFilteredColimitsAux.isFiltered F hF
  refine (isIndObject_iff _).mpr ⟨this, ?_⟩

  -- It remains to show that (yoneda / colimit F) is finally small. Because we have already shown
  -- it is filtered, it suffices to exhibit a small weakly terminal set.
  have : ∀ i, ∃ (s : Set (CostructuredArrow yoneda (F.obj i))) (_ : Small.{v} s),
      ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) :=
    fun i => (hF i).finallySmall.exists_small_weakly_terminal_set
  choose s hs j hjs hj using this
  refine finallySmall_of_small_weakly_terminal_set
    (⋃ i, (CostructuredArrow.map (colimit.ι F i)).obj '' (s i)) (fun A => ?_)
  obtain ⟨i, y, hy⟩ := FunctorToTypes.jointly_surjective'.{v, v} F _ (yonedaEquiv A.hom)
  let y' : CostructuredArrow yoneda (F.obj i) := CostructuredArrow.mk (yonedaEquiv.symm y)
  obtain ⟨x⟩ := hj _ y'
  refine ⟨(CostructuredArrow.map (colimit.ι F i)).obj (j i y'), ?_, ⟨?_⟩⟩
  · simp only [Set.mem_iUnion, Set.mem_image]
    refine ⟨i, j i y', hjs _ _, rfl⟩
  · refine ?_ ≫ (CostructuredArrow.map (colimit.ι F i)).map x
    refine CostructuredArrow.homMk (𝟙 A.left) (yonedaEquiv.injective ?_)
    simp [-EmbeddingLike.apply_eq_iff_eq, hy, yonedaEquiv_comp]

end CategoryTheory.Limits
