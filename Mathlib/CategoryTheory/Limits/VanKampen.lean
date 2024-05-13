/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

#align_import category_theory.extensive from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!

# Universal colimits and van Kampen colimits

## Main definitions
- `CategoryTheory.IsUniversalColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is universal
  if it is stable under pullbacks.
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.

## References
- https://ncatlab.org/nlab/show/van+Kampen+colimit
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

section NatTrans

/-- A natural transformation is equifibered if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def NatTrans.Equifibered {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)
#align category_theory.nat_trans.equifibered CategoryTheory.NatTrans.Equifibered

theorem NatTrans.equifibered_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩
#align category_theory.nat_trans.equifibered_of_is_iso CategoryTheory.NatTrans.equifibered_of_isIso

theorem NatTrans.Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
    (hβ : Equifibered β) : Equifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)
#align category_theory.nat_trans.equifibered.comp CategoryTheory.NatTrans.Equifibered.comp

theorem NatTrans.Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
#align category_theory.nat_trans.equifibered.whisker_right CategoryTheory.NatTrans.Equifibered.whiskerRight

theorem NatTrans.Equifibered.whiskerLeft {K : Type*} [Category K]  {F G : J ⥤ C} {α : F ⟶ G}
    (hα : Equifibered α) (H : K ⥤ J) : Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem mapPair_equifibered {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') :
    NatTrans.Equifibered α := by
  rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩
  all_goals
    dsimp; simp only [Discrete.functor_map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
#align category_theory.map_pair_equifibered CategoryTheory.mapPair_equifibered

theorem NatTrans.equifibered_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : NatTrans.Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

end NatTrans

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under pullbacks. -/
def IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) → Nonempty (IsColimit c')
#align category_theory.is_universal_colimit CategoryTheory.IsUniversalColimit

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone `c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullback of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserves it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
def IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ ∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)
#align category_theory.is_van_kampen_colimit CategoryTheory.IsVanKampenColimit

theorem IsVanKampenColimit.isUniversal {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c) :
    IsUniversalColimit c :=
  fun _ c' α f h hα => (H c' α f h hα).mpr
#align category_theory.is_van_kampen_colimit.is_universal CategoryTheory.IsVanKampenColimit.isUniversal

/-- A universal colimit is a colimit. -/
noncomputable def IsUniversalColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsUniversalColimit c) : IsColimit c := by
  refine ((h c (𝟙 F) (𝟙 c.pt : _) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (NatTrans.equifibered_of_isIso _)) fun j => ?_).some
  haveI : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by erw [NatTrans.id_app, Category.comp_id, Category.id_comp]⟩

/-- A van Kampen colimit is a colimit. -/
noncomputable def IsVanKampenColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsVanKampenColimit c) : IsColimit c :=
  h.isUniversal.isColimit
#align category_theory.is_van_kampen_colimit.is_colimit CategoryTheory.IsVanKampenColimit.isColimit

theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) := by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  haveI := h.isIso_to f
  refine' ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocones.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩
#align category_theory.is_initial.is_van_kampen_colimit CategoryTheory.IsInitial.isVanKampenColimit

section Functor

theorem IsUniversalColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (hc : IsUniversalColimit c)
    (e : c ≅ c') : IsUniversalColimit c' := by
  intro F' c'' α f h hα H
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  apply hc c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα
  intro j
  rw [← Category.comp_id (α.app j)]
  have : IsIso e.inv.hom := Functor.map_isIso (Cocones.forget _) e.inv
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨by simp⟩)

theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' := by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  haveI : IsIso e.inv.hom := Functor.map_isIso (Cocones.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm
#align category_theory.is_van_kampen_colimit.of_iso CategoryTheory.IsVanKampenColimit.of_iso

theorem IsVanKampenColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit ((Cocones.precompose α).obj c) := by
  intros F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e)
    (hα.comp (NatTrans.equifibered_of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [Functor.const_obj_obj, NatTrans.comp_app,
    Cocones.precompose_obj_pt, Cocones.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _, Category.comp_id]
  exact (congr_app e j).symm

theorem IsUniversalColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsUniversalColimit c) :
    IsUniversalColimit ((Cocones.precompose α).obj c) := by
  intros F' c' α' f e hα H
  apply (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e)
    (hα.comp (NatTrans.equifibered_of_isIso _)))
  intro j
  simp only [Functor.const_obj_obj, NatTrans.comp_app,
    Cocones.precompose_obj_pt, Cocones.precompose_obj_ι]
  rw [← Category.comp_id f]
  exact (H j).paste_vert (IsPullback.of_vert_isIso ⟨Category.comp_id _⟩)

theorem IsVanKampenColimit.precompose_isIso_iff {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} : IsVanKampenColimit ((Cocones.precompose α).obj c) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocones.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩

theorem IsUniversalColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsColimitsOfShape J G]
    (hc : IsUniversalColimit (G.mapCocone c)) : IsUniversalColimit c :=
  fun F' c' α f h hα H ↦
    ⟨ReflectsColimit.reflects (hc (G.mapCocone c') (whiskerRight α G) (G.map f)
    (by ext j; simpa using G.congr_map (NatTrans.congr_app h j))
    (hα.whiskerRight G) (fun j ↦ (H j).map G)).some⟩

theorem IsVanKampenColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [∀ (i j : J) (X : C) (f : X ⟶ F.obj j) (g : i ⟶ j), PreservesLimit (cospan f (F.map g)) G]
    [∀ (i : J) (X : C) (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) G]
    [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G]
    [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  refine' (Iff.trans _ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => _)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)
#align category_theory.is_van_kampen_colimit.of_map CategoryTheory.IsVanKampenColimit.of_mapCocone

theorem IsVanKampenColimit.mapCocone_iff (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [G.IsEquivalence] : IsVanKampenColimit (G.mapCocone c) ↔ IsVanKampenColimit c :=
  ⟨IsVanKampenColimit.of_mapCocone G, fun hc ↦ by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    exact hc.of_iso (Cocones.ext (G.asEquivalence.unitIso.app c.pt) (fun j => (by simp [e])))⟩

theorem IsUniversalColimit.whiskerEquivalence {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsUniversalColimit c) :
    IsUniversalColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα H
  convert hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
    ((hα.whiskerLeft _).comp (NatTrans.equifibered_of_isIso _)) ?_ using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · convert congr_arg (whiskerLeft e.inverse) e'
    ext
    simp
  · intro k
    rw [← Category.comp_id f]
    refine (H (e.inverse.obj k)).paste_vert ?_
    have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
    exact IsPullback.of_vert_isIso ⟨by simp⟩

theorem IsUniversalColimit.whiskerEquivalence_iff {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsUniversalColimit (c.whisker e.functor) ↔ IsUniversalColimit c :=
  ⟨fun hc ↦ ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocones.ext (Iso.refl _) (by simp)), IsUniversalColimit.whiskerEquivalence e⟩

theorem IsVanKampenColimit.whiskerEquivalence {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα
  convert hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
    ((hα.whiskerLeft _).comp (NatTrans.equifibered_of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j
          = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j)) := by
        simp [← Functor.map_comp]
      rw [← Category.id_comp f, this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

theorem IsVanKampenColimit.whiskerEquivalence_iff {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsVanKampenColimit (c.whisker e.functor) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocones.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩

theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : ∀ x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine' ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ _⟩⟩
    refine' fun x => (isLimitMapConePullbackConeEquiv _ _).symm _
    exact ((this x).mp ⟨PreservesColimit.preserves hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩
#align category_theory.is_van_kampen_colimit_of_evaluation CategoryTheory.isVanKampenColimit_of_evaluation

end Functor

section reflective

theorem IsUniversalColimit.map_reflective
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)}
    (H : IsUniversalColimit c)
    [∀ X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [∀ X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl] :
    IsUniversalColimit (Gl.mapCocone c) := by
  have := adj.rightAdjointPreservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjointPreservesColimits
  intros F' c' α f h hα hc'
  have : HasPullback (Gl.map (Gr.map f)) (Gl.map (adj.unit.app c.pt)) :=
    ⟨⟨_, isLimitPullbackConeMapOfIsLimit _ pullback.condition
      (IsPullback.of_hasPullback _ _).isLimit⟩⟩
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (NatTrans.equifibered_of_isIso _)
  have hadj : ∀ X, Gl.map (adj.unit.app X) = inv (adj.counit.app _) := by
    intro X
    apply IsIso.eq_inv_of_inv_hom_id
    exact adj.left_triangle_components _
  haveI : ∀ X, IsIso (Gl.map (adj.unit.app X)) := by
    simp_rw [hadj]
    infer_instance
  have hα'' : ∀ j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  have hc'' : ∀ j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := NatTrans.congr_app h
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let c'' : Cocone (F' ⋙ Gr) := by
    refine
    { pt := pullback (Gr.map f) (adj.unit.app _)
      ι := { app := fun j ↦ pullback.lift (Gr.map <| c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) ?_
             naturality := ?_ } }
    · rw [← Gr.map_comp, ← hc'']
      erw [← adj.unit_naturality]
      rw [Gl.map_comp, hα'']
      dsimp
      simp only [Category.assoc, Functor.map_comp, adj.right_triangle_components_assoc]
    · intros i j g
      dsimp [α']
      ext
      all_goals simp only [Category.comp_id, Category.id_comp, Category.assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp_assoc]
      · congr 1
        exact c'.w _
      · rw [α.naturality_assoc]
        dsimp
        rw [adj.counit_naturality, ← Category.assoc, Gr.map_comp_assoc]
        congr 1
        exact c.w _
  let cf : (Cocones.precompose β.hom).obj c' ⟶ Gl.mapCocone c'' := by
    refine { hom := pullback.lift ?_ f ?_ ≫ (PreservesPullback.iso _ _ _).inv, w := ?_ }
    · exact inv <| adj.counit.app c'.pt
    · rw [IsIso.inv_comp_eq, ← adj.counit_naturality_assoc f, ← cancel_mono (adj.counit.app <|
        Gl.obj c.pt), Category.assoc, Category.assoc, adj.left_triangle_components]
      erw [Category.comp_id]
      rfl
    · intro j
      rw [← Category.assoc, Iso.comp_inv_eq]
      ext
      all_goals simp only [PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd,
          pullback.lift_fst, pullback.lift_snd, Category.assoc,
          Functor.mapCocone_ι_app, ← Gl.map_comp]
      · rw [IsIso.comp_inv_eq, adj.counit_naturality]
        dsimp [β]
        rw [Category.comp_id]
      · rw [Gl.map_comp, hα'', Category.assoc, hc'']
        dsimp [β]
        rw [Category.comp_id, Category.assoc]
  have : cf.hom ≫ (PreservesPullback.iso _ _ _).hom ≫ pullback.fst ≫ adj.counit.app _ = 𝟙 _ := by
    simp only [IsIso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, pullback.lift_fst_assoc]
  have : IsIso cf := by
    apply @Cocones.cocone_iso_of_hom_iso (i := ?_)
    rw [← IsIso.eq_comp_inv] at this
    rw [this]
    infer_instance
  have ⟨Hc''⟩ := H c'' (whiskerRight α' Gr) pullback.snd ?_ (hα'.whiskerRight Gr) ?_
  · exact ⟨IsColimit.precomposeHomEquiv β c' <|
      (isColimitOfPreserves Gl Hc'').ofIsoColimit (asIso cf).symm⟩
  · ext j
    dsimp
    simp only [Category.comp_id, Category.id_comp, Category.assoc,
      Functor.map_comp, pullback.lift_snd]
  · intro j
    apply IsPullback.of_right _ _ (IsPullback.of_hasPullback _ _)
    · dsimp [α']
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_fst]
      rw [← Category.comp_id (Gr.map f)]
      refine ((hc' j).map Gr).paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
      rw [← adj.unit_naturality, Category.comp_id, ← Category.assoc,
        ← Category.id_comp (Gr.map ((Gl.mapCocone c).ι.app j))]
      congr 1
      rw [← cancel_mono (Gr.map (adj.counit.app (F.obj j)))]
      dsimp
      simp only [Category.comp_id, Adjunction.right_triangle_components, Category.id_comp,
        Category.assoc]
    · dsimp
      simp only [Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
        pullback.lift_snd]

theorem IsVanKampenColimit.map_reflective [HasColimitsOfShape J C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    {F : J ⥤ D} {c : Cocone (F ⋙ Gr)} (H : IsVanKampenColimit c)
    [∀ X (f : X ⟶ Gl.obj c.pt), HasPullback (Gr.map f) (adj.unit.app c.pt)]
    [∀ X (f : X ⟶ Gl.obj c.pt), PreservesLimit (cospan (Gr.map f) (adj.unit.app c.pt)) Gl]
    [∀ X i (f : X ⟶ c.pt), PreservesLimit (cospan f (c.ι.app i)) Gl] :
    IsVanKampenColimit (Gl.mapCocone c) := by
  have := adj.rightAdjointPreservesLimits
  have : PreservesColimitsOfSize.{u', v'} Gl := adj.leftAdjointPreservesColimits
  intro F' c' α f h hα
  refine ⟨?_, H.isUniversal.map_reflective adj c' α f h hα⟩
  intro ⟨hc'⟩ j
  let α' := α ≫ (Functor.associator _ _ _).hom ≫ whiskerLeft F adj.counit ≫ F.rightUnitor.hom
  have hα' : NatTrans.Equifibered α' := hα.comp (NatTrans.equifibered_of_isIso _)
  have hα'' : ∀ j, Gl.map (Gr.map <| α'.app j) = adj.counit.app _ ≫ α.app j := by
    intro j
    rw [← cancel_mono (adj.counit.app <| F.obj j)]
    dsimp [α']
    simp only [Category.comp_id, Adjunction.counit_naturality_assoc, Category.id_comp,
      Adjunction.counit_naturality, Category.assoc, Functor.map_comp]
  let β := isoWhiskerLeft F' (asIso adj.counit) ≪≫ F'.rightUnitor
  let hl := (IsColimit.precomposeHomEquiv β c').symm hc'
  let hr := isColimitOfPreserves Gl (colimit.isColimit <| F' ⋙ Gr)
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map <| α'.app j) := by
    rw [hα'']
    simp [β]
  rw [this]
  have : f = (hl.coconePointUniqueUpToIso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) := by
    symm
    convert @IsColimit.coconePointUniqueUpToIso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
      (Gl.mapCocone ⟨_, (whiskerRight α' Gr ≫ c.2 : _)⟩) _ _ hl hr using 2
    · apply hr.hom_ext
      intro j
      rw [hr.fac, Functor.mapCocone_ι_app, ← Gl.map_comp, colimit.cocone_ι, colimit.ι_desc]
      rfl
    · clear_value α'
      apply hl.hom_ext
      intro j
      rw [hl.fac]
      dsimp [β]
      simp only [Category.comp_id, hα'', Category.assoc, Gl.map_comp]
      congr 1
      exact (NatTrans.congr_app h j).symm
  rw [this]
  have := ((H (colimit.cocone <| F' ⋙ Gr) (whiskerRight α' Gr)
    (colimit.desc _ ⟨_, whiskerRight α' Gr ≫ c.2⟩) ?_ (hα'.whiskerRight Gr)).mp
    ⟨(getColimitCocone <| F' ⋙ Gr).2⟩ j).map Gl
  · convert IsPullback.paste_vert _ this
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← IsIso.inv_comp_eq, ← Category.assoc, NatIso.inv_inv_app]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hl hr _
  · clear_value α'
    ext j
    simp

end reflective

section Initial

theorem hasStrictInitial_of_isUniversal [HasInitial C]
    (H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C :=
  hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases(Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine' (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> simp)
        (mapPair_equifibered _) _).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
#align category_theory.has_strict_initial_of_is_universal CategoryTheory.hasStrictInitial_of_isUniversal

theorem isVanKampenColimit_of_isEmpty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  have : IsInitial c.pt := by
    have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocones.ext (Iso.refl c.pt) (fun {X} ↦ isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocones.ext (Iso.refl _) (by simp))

end Initial

section BinaryCoproduct

variable {X Y : C}

theorem BinaryCofan.isVanKampen_iff (c : BinaryCofan X Y) :
    IsVanKampenColimit c ↔
      ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.pt ⟶ c.pt)
        (_ : αX ≫ c.inl = c'.inl ≫ f) (_ : αY ≫ c.inr = c'.inr ≫ f),
        Nonempty (IsColimit c') ↔ IsPullback c'.inl αX f c.inl ∧ IsPullback c'.inr αY f c.inr := by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (mapPair_equifibered _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩
#align category_theory.binary_cofan.is_van_kampen_iff CategoryTheory.BinaryCofan.isVanKampen_iff

theorem BinaryCofan.isVanKampen_mk {X Y : C} (c : BinaryCofan X Y)
    (cofans : ∀ X Y : C, BinaryCofan X Y) (colimits : ∀ X Y, IsColimit (cofans X Y))
    (cones : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g)
    (limits : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (cones f g))
    (h₁ : ∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt)
      (_ : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (_ : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
      IsPullback (cofans X' Y').inl αX f c.inl ∧ IsPullback (cofans X' Y').inr αY f c.inr)
    (h₂ : ∀ {Z : C} (f : Z ⟶ c.pt),
      IsColimit (BinaryCofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
    IsVanKampenColimit c := by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [e, hX]) (by simp [e, hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      haveI : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      haveI : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp [e]
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
    refine' ⟨IsColimit.ofIsoColimit _ <| (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp [e₁]
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp [e₂]
    rw [he₁, he₂]
    apply BinaryCofan.isColimitCompRightIso (BinaryCofan.mk _ _)
    apply BinaryCofan.isColimitCompLeftIso (BinaryCofan.mk _ _)
    exact h₂ f
#align category_theory.binary_cofan.is_van_kampen_mk CategoryTheory.BinaryCofan.isVanKampen_mk

theorem BinaryCofan.mono_inr_of_isVanKampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr := by
  refine' PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit _)
  refine' (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some
#align category_theory.binary_cofan.mono_inr_of_is_van_kampen CategoryTheory.BinaryCofan.mono_inr_of_isVanKampen

theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine' ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some
#align category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen

end BinaryCoproduct

section FiniteCoproducts

theorem isUniversalColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsUniversalColimit c₁) (t₂ : IsUniversalColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i] :
    IsUniversalColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα H
  let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F' := by
    apply Functor.hext
    · exact fun i ↦ rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp [F']
  have t₁' := @t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) fun j ↦ pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans fun i ↦ α.app _) pullback.fst ?_ (NatTrans.equifibered_of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj, id_eq,
      extendCofan_pt, eq_mpr_eq_cast, Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i)) (BinaryCofan.mk (c.ι.app ⟨0⟩) pullback.snd)
    (mapPair (α.app _) pullback.fst) i ?_ (mapPair_equifibered _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using congr_app e ⟨0⟩
    · simpa using pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i ↦ (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocones.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [Discrete.functor_obj, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction' j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

theorem isVanKampenColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsVanKampenColimit c₁) (t₂ : IsVanKampenColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i]
    [HasFiniteCoproducts C] :
    IsVanKampenColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) ↦ F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc fun b ↦ c.ι.app _))
    (mapPair (α.app _) (Sigma.desc fun b ↦ α.app _ ≫ c₁.inj _)) i ?_
    (mapPair_equifibered _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F' := by
      apply Functor.hext
      · exact fun i ↦ rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp [F']
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ ↦ Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_right, BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app]
      induction' j using Fin.inductionOn with j _
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction' j using Fin.inductionOn with j _
  · exact t₂' ⟨WalkingPair.left⟩
  · have t₁' := (@t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      fun i ↦ α.app _) (Sigma.desc (fun j ↦ α.app _ ≫ c₁.inj _)) ?_
      (NatTrans.equifibered_of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      erw [colimit.ι_desc] -- Why?
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

theorem isPullback_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {X : ι → C}
    {c : Cofan X} (hc : IsVanKampenColimit c) (i j : ι) [DecidableEq ι] :
    IsPullback (P := (if j = i then X i else ⊥_ C))
      (if h : j = i then eqToHom (if_pos h) else eqToHom (if_neg h) ≫ initial.to (X i))
      (if h : j = i then eqToHom ((if_pos h).trans (congr_arg X h.symm))
        else eqToHom (if_neg h) ≫ initial.to (X j))
      (Cofan.inj c i) (Cofan.inj c j) := by
  refine (hc (Cofan.mk (X i) (f := fun k ↦ if k = i then X i else ⊥_ C)
    (fun k ↦ if h : k = i then (eqToHom <| if_pos h) else (eqToHom <| if_neg h) ≫ initial.to _))
    (Discrete.natTrans (fun k ↦ if h : k.1 = i then (eqToHom <| (if_pos h).trans
      (congr_arg X h.symm)) else (eqToHom <| if_neg h) ≫ initial.to _))
    (c.inj i) ?_ (NatTrans.equifibered_of_discrete _)).mp ⟨?_⟩ ⟨j⟩
  · ext ⟨k⟩
    simp only [Discrete.functor_obj, Functor.const_obj_obj, NatTrans.comp_app,
      Discrete.natTrans_app, Cofan.mk_pt, Cofan.mk_ι_app, Functor.const_map_app]
    split
    · subst ‹k = i›; rfl
    · simp
  · refine mkCofanColimit _ (fun t ↦ (eqToHom (if_pos rfl).symm) ≫ t.inj i) ?_ ?_
    · intro t j
      simp only [Cofan.mk_pt, cofan_mk_inj]
      split
      · subst ‹j = i›; simp
      · rw [Category.assoc, ← IsIso.eq_inv_comp]
        exact initialIsInitial.hom_ext _ _
    · intro t m hm
      simp [← hm i]

theorem isPullback_initial_to_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i j : Discrete ι) (hi : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  have : ∀ i, Subsingleton (⊥_ C ⟶ (Discrete.functor f).obj i) := inferInstance
  convert isPullback_of_cofan_isVanKampen hc i.as j.as
  exact (if_neg (mt (Discrete.ext _ _) hi.symm)).symm

theorem mono_of_cofan_isVanKampen [HasInitial C] {ι : Type*} {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsVanKampenColimit c) (i : Discrete ι) : Mono (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  refine' PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit _)
  nth_rw 1 [← Category.id_comp (c.ι.app i)]
  convert IsPullback.paste_vert _ (isPullback_of_cofan_isVanKampen hc i.as i.as)
  swap
  · exact (eqToHom (if_pos rfl).symm)
  · simp
  · exact IsPullback.of_vert_isIso ⟨by simp⟩

end FiniteCoproducts

end CategoryTheory
