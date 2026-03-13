/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Gluing data

We define `GlueData` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also state lemmas about its
interaction with a functor that preserves certain pullbacks.

-/

@[expose] public section


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u₁ u₂

variable (C : Type u₁) [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-- A gluing datum consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
4. A monomorphism `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. The pullback for `f i j` and `f i k` exists.
9. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
10. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
structure GlueData where
  /-- The index type `J` of a gluing datum -/
  J : Type v
  /-- For each `i : J`, an object `U i` -/
  U : J → C
  /-- For each `i j : J`, an object `V i j` -/
  V : J × J → C
  /-- For each `i j : J`, a monomorphism `f i j : V i j ⟶ U i` -/
  f : ∀ i j, V (i, j) ⟶ U i
  f_mono : ∀ i j, Mono (f i j) := by infer_instance
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k) := by infer_instance
  f_id : ∀ i, IsIso (f i i) := by infer_instance
  /-- For each `i j : J`, a transition map `t i j : V i j ⟶ V j i` -/
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  /-- The morphism via which `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through
  `V j k ×[U j] V j i ⟶ V j i` -/
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

attribute [simp] GlueData.t_id

attribute [instance] GlueData.f_id GlueData.f_mono GlueData.f_hasPullback

attribute [reassoc] GlueData.t_fac GlueData.cocycle

namespace GlueData

variable {C}
variable (D : GlueData C)

@[simp]
theorem t'_iij (i j : D.J) : D.t' i i j = (pullbackSymmetry _ _).hom := by
  have eq₁ := D.t_fac i i j
  have eq₂ := (IsIso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id, Category.comp_id, eq₂] at eq₁
  have eq₃ := (IsIso.eq_comp_inv (D.f i i)).mp eq₁
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at eq₃
  exact
    Mono.right_cancellation _ _
      ((Mono.right_cancellation _ _ eq₃).trans (pullbackSymmetry_hom_comp_fst _ _).symm)

theorem t'_jii (i j : D.J) : D.t' j i i = pullback.fst _ _ ≫ D.t j i ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc, ← D.t_fac]
  simp

theorem t'_iji (i j : D.J) : D.t' i j i = pullback.fst _ _ ≫ D.t i j ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc, ← D.t_fac]
  simp

@[reassoc, elementwise (attr := simp)]
theorem t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := by
  have eq : (pullbackSymmetry (D.f i i) (D.f i j)).hom =
      pullback.snd _ _ ≫ inv (pullback.fst _ _) := by simp
  have := D.cocycle i j i
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, eq] at this
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at this
  rw [← IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq] at this
  simpa using this

theorem t'_inv (i j k : D.J) :
    D.t' i j k ≫ (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom = 𝟙 _ := by
  rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
  simp [t_fac, t_fac_assoc]

instance t_isIso (i j : D.J) : IsIso (D.t i j) :=
  ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

instance t'_isIso (i j k : D.J) : IsIso (D.t' i j k) :=
  ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by simpa using D.cocycle _ _ _⟩⟩

@[reassoc]
theorem t'_comp_eq_pullbackSymmetry (i j k : D.J) :
    D.t' j k i ≫ D.t' k i j =
      (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom := by
  trans inv (D.t' i j k)
  · exact IsIso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
  · rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
    simp [t_fac, t_fac_assoc]

/-- (Implementation) The disjoint union of `U i`. -/
def sigmaOpens [HasCoproduct D.U] : C :=
  ∐ D.U

/-- (Implementation) The diagram to take colimit of. -/
def diagram : MultispanIndex (.prod D.J) C where
  left := D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]
theorem diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j :=
  rfl

@[simp]
theorem diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i :=
  rfl

@[simp]
theorem diagram_left : D.diagram.left = D.V :=
  rfl

@[simp]
theorem diagram_right : D.diagram.right = D.U :=
  rfl

section

variable [HasMulticoequalizer D.diagram]

/-- The glued object given a family of gluing data. -/
def glued : C :=
  multicoequalizer D.diagram

/-- The map `D.U i ⟶ D.glued` for each `i`. -/
def ι (i : D.J) : D.U i ⟶ D.glued :=
  Multicoequalizer.π D.diagram i

@[elementwise (attr := simp)]
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  (Category.assoc _ _ _).symm.trans (Multicoequalizer.condition D.diagram ⟨i, j⟩).symm

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This will often be a pullback diagram. -/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

variable [HasColimits C]

/-- The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigmaOpens ⟶ D.glued :=
  Multicoequalizer.sigmaπ D.diagram

set_option backward.isDefEq.respectTransparency false in
instance π_epi : Epi D.π := by
  unfold π
  infer_instance

end

universe w in
theorem types_π_surjective (D : GlueData (Type w)) : Function.Surjective D.π :=
  (epi_iff_surjective _).mp inferInstance

theorem types_ι_jointly_surjective (D : GlueData (Type v)) (x : D.glued) :
    ∃ (i : _) (y : D.U i), D.ι i y = x := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  --have := colimit.isoColimitCocone (Types.coproductColimitCocone _)
  rw [← show (colimit.isoColimitCocone (Types.coproductColimitCocone.{v, v} _)).inv _ = x' from
      ConcreteCategory.congr_hom
        (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom_inv_id x']
  rcases (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom x' with ⟨i, y⟩
  exact ⟨i, y, by
    simp
    rfl ⟩

variable (F : C ⥤ C')

section
variable [∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

instance (i j k : D.J) : HasPullback (F.map (D.f i j)) (F.map (D.f i k)) :=
  ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit F (D.f i j) (D.f i k)⟩⟩⟩

/-- A functor that preserves the pullbacks of `f i j` and `f i k` can map a family of glue data. -/
@[simps]
def mapGlueData : GlueData C' where
  J := D.J
  U i := F.obj (D.U i)
  V i := F.obj (D.V i)
  f i j := F.map (D.f i j)
  f_mono _ _ := preserves_mono_of_preservesLimit _ _
  f_id _ := inferInstance
  t i j := F.map (D.t i j)
  t_id i := by
    simp
  t' i j k :=
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k) ≫ (PreservesPullback.iso F (D.f j k) (D.f j i)).hom
  t_fac i j k := by simpa [Iso.inv_comp_eq] using congr_arg (fun f => F.map f) (D.t_fac i j k)
  cocycle i j k := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, D.cocycle,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The diagram of the image of a `GlueData` under a functor `F` is naturally isomorphic to the
original diagram of the `GlueData` via `F`.
-/
def diagramIso : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | WalkingMultispan.left _ => Iso.refl _
      | WalkingMultispan.right _ => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _) <;> simp)

@[simp]
theorem diagramIso_app_left (i : D.J × D.J) :
    (D.diagramIso F).app (WalkingMultispan.left i) = Iso.refl _ :=
  rfl

@[simp]
theorem diagramIso_app_right (i : D.J) :
    (D.diagramIso F).app (WalkingMultispan.right i) = Iso.refl _ :=
  rfl

@[simp]
theorem diagramIso_hom_app_left (i : D.J × D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagramIso_hom_app_right (i : D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagramIso_inv_app_left (i : D.J × D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
theorem diagramIso_inv_app_right (i : D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

end

variable [HasMulticoequalizer D.diagram] [PreservesColimit D.diagram.multispan F]

theorem hasColimit_multispan_comp : HasColimit (D.diagram.multispan ⋙ F) :=
  ⟨⟨⟨_, isColimitOfPreserves _ (colimit.isColimit _)⟩⟩⟩

attribute [local instance] hasColimit_multispan_comp

variable [∀ i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

set_option backward.isDefEq.respectTransparency false in
theorem hasColimit_mapGlueData_diagram : HasMulticoequalizer (D.mapGlueData F).diagram :=
  hasColimit_of_iso (D.diagramIso F).symm

attribute [local instance] hasColimit_mapGlueData_diagram

set_option backward.isDefEq.respectTransparency false in
/-- If `F` preserves the gluing, we obtain an iso between the glued objects. -/
def gluedIso : F.obj D.glued ≅ (D.mapGlueData F).glued :=
  haveI : HasColimit (MultispanIndex.multispan (diagram (mapGlueData D F))) := inferInstance
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_gluedIso_hom (i : D.J) : F.map (D.ι i) ≫ (D.gluedIso F).hom = (D.mapGlueData F).ι i := by
  erw [ι_preservesColimitIso_hom_assoc]
  simp [GlueData.ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_gluedIso_inv (i : D.J) : (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i) := by
  rw [Iso.comp_inv_eq, ι_gluedIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j ⟶ glued`,
then `F` reflects the fact that `V_pullback_cone` is a pullback. -/
def vPullbackConeIsLimitOfMap (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
    (hc : IsLimit ((D.mapGlueData F).vPullbackCone i j)) : IsLimit (D.vPullbackCone i j) := by
  apply isLimitOfReflects F
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
      cospan ((D.mapGlueData F).ι i) ((D.mapGlueData F).ι j) :=
    NatIso.ofComponents
      (fun x => by
        cases x
        exacts [D.gluedIso F, Iso.refl _])
      (by rintro (_ | _) (_ | _) (_ | _ | _) <;> simp)
  apply IsLimit.postcomposeHomEquiv e _ _
  apply hc.ofIsoLimit
  refine Cone.ext (Iso.refl _) ?_
  rintro (_ | _ | _)
  all_goals simp [e]; rfl

/-- If there is a forgetful functor into `Type` that preserves enough (co)limits, then `D.ι` will
be jointly surjective. -/
theorem ι_jointly_surjective (F : C ⥤ Type v) [PreservesColimit D.diagram.multispan F]
    [∀ i j k : D.J, PreservesLimit (cospan (D.f i j) (D.f i k)) F] (x : F.obj D.glued) :
    ∃ (i : _) (y : F.obj (D.U i)), F.map (D.ι i) y = x := by
  let e := D.gluedIso F
  obtain ⟨i, y, eq⟩ := (D.mapGlueData F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv eq
  change ((D.mapGlueData F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id, D.ι_gluedIso_inv] at eq
  exact ⟨i, y, eq⟩

end GlueData

section GlueData'

/--
This is a variant of `GlueData` that only requires conditions on `V (i, j)` when `i ≠ j`.
See `GlueData.ofGlueData'`
-/
structure GlueData' where
  /-- Indexing type of a glue data. -/
  J : Type v
  /-- Objects of a glue data to be glued. -/
  U : J → C
  /-- Objects representing the intersections. -/
  V : ∀ (i j : J), i ≠ j → C
  /-- The inclusion maps of the intersection into the object. -/
  f : ∀ i j h, V i j h ⟶ U i
  f_mono : ∀ i j h, Mono (f i j h) := by infer_instance
  f_hasPullback : ∀ i j k hij hik, HasPullback (f i j hij) (f i k hik) := by infer_instance
  /-- The transition maps between the intersections. -/
  t : ∀ i j h, V i j h ⟶ V j i h.symm
  /-- The transition maps between the intersection of intersections. -/
  t' : ∀ i j k hij hik hjk,
    pullback (f i j hij) (f i k hik) ⟶ pullback (f j k hjk) (f j i hij.symm)
  t_fac : ∀ i j k hij hik hjk, t' i j k hij hik hjk ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ t i j hij
  t_inv : ∀ i j hij, t i j hij ≫ t j i hij.symm = 𝟙 _
  cocycle : ∀ i j k hij hik hjk, t' i j k hij hik hjk ≫
    t' j k i hjk hij.symm hik.symm ≫ t' k i j hik.symm hjk.symm hij = 𝟙 _

attribute [local instance] GlueData'.f_mono GlueData'.f_hasPullback

attribute [reassoc (attr := simp)] GlueData'.t_inv GlueData'.cocycle

variable {C}

open scoped Classical in
/-- (Implementation detail) the constructed `GlueData.f` from a `GlueData'`. -/
abbrev GlueData'.f' (D : GlueData' C) (i j : D.J) :
    (if h : i = j then D.U i else D.V i j h) ⟶ D.U i :=
  if h : i = j then eqToHom (dif_pos h) else eqToHom (dif_neg h) ≫ D.f i j h

instance (D : GlueData' C) (i j : D.J) :
    Mono (D.f' i j) := by dsimp [GlueData'.f']; split_ifs <;> infer_instance

instance (D : GlueData' C) (i : D.J) :
    IsIso (D.f' i i) := by simp only [GlueData'.f', ↓reduceDIte]; infer_instance

instance (D : GlueData' C) (i j k : D.J) :
    HasPullback (D.f' i j) (D.f' i k) := by
  if hij : i = j then
    apply +allowSynthFailures hasPullback_of_left_iso
    simp only [GlueData'.f', dif_pos hij]
    infer_instance
  else if hik : i = k then
    apply +allowSynthFailures hasPullback_of_right_iso
    simp only [GlueData'.f', dif_pos hik]
    infer_instance
  else
    have {X Y Z : C} (f : X ⟶ Y) (e : Z = X) : eqToHom e ≫ f ≍ f := by subst e; simp
    convert D.f_hasPullback i j k hij hik <;> simp [GlueData'.f', hij, hik, this]

open scoped Classical in
/-- (Implementation detail) the constructed `GlueData.t'` from a `GlueData'`. -/
def GlueData'.t'' (D : GlueData' C) (i j k : D.J) :
    pullback (D.f' i j) (D.f' i k) ⟶ pullback (D.f' j k) (D.f' j i) :=
  if hij : i = j then
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by aesop))
        (by aesop) (by aesop)
  else if hik : i = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      subst hik; infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else if hjk : j = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      apply +allowSynthFailures pullback_snd_iso_of_left_iso
      simp only [hjk, GlueData'.f', ↓reduceDIte]
      infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else
    haveI := Ne.symm hij
    pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by rw [dif_neg hik]))
        (eqToHom (by simp)) (by delta f'; aesop) (by delta f'; aesop) ≫
      D.t' i j k hij hik hjk ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by simp))
        (by delta f'; aesop) (by delta f'; aesop)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
The constructed `GlueData` of a `GlueData'`, where `GlueData'` is a variant of `GlueData` that only
requires conditions on `V (i, j)` when `i ≠ j`.
-/
def GlueData.ofGlueData' (D : GlueData' C) : GlueData C where
  J := D.J
  U := D.U
  V ij := if h : ij.1 = ij.2 then D.U ij.1 else D.V ij.1 ij.2 h
  f i j := D.f' i j
  f_id i := by simp only [↓reduceDIte, GlueData'.f']; infer_instance
  t i j := if h : i = j then eqToHom (by simp [h]) else
    eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm
  t_id i := by simp
  t' := D.t''
  t_fac i j k := by
    delta GlueData'.t''
    obtain rfl | _ := eq_or_ne i j
    · simp
    obtain rfl | _ := eq_or_ne i k
    · simp [*]
    obtain rfl | _ := eq_or_ne j k
    · simp [*]
    · simp [*, reassoc_of% D.t_fac]
  cocycle i j k := by
    delta GlueData'.t''
    if hij : i = j then
      subst hij
      if hik : i = k then
        subst hik
        ext <;> simp
      else
        simp [hik, Ne.symm hik, fst_eq_snd_of_mono_eq]
    else if hik : i = k then
      subst hik
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq, pullback.condition_assoc]
    else if hjk : j = k then
      subst hjk
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq]
    else
      ext <;> simp [hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk,
        pullback.map_comp_assoc]

end GlueData'

end CategoryTheory
