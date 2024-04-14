import Mathlib.Condensed.Discrete.LocallyConstant
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.AsLimit

universe u

noncomputable section

open CategoryTheory Functor Limits Condensed FintypeCat StructuredArrow

attribute [local instance] FintypeCat.discreteTopology

namespace Condensed

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (F : I ⥤ FintypeCat.{u})
    (c : Cone <| F ⋙ toProfinite) (hc : IsLimit c)

namespace ToStructuredArrow

@[simps]
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)
  map_id _ := by
    simp only [CategoryTheory.Functor.map_id, hom_eq_iff, mk_right, homMk_right, id_right]
  map_comp _ _ := by simp only [Functor.map_comp, hom_eq_iff, mk_right, homMk_right, comp_right]

def functorIso : functor F c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

def functorOp : Iᵒᵖ ⥤ CostructuredArrow toProfinite.op ⟨c.pt⟩ :=
  (functor F c).op ⋙ toCostructuredArrow _ _

def functorOpIso : functorOp F c ⋙ CostructuredArrow.proj toProfinite.op ⟨c.pt⟩ ≅ F.op := Iso.refl _

-- TODO: PR
instance : Faithful toProfinite where
  map_injective h := funext fun _ ↦ (DFunLike.ext_iff.mp h) _

-- TODO: PR
instance : Full toProfinite where
  preimage f := fun x ↦ f x
  witness _ := rfl

theorem functor_initial [∀ i, Epi (c.π.app i)] : Initial (functor F c) := by
  rw [initial_iff_of_isCofiltered (F := functor F c)]
  constructor
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩
    have : DiscreteTopology (toProfinite.obj X) := by
      simp only [toProfinite, Profinite.of]
      infer_instance
    let f' : LocallyConstant c.pt (toProfinite.obj X) := ⟨f, by
      rw [IsLocallyConstant.iff_continuous]
      exact f.continuous⟩
    obtain ⟨i, g, h⟩ := Profinite.exists_locallyConstant.{_, u, u} c hc f'
    refine ⟨i, ⟨homMk g.toFun ?_⟩⟩
    ext x
    have := (LocallyConstant.congr_fun h x).symm
    erw [LocallyConstant.coe_comap_apply _ _ (c.π.app i).continuous] at this
    exact this
  · intro ⟨_, X, (f : c.pt ⟶ _)⟩ i ⟨_, (s : F.obj i ⟶ X), (w : f = c.π.app i ≫ _)⟩
      ⟨_, (s' : F.obj i ⟶ X), (w' : f = c.π.app i ≫ _)⟩
    simp only [functor_obj, functor_map, hom_eq_iff, mk_right, comp_right, homMk_right]
    refine ⟨i, 𝟙 _, ?_⟩
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [w] at w'
    exact toProfinite.map_injective <| Epi.left_cancellation _ _ w'

theorem functorOp_final [∀ i, Epi (c.π.app i)] : Final (functorOp F c) := by
  have := functor_initial F c hc
  have : IsEquivalence ((toCostructuredArrow toProfinite c.pt)) :=
    (inferInstance : IsEquivalence (structuredArrowOpEquivalence _ _).functor)
  exact Functor.final_comp (functor F c).op _

end Condensed.ToStructuredArrow

@[simps!]
def lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (lan toProfinite.op).obj (toProfinite.op ⋙ F)

namespace Condensed.ColimitLocallyConstant

variable (S : Profinite.{u}) (X : Type (u+1))

def _root_.Profinite.proj (i : DiscreteQuotient S) : C(S, S.diagram.obj i) := by
  have : DiscreteTopology i := inferInstance
  refine ⟨i.proj, ?_⟩
  convert i.proj_continuous
  exact this.eq_bot.symm

@[simps]
def LC_cocone : Cocone (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) where
  pt := LocallyConstant S X
  ι := { app := fun i (f : LocallyConstant _ _) ↦ f.comap' (S.proj i.unop) }

@[simps]
def LC_cocone' : Cocone
    (Lan.diagram toProfinite.op (toProfinite.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨S⟩) where
  pt := LocallyConstant S X
  ι := {
    app := fun i (f : LocallyConstant _ _) ↦ f.comap' i.hom.unop
    naturality := by
      intro i j f
      simp only [LC, comp_obj, CostructuredArrow.proj_obj, op_obj, Opposite.unop_op,
        profiniteToCompHaus_obj, toProfinite_obj_toCompHaus_toTop_α, const_obj_obj,
        Functor.comp_map, CostructuredArrow.proj_map, op_map, Quiver.Hom.unop_op,
        profiniteToCompHaus_map, const_obj_map, Category.comp_id]
      ext
      have := f.w
      simp only [op_obj, const_obj_obj, op_map, CostructuredArrow.right_eq_id, const_obj_map,
        Category.comp_id] at this
      rw [← this]
      rfl }

example : LC_cocone S X =
  (LC_cocone' S X).whisker (ToStructuredArrow.functorOp S.fintypeDiagram S.asLimitCone) := rfl

def can :
    colimit (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟶ LocallyConstant S X :=
  colimit.desc (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) (LC_cocone S X)

def can' : colimit
    (Lan.diagram toProfinite.op (toProfinite.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨S⟩) ⟶
      LocallyConstant S X :=
  colimit.desc
    (Lan.diagram toProfinite.op (toProfinite.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨S⟩)
    (LC_cocone' S X)

theorem injective_can : Function.Injective (can S X) := by
  intro a' b' h
  obtain ⟨i, (a : LocallyConstant _ _), ha⟩ := Types.jointly_surjective' a'
  obtain ⟨j, (b :  LocallyConstant _ _), hb⟩ := Types.jointly_surjective' b'
  obtain ⟨k, ki, kj, _⟩ := (isFiltered_op_of_isCofiltered (DiscreteQuotient S)).cocone_objs i j
  rw [← ha, ← hb, Types.FilteredColimit.colimit_eq_iff]
  refine ⟨k, ki, kj, ?_⟩
  dsimp only [comp_obj, op_obj, Opposite.unop_op, profiniteToCompHaus_obj, LC_obj_obj,
    toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, op_map, Quiver.Hom.unop_op,
    profiniteToCompHaus_map, LC_obj_map]
  apply DFunLike.ext
  intro x'
  obtain ⟨x, hx⟩ := k.unop.proj_surjective x'
  rw [← hx]
  change a.toFun (i.unop.proj x) = b.toFun (j.unop.proj x)
  simp only [← ha, ← hb, can,
    ← types_comp_apply (colimit.ι _ i) (colimit.desc _ (LC_cocone S X)) a,
    ← types_comp_apply (colimit.ι _ j) (colimit.desc _ (LC_cocone S X)) b,
    colimit.ι_desc, LC_cocone_pt, LC_cocone_ι_app, LocallyConstant.comap', comp_obj,
    toProfinite_obj_toCompHaus_toTop_α, LocallyConstant.mk.injEq] at h
  exact congrFun h _

theorem surjective_can : Function.Surjective (can S X) := by
  intro f
  obtain ⟨j, g, hg⟩ := Profinite.exists_locallyConstant.{_, u, u} S.asLimitCone S.asLimit f
  refine ⟨colimit.ι (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨j⟩ g, ?_⟩
  rw [can, ← types_comp_apply (colimit.ι _ ⟨j⟩)
    (colimit.desc _ (LC_cocone S X)) _]
  simp only [colimit.ι_desc]
  rw [hg]
  simp only [LC_cocone_pt, LC_cocone_ι_app, comp_obj, toProfinite_obj_toCompHaus_toTop_α,
    const_obj_obj]
  apply DFunLike.ext
  intro x
  erw [LocallyConstant.coe_comap_apply _ _ (S.asLimitCone.π.app _).continuous]
  rfl

theorem bijective_can : Function.Bijective (can S X) :=
  ⟨injective_can _ _, surjective_can _ _⟩

def loc_const_iso_colimit :
    colimit (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ≅ LocallyConstant S X  :=
  Equiv.toIso (Equiv.ofBijective (can S X) (bijective_can S X))

def LC_iso_colimit :
    colimit ((Condensed.ToStructuredArrow.functorOp S.fintypeDiagram S.asLimitCone) ⋙
      ((CostructuredArrow.proj toProfinite.op ⟨S⟩) ⋙ toProfinite.op ⋙ profiniteToCompHaus.op ⋙
      LC.obj X)) ≅ (profiniteToCompHaus.op ⋙ LC.obj X).obj ⟨S⟩ :=
  loc_const_iso_colimit S X

instance (S : Profinite) (i : DiscreteQuotient S) : Epi (S.asLimitCone.π.app i) := by
  rw [Profinite.epi_iff_surjective]
  exact i.proj_surjective

instance (S : Profinite) : Initial <|
    Condensed.ToStructuredArrow.functor S.fintypeDiagram S.asLimitCone :=
  Condensed.ToStructuredArrow.functor_initial S.fintypeDiagram S.asLimitCone S.asLimit

example (S : Profinite) : Final <|
    (Condensed.ToStructuredArrow.functor S.fintypeDiagram S.asLimitCone).op := inferInstance

instance (S : Profinite) : Final <|
    Condensed.ToStructuredArrow.functorOp S.fintypeDiagram S.asLimitCone :=
  Condensed.ToStructuredArrow.functorOp_final S.fintypeDiagram S.asLimitCone S.asLimit

def LC_iso_colimit_lan :
    (lanPresheaf (profiniteToCompHaus.op ⋙ LC.obj X)).obj ⟨S⟩ ≅
    (profiniteToCompHaus.op ⋙ LC.obj X).obj ⟨S⟩ :=
  (Functor.Final.colimitIso
    (Condensed.ToStructuredArrow.functorOp S.fintypeDiagram S.asLimitCone) _).symm
    ≪≫ LC_iso_colimit S X

lemma LC_iso_colimit_lan_eq_desc :
    (LC_iso_colimit_lan S X).hom = ColimitLocallyConstant.can' S X := by
  simp only [lanPresheaf_obj, comp_obj, op_obj, profiniteToCompHaus_obj, LC_obj_obj,
    Opposite.unop_op, LC_iso_colimit_lan, Final.colimitIso, LC_iso_colimit,
    loc_const_iso_colimit, Equiv.ofBijective, can, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Equiv.toIso_hom, Equiv.coe_fn_mk, can', IsIso.inv_comp_eq, colimit.pre_desc]
  rfl

end Condensed.ColimitLocallyConstant

def lanPresheaf_iso_LC (X : Type (u+1)) :
    lanPresheaf (profiniteToCompHaus.op ⋙ LC.obj X) ≅ profiniteToCompHaus.op ⋙ LC.obj X := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (Condensed.ColimitLocallyConstant.LC_iso_colimit_lan S X)) ?_
  intro ⟨S⟩ ⟨T⟩ ⟨(f : T ⟶ S)⟩
  simp only [lanPresheaf_obj, comp_obj, op_obj, profiniteToCompHaus_obj, LC_obj_obj,
    Opposite.unop_op, Functor.comp_map, op_map, profiniteToCompHaus_map]
  rw [ColimitLocallyConstant.LC_iso_colimit_lan_eq_desc,
    ColimitLocallyConstant.LC_iso_colimit_lan_eq_desc]
  simp only [lanPresheaf, lan_obj_map, ColimitLocallyConstant.can', colimit.pre_desc]
  apply colimit.hom_ext
  intro j
  simp only [comp_obj, CostructuredArrow.proj_obj, CostructuredArrow.map_obj_left, op_obj,
    Opposite.unop_op, profiniteToCompHaus_obj, LC_obj_obj, toProfinite_obj_toCompHaus_toTop_α,
    ColimitLocallyConstant.LC_cocone', const_obj_obj, Cocone.whisker_pt, colimit.ι_desc,
    Cocone.whisker_ι, whiskerLeft_app, CostructuredArrow.map_obj_hom, unop_comp]
  have : colimit.ι (CostructuredArrow.map f.op ⋙ Lan.diagram toProfinite.op
      (toProfinite.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨T⟩) = colimit.ι
      (Lan.diagram toProfinite.op (toProfinite.op ⋙ profiniteToCompHaus.op ⋙ LC.obj X) ⟨S⟩) := rfl
  erw [this]
  simp only [colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj, op_obj, Opposite.unop_op,
    profiniteToCompHaus_obj, LC_obj_obj, toProfinite_obj_toCompHaus_toTop_α]
  rfl
