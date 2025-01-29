import Mathlib

noncomputable section

universe v u
open CategoryTheory Limits

namespace Alexandrov

variable
  {X : Type v} [TopologicalSpace X] [Preorder X] [Topology.IsUpperSet X]
  {C : Type u} [Category.{v} C] [HasLimits C]
  (F : X ⥤ C)

open TopologicalSpace Topology

def principalOpen (x : X) : Opens X :=
  .mk { y | x ≤ y } <| by
    rw [IsUpperSet.isOpen_iff_isUpperSet]
    intro y z h1 h2
    exact le_trans h2 h1

lemma principalOpen_le {x y : X} (h : x ≤ y) :
    principalOpen y ≤ principalOpen x :=
  fun _ hc => le_trans h hc

lemma self_mem_principalOpen (x : X) : x ∈ principalOpen x := le_refl _

@[simp]
lemma principalOpen_le_iff {x : X} (U : Opens X) :
    principalOpen x ≤ U ↔ x ∈ U := by
  refine ⟨?_, ?_⟩
  · intro h
    apply h
    exact self_mem_principalOpen _
  · intro hx y hy
    have := U.2
    rw [IsUpperSet.isOpen_iff_isUpperSet] at this
    apply this hy hx

variable (X) in
@[simps]
def principals : X ⥤ (Opens X)ᵒᵖ where
  obj x := .op <| principalOpen x
  map {x y} f := .op <| principalOpen_le f.le |>.hom

lemma exists_le_of_le_sup
    {ι : Type v}
    {x : X}
    (Us : ι → Opens X)
    (h : principalOpen x ≤ iSup Us) :
    ∃ i : ι, principalOpen x ≤ Us i := by
  have : x ∈ iSup Us := h <| self_mem_principalOpen x
  simp only [Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨i, ?_⟩
  simpa

open TopCat

abbrev ιι : (Opens X)ᵒᵖ ⥤ C :=
  (principals X).pointwiseRightKanExtension F

def forget (U : Opens X) :
    StructuredArrow (.op U) (principals X) ⥤ X :=
  StructuredArrow.proj (.op U) (principals X)

@[simps]
def forgetiSup {ι : Type v} (Us : ι → Opens X) :
    StructuredArrow (.op <| iSup Us) (principals X) ⥤
      (FullSubcategory fun V => ∃ i, V ≤ Us i)ᵒᵖ where
  obj f := .op <| .mk (principalOpen f.right) <| exists_le_of_le_sup Us f.hom.unop.le
  map e := .op <| LE.le.hom <| principalOpen_le <| e.right.le

variable {F} in
@[simps]
def lowerCone {α : Type v} (Us : α → Opens X)
  (S : Cone ((fullSubcategoryInclusion fun V => ∃ i, V ≤ Us i).op ⋙ ιι F)) :
    Cone (forget (iSup Us) ⋙ F) where
  pt := S.pt
  π := {
    app := fun f =>
      S.π.app ((forgetiSup Us).obj f) ≫
      limit.π (StructuredArrow.proj (Opposite.op <| principalOpen f.right) (principals X) ⋙ F)
        ⟨.mk .unit, f.right, 𝟙 _⟩
    naturality := by
      rintro x y e
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, principals_obj,
        Functor.op_obj, fullSubcategoryInclusion.obj, Functor.pointwiseRightKanExtension_obj,
        Category.id_comp, Functor.comp_map, Category.assoc]
      rw [← S.w ((forgetiSup Us).map e), Category.assoc]
      congr 1
      simp only [forgetiSup_obj, Functor.comp_obj, Functor.op_obj, fullSubcategoryInclusion.obj,
        Functor.pointwiseRightKanExtension_obj, forgetiSup_map, homOfLE_leOfHom, Functor.comp_map,
        Functor.op_map, Quiver.Hom.unop_op, fullSubcategoryInclusion.map,
        Functor.pointwiseRightKanExtension_map, limit.lift_π]
      let xx : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
        ⟨.mk .unit, x.right, 𝟙 _⟩
      let yy : StructuredArrow (Opposite.op (principalOpen x.right)) (principals X) :=
        ⟨.mk .unit, y.right, .op <| LE.le.hom <| principalOpen_le e.right.le⟩
      let ee : xx ⟶ yy := { left := 𝟙 _, right := e.right }
      exact limit.w
        (StructuredArrow.proj (Opposite.op (principalOpen x.right)) (principals X) ⋙ F) ee
        |>.symm
  }

open Presheaf Functor SheafCondition
def isLimit {X : TopCat.{v}} [Preorder X] [Topology.IsUpperSet X]
    (F : X ⥤ C)
    (α : Type v) (Us : α → Opens X) :
    IsLimit (mapCone (ιι F) (opensLeCoverCocone Us).op) where
  lift S := limit.lift _ (lowerCone Us S)
  fac := by
    rintro S ⟨V, i, hV⟩
    dsimp [forget, opensLeCoverCocone]
    ext ⟨_, x, f⟩
    simp only [comp_obj, StructuredArrow.proj_obj, Category.assoc, limit.lift_π, lowerCone_pt,
      lowerCone_π_app, const_obj_obj, forgetiSup_obj, StructuredArrow.map_obj_right, op_obj,
      fullSubcategoryInclusion.obj, pointwiseRightKanExtension_obj]
    have e : principalOpen x ≤ V := f.unop.le
    let VV : (FullSubcategory fun V => ∃ i, V ≤ Us i) := ⟨V, i, hV⟩
    let xx : (FullSubcategory fun V => ∃ i, V ≤ Us i) := ⟨principalOpen x, i, le_trans e hV⟩
    let ee : xx ⟶ VV := e.hom
    rw [← S.w ee.op, Category.assoc]
    congr 1
    simp only [comp_obj, op_obj, fullSubcategoryInclusion.obj, pointwiseRightKanExtension_obj,
      Functor.comp_map, op_map, Quiver.Hom.unop_op, fullSubcategoryInclusion.map,
      pointwiseRightKanExtension_map, limit.lift_π, xx, VV]
    congr
  uniq := by
    intro S m hm
    dsimp
    symm
    ext ⟨_, x, f⟩
    simp only [lowerCone_pt, comp_obj, limit.lift_π, lowerCone_π_app, const_obj_obj, forgetiSup_obj,
      op_obj, fullSubcategoryInclusion.obj, pointwiseRightKanExtension_obj]
    specialize hm ⟨principalOpen x, ?_⟩
    · apply exists_le_of_le_sup
      exact f.unop.le
    · rw [← hm]
      simp only [mapCone_pt, Cocone.op_pt, pointwiseRightKanExtension_obj, principals_obj,
        const_obj_obj, comp_obj, op_obj, fullSubcategoryInclusion.obj, mapCone_π_app, Cocone.op_π,
        NatTrans.op_app, pointwiseRightKanExtension_map, Category.assoc, limit.lift_π]
      congr

theorem is_sheaf_ιι {X : TopCat.{v}} [Preorder X] [Topology.IsUpperSet X] (F : X ⥤ C) :
    Presheaf.IsSheaf (ιι F) := by
  rw [isSheaf_iff_isSheafOpensLeCover]
  intro ι Us
  constructor
  apply isLimit

theorem is_sheaf_of_is_Kan_extension
    (P : (Opens X)ᵒᵖ ⥤ C)
    (η : principals X ⋙ P ⟶ F)
    [P.IsRightKanExtension η] :
    IsSheaf (X := TopCat.of X) P := by
  let γ : principals X ⋙ ιι F ⟶ F := (principals X).pointwiseRightKanExtensionCounit F
  let h2 : (ιι F).IsRightKanExtension γ := inferInstance
  have : P ≅ ιι F := @rightKanExtensionUnique _ _ _ _ _ _ _ _ _ _ (by assumption) _ _ h2
  rw [isSheaf_iso_iff this]
  let _ : Preorder (TopCat.of X) := inferInstanceAs <| Preorder X
  have _ : Topology.IsUpperSet (TopCat.of X) := inferInstanceAs <| Topology.IsUpperSet X
  exact is_sheaf_ιι (X := TopCat.of X) F

end Alexandrov
