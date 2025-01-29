import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

noncomputable section

universe v u
open CategoryTheory Limits

variable {X : Type v} [Preorder X] {C : Type u}
  [Category.{v} C] [HasLimits C]

variable (F : X ⥤ C)

open TopologicalSpace

variable (X)

def alexandrov : TopologicalSpace X where
  IsOpen S := ∀ ⦃x y : X⦄, x ∈ S → x ≤ y → y ∈ S
  isOpen_univ := fun _ _ _ _ => trivial
  isOpen_inter A B hA hB x y hx h :=
    ⟨hA hx.left h, hB hx.right h⟩
  isOpen_sUnion S hS x y hx h := by
    obtain ⟨T, hT, hx⟩ := hx
    refine ⟨T, hT, hS T hT hx h⟩

def Alexandrov : TopCat where
  α := X
  str := alexandrov X

namespace Alexandrov

variable {X}

lemma mem_of_le {U : Opens (Alexandrov X)}
    (x y : X) (h : x ≤ y) (hx : x ∈ U) :
    y ∈ U :=
  U.2 hx h

def principalOpen (x : X) : Opens (Alexandrov X) :=
  .mk { y | x ≤ y } <| fun _ _ h h' => le_trans h h'

lemma principalOpen_le {x y : X} (h : x ≤ y) : principalOpen y ≤ principalOpen x :=
  fun _ hc => le_trans h hc

lemma mem_principalOpen (x : X) : x ∈ principalOpen x := le_refl _

@[simp]
lemma principalOpen_le_iff {x : X} (U : Opens (Alexandrov X)) :
    principalOpen x ≤ U ↔ x ∈ U := by
  refine ⟨?_, ?_⟩
  · intro h
    apply h
    exact mem_principalOpen _
  · intro hx y hy
    exact mem_of_le _ _ hy hx

@[simps]
def principals : X ⥤ (Opens (Alexandrov X))ᵒᵖ where
  obj x := .op <| principalOpen x
  map {x y} f := .op <| principalOpen_le f.le |>.hom

lemma exists_le_of_le_sup {ι : Type v} {x : X}
    (Us : ι → Opens (Alexandrov X))
    (h : principalOpen x ≤ iSup Us) :
    ∃ i : ι, principalOpen x ≤ Us i := by
  have : x ∈ iSup Us := h <| mem_principalOpen x
  simp only [Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨i, ?_⟩
  simpa

open TopCat


abbrev ιι : Presheaf C (Alexandrov X) :=
  principals.pointwiseRightKanExtension F

def forget (U : Opens (Alexandrov X)) :
    StructuredArrow (.op U) principals ⥤ X :=
  StructuredArrow.proj (.op U) principals

@[simps]
def forgetiSup {ι : Type v} (Us : ι → Opens (Alexandrov X)) :
    StructuredArrow (.op <| iSup Us) principals ⥤ (FullSubcategory fun V => ∃ i, V ≤ Us i)ᵒᵖ where
  obj f := .op <| .mk (principalOpen f.right) <| exists_le_of_le_sup Us f.hom.unop.le
  map e := .op <| LE.le.hom <| principalOpen_le <| e.right.le

variable {F} in
@[simps]
def lowerCone {α : Type v} (Us : α → Opens (Alexandrov X))
  (S : Cone ((fullSubcategoryInclusion fun V => ∃ i, V ≤ Us i).op ⋙ ιι F)) :
    Cone (forget (iSup Us) ⋙ F) where
  pt := S.pt
  π := {
    app := fun f =>
      S.π.app ((forgetiSup Us).obj f) ≫
      limit.π (StructuredArrow.proj (Opposite.op <| principalOpen f.right) principals ⋙ F)
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
      let xx : StructuredArrow (Opposite.op (principalOpen x.right)) principals :=
        ⟨.mk .unit, x.right, 𝟙 _⟩
      let yy : StructuredArrow (Opposite.op (principalOpen x.right)) principals :=
        ⟨.mk .unit, y.right, .op <| LE.le.hom <| principalOpen_le e.right.le⟩
      let ee : xx ⟶ yy := { left := 𝟙 _, right := e.right }
      exact limit.w
        (StructuredArrow.proj (Opposite.op (principalOpen x.right)) principals ⋙ F) ee |>.symm
  }

open Presheaf Functor SheafCondition
def isLimit (α : Type v) (Us : α → Opens (Alexandrov X)) :
    IsLimit (mapCone (ιι F) (SheafCondition.opensLeCoverCocone Us).op) where
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

theorem is_sheaf_ιι : (ιι F).IsSheaf := by
  rw [isSheaf_iff_isSheafOpensLeCover]
  intro ι Us
  constructor
  apply isLimit

theorem is_sheaf_of_is_Kan_extension
    (P : (Opens (Alexandrov X))ᵒᵖ ⥤ C)
    (η : principals ⋙ P ⟶ F)
    [P.IsRightKanExtension η] :
    IsSheaf P := by
  let γ : principals ⋙ ιι F ⟶ F := principals.pointwiseRightKanExtensionCounit F
  let h2 : (ιι F).IsRightKanExtension γ := inferInstance
  have : P ≅ ιι F := @rightKanExtensionUnique _ _ _ _ _ _ _ _ _ _ (by assumption) _ _ h2
  rw [isSheaf_iso_iff this]
  exact is_sheaf_ιι F

end Alexandrov
