import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.HasLimits

universe u v w

open CategoryTheory Limits Functor

section Constructions

variable {C : Type u} [Category.{u, u} C] {J : Type u} [SmallCategory J]

def D (X : Jᵒᵖ ⥤ C) (Y : C) : J ⥤ TypeMax.{u, u} where
  obj i := X.obj ⟨i⟩ ⟶ Y
  map {i j} f := by
    intro g
    show X.obj { unop := j }  ⟶ Y
    exact X.map ⟨f⟩ ≫ g
  map_id {i} := by
    ext (g : X.obj ⟨i⟩ ⟶ Y)
    show X.map (𝟙 ⟨i⟩) ≫ g = g
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp {i j k} f g := by
    ext (h : X.obj ⟨i⟩ ⟶ Y)
    show X.map (⟨g⟩ ≫ ⟨f⟩) ≫ h = X.map ⟨g⟩ ≫ (X.map ⟨f⟩ ≫ h)
    simp only [map_comp, Category.assoc]

@[simp]
lemma D_obj_eq (X : Jᵒᵖ ⥤ C) {Y : C} (i : J) : (D X Y).obj i = (X.obj ⟨i⟩ ⟶ Y) :=
  rfl

@[simp]
lemma D_map_eq (X : Jᵒᵖ ⥤ C) {Y : C} {i j : J} (u : i ⟶ j) (g : X.obj ⟨i⟩ ⟶ Y) :
    (D X Y).map u g = X.map ⟨u⟩ ≫ g :=
  rfl

def Dtrans (X : Jᵒᵖ ⥤ C) {Y Z : C} (f : Y ⟶ Z) : D X Y ⟶ D X Z where
  app i g := g ≫ f
  naturality i j u := by
    ext (g : X.obj ⟨i⟩ ⟶ Y)
    show (X.map ⟨u⟩ ≫ g) ≫ f = X.map ⟨u⟩ ≫ (g ≫ f)
    simp only [Category.assoc]

@[simp]
lemma Dtrans_app_eq (X : Jᵒᵖ ⥤ C) {Y Z : C} (f : Y ⟶ Z) (i : J) (g : (D X Y).obj i) :
    (Dtrans X f).app i g = g ≫ f :=
  rfl

@[simp]
lemma Dtrans_id_eq (X : Jᵒᵖ ⥤ C) (Y : C) : Dtrans X (𝟙 Y) = 𝟙 (D X Y) := by
  ext i (f : X.obj ⟨i⟩ ⟶ Y)
  show f ≫ 𝟙 Y = f
  simp only [Category.comp_id]

@[simp]
lemma Dtrans_comp_eq (X : Jᵒᵖ ⥤ C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
    Dtrans X (f ≫ g) = Dtrans X f ≫ Dtrans X g := by
  ext i (u : X.obj ⟨i⟩ ⟶ Y)
  show u ≫ (f ≫ g) = (u ≫ f) ≫  g
  simp only [Category.assoc]

@[simp]
lemma colimMapIdentity {J C : Type*} [Category C] [Category J] (F : J ⥤ C) [HasColimit F]
    : colimMap (𝟙 F) = 𝟙 (colimit F) := by
  aesop

@[simp]
lemma colimMapComp {J C : Type*} [Category C] [Category J] {F G H : J ⥤ C} [HasColimit F]
    [HasColimit G] [HasColimit H] (t : F ⟶ G) (s : G ⟶ H)
    : colimMap (t ≫ s) = colimMap t ≫ colimMap s := by
  aesop

noncomputable def h (X : Jᵒᵖ ⥤ C) : C ⥤ Type u where
  obj Y := colimit (D X Y)
  map {Y Z} f := by
    show colimit (D X Y) → colimit (D X Z)
    exact colim.map (Dtrans X f)
  map_id Y := by
    simp only [colim_map, Dtrans_id_eq, colimMapIdentity]
  map_comp {Y Z W} f g := by
    simp only [colim_map, Dtrans_comp_eq, colimMapComp]

@[simp]
lemma h_map_eq (X : Jᵒᵖ ⥤ C) {Y Z : C} (f : Y ⟶ Z) (i : J)
    (u : (X.obj ⟨i⟩ ⟶ Y)):
    (h X).map f (colimit.ι (D X Y) i u) = colimit.ι (D X Z) i (u ≫ f) := by
  show colim.map (Dtrans X f) (colimit.ι (D X Y) i u) = colimit.ι (D X Z) i (u ≫ f)
  simp

noncomputable def procoyonedaLemma [IsFiltered J] (X : Jᵒᵖ ⥤ C) (F : C ⥤ Type u) :
    (h X ⟶ F) ≃ limit (X ⋙ F) where
  toFun t := by
    refine Types.Limit.mk (X ⋙ F) ?_ ?_
    intro i
    exact t.app (X.obj i) (colimit.ι (D X (X.obj i)) i.unop (𝟙 (X.obj i)))
    intro i j u
    have := congrFun (t.naturality (X.map u)) (colimit.ι (D X (X.obj i)) i.unop (𝟙 (X.obj i)))
    simp
    simp at this
    rw [←this]
    have h : colimit.ι (D X (X.obj j)) i.unop (X.map u) = 
        colimit.ι (D X (X.obj j)) j.unop (𝟙 (X.obj j)) := by
      apply (Types.FilteredColimit.colimit_eq_iff (D X (X.obj j))).mpr
      use i.unop
      use (𝟙 i.unop)
      use u.unop
      simp only [D_obj_eq, D_map_eq, Category.comp_id]
      show X.map (𝟙 i) ≫ X.map u = X.map u
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [h]
  invFun s := {
    app := by
      intro Y
      let c : Cocone (D X Y) := {
        pt := F.obj Y
        ι := {
          app := by
            intro i (g : X.obj ⟨i⟩ ⟶ Y)
            simp
            exact F.map g (limit.π (X ⋙ F) ⟨i⟩ s)
          naturality := by
            intro i j u
            simp only [D_obj_eq, const_obj_obj, id_eq, const_obj_map, Category.comp_id]
            ext g
            simp only [types_comp_apply, D_map_eq, FunctorToTypes.map_comp_apply]
            rw [←Functor.comp_map X F ⟨u⟩, Types.Limit.w_apply']
        }
      }
      exact colimit.desc (D X Y) c
    naturality := by
      intro Y Z f
      ext g
      obtain ⟨i, y, h⟩ := Types.jointly_surjective' g
      rw [←h]
      simp
  }
  left_inv := by
    intro t
    ext Y g
    obtain ⟨i, (y : X.obj ⟨i⟩ ⟶ Y), h⟩ := Types.jointly_surjective' g
    simp only [←h, id_eq, Types.Colimit.ι_desc_apply', Types.Limit.π_mk]
    let h2 := congrFun (t.naturality y) (colimit.ι (D X (X.obj ⟨i⟩)) i (𝟙 (X.obj ⟨i⟩)))
    simp only [types_comp_apply, h_map_eq, Category.id_comp] at h2 
    rw [←h2]
  right_inv := by
    intro s
    apply Types.limit_ext (X ⋙ F) _ _
    simp

end Constructions

structure ProObject (C : Type u) [Category.{v, u} C] : Type _ where
  {J : Type w}
  [Jcategory : SmallCategory J]
  [Jfiltered : IsFiltered J]
  (X : Jᵒᵖ ⥤ C)

instance {C : Type u} [Category.{v, u} C] (X : ProObject C) : SmallCategory X.J := X.Jcategory

instance {C : Type u} [Category.{v, u} C] (X : ProObject C) : IsFiltered X.J := X.Jfiltered

noncomputable instance {C : Type u} [Category.{u, u} C] : Category (ProObject C) where
  Hom X Y := limit (Y.X ⋙ h X.X)
  id X := procoyonedaLemma X.X (h X.X) (𝟙 (h X.X))
  comp {X Y Z} f g := by
    let s : h Z.X ⟶ h Y.X := (procoyonedaLemma Z.X (h Y.X)).symm g
    let t : h Y.X ⟶ h X.X := (procoyonedaLemma Y.X (h X.X)).symm f
    exact procoyonedaLemma Z.X (h X.X) (s ≫ t)

lemma proObject_id_eq {C : Type u} [Category.{u, u} C] (X : ProObject C) :
    𝟙 X = procoyonedaLemma X.X (h X.X) (𝟙 (h X.X)) :=
  rfl

lemma proObject_id_comp {C : Type u} [Category.{u, u} C] {X Y Z : ProObject C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = procoyonedaLemma Z.X (h X.X)
      ((procoyonedaLemma Z.X (h Y.X)).symm g ≫ ((procoyonedaLemma Y.X (h X.X)).symm f)) :=
  rfl

class Procorepresentable {C : Type u} [Category.{u, u} C] (F : C ⥤ Type u) : Prop where
  has_procorepresentation : ∃ (X : ProObject C), Nonempty (h X.X ≅ F)

noncomputable def procoyonedaEmbedding (C : Type u) [Category.{u, u} C] :
    (ProObject C)ᵒᵖ ⥤ (C ⥤ Type u) where
  obj := fun ⟨X⟩ ↦ h X.X
  map := fun ⟨f⟩ => (procoyonedaLemma _ _).symm f
  map_id := fun ⟨X⟩ => by
    show (procoyonedaLemma X.X (h X.X)).symm (𝟙 X) = 𝟙 (h X.X)
    simp only [proObject_id_eq, Equiv.symm_apply_apply]
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    show (procoyonedaLemma X.X (h Z.X)).symm (g ≫ f) = (procoyonedaLemma X.X (h Y.X)).symm f ≫
        (procoyonedaLemma Y.X (h Z.X)).symm g
    simp only [proObject_id_comp, Equiv.symm_apply_apply]

noncomputable instance {C : Type u} [Category.{u, u} C] : Full (procoyonedaEmbedding C) where
  preimage := by
    intro ⟨Y⟩ ⟨X⟩ (f : h Y.X ⟶ h X.X)
    exact ⟨procoyonedaLemma _ _ f⟩
  witness := by
    intro ⟨Y⟩ ⟨X⟩ (f : h Y.X ⟶ h X.X)
    show (procoyonedaLemma _ _).symm (procoyonedaLemma _ _ f) = f
    simp only [Equiv.symm_apply_apply]

noncomputable instance {C : Type u} [Category.{u, u} C] : Faithful (procoyonedaEmbedding C) where
  map_injective := by
    intro ⟨Y⟩ ⟨X⟩ ⟨(f : X ⟶ Y)⟩ ⟨(g : X ⟶ Y)⟩
      (h : (procoyonedaLemma _ _).symm f = (procoyonedaLemma _ _).symm g)
    apply (Opposite.op_inj_iff f g).mpr
    exact Equiv.injective (procoyonedaLemma _ _).symm h

--instance representable_of_procorepresentable {C : Type u} [Category.{u, u} C]
--    (F : C ⥤ Type u) [Corepresentable F] : Procorepresentable F where
--  has_procorepresentation := sorry
