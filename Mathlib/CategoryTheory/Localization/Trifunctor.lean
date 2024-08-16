import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Functor.Trifunctor
import Mathlib.CategoryTheory.Products.Associator

namespace CategoryTheory

section

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₄] [Category C₁₂] [Category C₂₃]

variable (C₁ C₂ C₃) in
def whiskeringRight₃Obj {D : Type*} [Category D]
    (F : C₄ ⥤ D) : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ D) :=
  (whiskeringRight C₁ _ _).obj ((whiskeringRight C₂ _ _).obj ((whiskeringRight C₃ _ _).obj F))

@[simps! obj map_app_app_app]
def bifunctorComp₁₂FunctorObj (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) :
    (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) where
  obj G := bifunctorComp₁₂ F₁₂ G
  map {G G'} φ :=
    { app := fun X₁ ↦
        { app := fun X₂ ↦
            { app := fun X₃ ↦ (φ.app ((F₁₂.obj X₁).obj X₂)).app X₃ }
          naturality := fun X₂ Y₂ f ↦ by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality] }
      naturality := fun X₁ Y₁ f ↦ by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }

@[simps]
def bifunctorComp₁₂FunctorMap {F₁₂ F₁₂' : C₁ ⥤ C₂ ⥤ C₁₂} (φ : F₁₂ ⟶ F₁₂') :
  bifunctorComp₁₂FunctorObj (C₃ := C₃) (C₄ := C₄) F₁₂ ⟶ bifunctorComp₁₂FunctorObj F₁₂' where
  app := fun G ↦
    { app := fun X₁ ↦
        { app := fun X₂ ↦
            { app := fun X₃ ↦ (G.map ((φ.app X₁).app X₂)).app X₃
               }
          naturality := fun X₂ Y₂ f ↦ by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
      naturality := fun X₁ Y₁ f ↦ by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
  naturality := fun G G' f ↦ by
    ext X₁ X₂ X₃
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

@[simps]
def bifunctorComp₁₂Functor : (C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) where
  obj := bifunctorComp₁₂FunctorObj
  map := bifunctorComp₁₂FunctorMap

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

def bifunctorComp₁₂Iso : bifunctorComp₁₂ F₁₂ G ≅ curry.obj (uncurry.obj F₁₂ ⋙ G) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)

def bifunctorComp₂₃Iso : bifunctorComp₂₃ F G₂₃ ≅
    curry.obj (curry.obj (prod.associator _ _ _ ⋙ uncurry.obj (uncurry.obj G₂₃ ⋙ F.flip).flip)) :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦
    NatIso.ofComponents (fun _ ↦ Iso.refl _)))

end

variable {C₁ C₂ C₃ E : Type*} [Category C₁] [Category C₂] [Category C₃] [Category E]

@[reassoc (attr := simp)]
lemma Iso.hom_inv_id_app_app_app {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ E} (e : F ≅ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    ((e.hom.app X₁).app X₂).app X₃ ≫ ((e.inv.app X₁).app X₂).app X₃ = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, Iso.hom_inv_id_app,
    NatTrans.id_app, NatTrans.id_app]

@[reassoc (attr := simp)]
lemma Iso.inv_hom_id_app_app_app {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ E} (e : F ≅ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    ((e.inv.app X₁).app X₂).app X₃ ≫ ((e.hom.app X₁).app X₂).app X₃ = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, Iso.inv_hom_id_app,
    NatTrans.id_app, NatTrans.id_app]

def currying₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ≌ (C₁ × C₂ × C₃ ⥤ E) :=
  currying.trans (currying.trans (prod.associativity C₁ C₂ C₃).congrLeft)

abbrev uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ × C₂ × C₃ ⥤ E) := currying₃.functor
abbrev curry₃ : (C₁ × C₂ × C₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) := currying₃.inverse

def fullyFaithfulUncurry₃ :
    (uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ × C₂ × C₃ ⥤ E)).FullyFaithful :=
  currying₃.fullyFaithfulFunctor

@[simp]
lemma curry₃_obj_map_app_app (F : C₁ × C₂ × C₃ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.inverse.obj F).map f).app X₂).app X₃ = F.map ⟨f, 𝟙 X₂, 𝟙 X₃⟩ := rfl

@[simp]
lemma curry₃_obj_obj_map_app (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) :
    (((currying₃.inverse.obj F).obj X₁).map f).app X₃ = F.map ⟨𝟙 X₁, f, 𝟙 X₃⟩ := rfl

@[simp]
lemma curry₃_obj_obj_obj_map (F : C₁ × C₂ × C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) :
    (((currying₃.inverse.obj F).obj X₁).obj X₂).map f = F.map ⟨𝟙 X₁, 𝟙 X₂, f⟩ := rfl

@[simp]
lemma curry₃_map_app_app_app {F G : C₁ × C₂ × C₃ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.inverse.map f).app X₁).app X₂).app X₃ = f.app ⟨X₁, X₂, X₃⟩ := rfl

@[simp]
lemma currying₃_unitIso_hom_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.hom.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃]

@[simp]
lemma currying₃_unitIso_inv_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((currying₃.unitIso.inv.app F).app X₁).app X₂).app X₃ = 𝟙 _ := by
  simp [currying₃]

namespace MorphismProperty

def IsInvertedBy₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : Prop :=
  (W₁.prod (W₂.prod W₃)).IsInvertedBy (currying₃.functor.obj F)

end MorphismProperty

variable {D₁ D₂ D₃ : Type*} [Category D₁] [Category D₂] [Category D₃]

@[simps!]
def whiskeringLeft₃ObjObjObj (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (E : Type*) [Category E] :
    (D₁ ⥤ D₂ ⥤ D₃ ⥤ E) ⥤ (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) :=
  (whiskeringRight _ _ _).obj (whiskeringLeft₂ObjObj F₂ F₃ E) ⋙ (whiskeringLeft C₁ D₁ _).obj F₁

@[simps!]
def curry₃ObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃) (G : D₁ × D₂ × D₃ ⥤ E) :
    curry₃.obj (F₁.prod (F₂.prod F₃) ⋙ G) ≅
      F₁ ⋙ curry₃.obj G ⋙ whiskeringLeft₂ObjObj F₂ F₃ E :=
  NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents
      (fun X₂ ↦ NatIso.ofComponents (fun X₃ ↦ Iso.refl _)))

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)

class Lifting₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) where
  iso': (whiskeringLeft₃ObjObjObj L₁ L₂ L₃ E).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F']

noncomputable def Lifting₃.iso : (whiskeringLeft₃ObjObjObj L₁ L₂ L₃ E).obj F' ≅ F :=
  Lifting₃.iso' W₁ W₂ W₃

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)

noncomputable instance Lifting₃.uncurry [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F'] :
    Lifting (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))
      (uncurry₃.obj F) (uncurry₃.obj F') where
  iso' := uncurry₃.mapIso (Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F F')

end

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}
  (hF : MorphismProperty.IsInvertedBy₃ W₁ W₂ W₃ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

noncomputable def lift₃ : D₁ ⥤ D₂ ⥤ D₃ ⥤ E :=
  curry₃.obj (lift (uncurry₃.obj F) hF (L₁.prod (L₂.prod L₃)))

noncomputable instance : Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F (lift₃ F hF L₁ L₂ L₃) where
  iso' :=
    (curry₃ObjProdComp L₁ L₂ L₃ _).symm ≪≫
      curry₃.mapIso (fac (uncurry₃.obj F) hF (L₁.prod (L₂.prod L₃))) ≪≫
        currying₃.unitIso.symm.app F

end

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)
  [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁'] [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂'] (τ : F₁ ⟶ F₂)
  (e : F₁ ≅ F₂)

noncomputable def lift₃NatTrans : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry₃.preimage
    (liftNatTrans (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃)) (uncurry₃.obj F₁)
      (uncurry₃.obj F₂) (uncurry₃.obj F₁') (uncurry₃.obj F₂') (uncurry₃.map τ))

@[simp]
theorem lift₃NatTrans_app_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₂ F₁' F₂' τ).app
        (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃) =
      (((Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁').hom.app X₁).app X₂).app X₃ ≫
        ((τ.app X₁).app X₂).app X₃ ≫
        (((Lifting₃.iso L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂').inv.app X₁).app X₂).app X₃ := by
  dsimp [lift₃NatTrans, fullyFaithfulUncurry₃, Equivalence.fullyFaithfulFunctor]
  simp only [currying₃_unitIso_hom_app_app_app_app, Functor.id_obj,
    currying₃_unitIso_inv_app_app_app_app, Functor.comp_obj,
    Category.comp_id, Category.id_comp]
  exact liftNatTrans_app _ _ _ _ (uncurry₃.obj F₁') (uncurry₃.obj F₂') (uncurry₃.map τ) ⟨X₁, X₂, X₃⟩

variable {F₁' F₂'} in
include W₁ W₂ W₃ in
theorem natTrans₃_ext {τ τ' : F₁' ⟶ F₂'}
    (h : ∀ (X₁ : C₁) (X₂ : C₂) (X₃ : C₃), ((τ.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃) =
      ((τ'.app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃)) : τ = τ' :=
  uncurry₃.map_injective (natTrans_ext (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))
    (fun _ ↦ h _ _ _))

noncomputable def lift₃NatIso : F₁' ≅ F₂' where
  hom := lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₂ F₁' F₂' e.hom
  inv := lift₃NatTrans L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₁ F₂' F₁' e.inv
  hom_inv_id := natTrans₃_ext L₁ L₂ L₃ W₁ W₂ W₃ (by aesop_cat)
  inv_hom_id := natTrans₃_ext L₁ L₂ L₃ W₁ W₂ W₃ (by aesop_cat)

end

section

variable {C₁ C₂ C₃ C₁₂ C : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₁₂] [Category C]
  {D₁ D₂ D₃ D₁₂ D₂₃ D : Type*} [Category D₁] [Category D₂] [Category D₃]
  [Category D₁₂] [Category D]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃) (L₁₂ : C₁₂ ⥤ D₁₂) (L : C ⥤ D)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (W₁₂ : MorphismProperty C₁₂) (W : MorphismProperty C)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [L₁₂.IsLocalization W₁₂] [L.IsLocalization W]
  (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C)
  (F₁₂' : D₁ ⥤ D₂ ⥤ D₁₂) (G' : D₁₂ ⥤ D₃ ⥤ D)
  [Lifting₂ L₁ L₂ W₁ W₂ (F₁₂ ⋙ (whiskeringRight _ _ _).obj L₁₂) F₁₂']
  [Lifting₂ L₁₂ L₃ W₁₂ W₃ (G ⋙ (whiskeringRight _ _ _).obj L) G']

noncomputable nonrec def Lifting₃.bifunctorComp₁₂ :
    Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃
      ((whiskeringRight₃Obj C₁ C₂ C₃ L).obj (bifunctorComp₁₂ F₁₂ G))
      (bifunctorComp₁₂ F₁₂' G') where
  iso' :=
    ((whiskeringRight C₁ _ _).obj
      ((whiskeringRight C₂ _ _).obj ((whiskeringLeft _ _ D).obj L₃))).mapIso
        ((bifunctorComp₁₂Functor.mapIso
          (Lifting₂.iso L₁ L₂ W₁ W₂ (F₁₂ ⋙ (whiskeringRight _ _ _).obj L₁₂) F₁₂')).app G') ≪≫
        (bifunctorComp₁₂Functor.obj F₁₂).mapIso
          (Lifting₂.iso L₁₂ L₃ W₁₂ W₃ (G ⋙ (whiskeringRight _ _ _).obj L) G')

end

end Localization

end CategoryTheory
