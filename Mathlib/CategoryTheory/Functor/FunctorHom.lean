import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Enriched.Basic

universe w v' v u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F G : C ⥤ D)

open MonoidalCategory

@[ext]
structure HomObj (A : C ⥤ Type w) where
  app (X : C) (a : A.obj X) : F.obj X ⟶ G.obj X
  naturality {X Y : C} (φ : X ⟶ Y) (a : A.obj X) :
    F.map φ ≫ app Y (A.map φ a) = app X a ≫ G.map φ := by aesop_cat

namespace HomObj

attribute [reassoc (attr := simp)] naturality

variable {F G} in
lemma congr_app {A : C ⥤ Type w} {f g : HomObj F G A} (h : f = g) (X : C)
    (a : A.obj X) : f.app X a = g.app X a := by subst h; rfl

@[simps]
def id (A : C ⥤ Type w) : HomObj F F A where
  app _ _ := 𝟙 _

variable {F G}

variable {A : C ⥤ Type w}

@[simps]
def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

/-- -/
@[simps]
def map (x : HomObj F G A) {A' : C ⥤ Type w} (f : A' ⟶ A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    dsimp
    rw [← x.naturality φ (f.app Δ a), FunctorToTypes.naturality _ _ f φ a]

@[simps]
def ofNatTrans (f : F ⟶ G) : HomObj F G A where
  app X _ := f.app X

end HomObj

/-- The contravariant functor taking `A : C ⥤ Type w` to `HomObj F G A`. -/
@[simps!]
def HomObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := HomObj F G A.unop
  map {A A'} f x := x.map f.unop

def functorHom : C ⥤ Type max v' v u := coyoneda.rightOp ⋙ HomObjFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (functorHom F G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext _ _ (by ext; apply h)

def functorHomEquiv (A : C ⥤ Type max u v v') : (A ⟶ functorHom F G) ≃ HomObj F G A where
  toFun φ :=
    { app := fun X a ↦ (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)
        dsimp [functorHom] at this
        aesop }
  invFun x :=
    { app := fun X a ↦ { app := fun Y f => x.app Y (A.map f a) }
      naturality := fun X Y f => by
        ext a Z φ
        dsimp only [types_comp_apply]
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))
  right_inv x := by aesop

variable {F G} in
@[simps]
def natTransEquiv : (F ⟶ G) ≃ (𝟙_ _ ⟶ functorHom F G) where
  toFun f := ⟨fun _ _ ↦ HomObj.ofNatTrans f, _⟩
  invFun f := ⟨fun X ↦ (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom] at this
    aesop ⟩
  left_inv _ := rfl
  right_inv f := by
    ext X a Y φ
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom] at this
    aesop

@[simp]
lemma natTransEquiv_app_app_apply (F G : C ⥤ D) (f : F ⟶ G)
    {X : C} {a : (𝟙_ (C ⥤ Type (max v' v u))).obj X} (Y : C) {φ : X ⟶ Y} :
    ((natTransEquiv f).app X a).app Y φ = f.app Y := rfl

@[simp]
lemma natTransEquiv_whiskerRight_functorHom_app (K L : C ⥤ D) (X : C) (f : K ⟶ K)
    (x : 𝟙_ _ ⊗ (K.functorHom L).obj X) :
    ((natTransEquiv f ▷ K.functorHom L).app X x) =
    (HomObj.ofNatTrans f, x.2) := rfl

@[simp]
lemma functorHom_whiskerLeft_natTransEquiv_app (K L : C ⥤ D) (X : C) (f : L ⟶ L)
    (x : (K.functorHom L).obj X ⊗ 𝟙_ _) :
    ((K.functorHom L ◁ natTransEquiv f).app X x) =
    (x.1, HomObj.ofNatTrans f) := rfl

@[simp]
lemma whiskerLeft_app_apply (K L M N : C ⥤ D)
    (g : L.functorHom M ⊗ M.functorHom N ⟶ L.functorHom N)
    {X : C} (a : (K.functorHom L ⊗ L.functorHom M ⊗ M.functorHom N).obj X) :
    (K.functorHom L ◁ g).app X a = ⟨a.1, g.app X a.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply (K L M N : C ⥤ D)
    (f : K.functorHom L ⊗ L.functorHom M ⟶ K.functorHom M)
    {X : C} (a : ((K.functorHom L ⊗ L.functorHom M) ⊗ M.functorHom N).obj X) :
    (f ▷  M.functorHom N).app X a = ⟨f.app X a.1, a.2⟩ := rfl

@[simp]
lemma associator_inv_apply (K L M N : C ⥤ D) {X : C}
    (x : ((K.functorHom L) ⊗ (L.functorHom M) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).inv x =
    ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

@[simp]
lemma associator_hom_apply (K L M N : C ⥤ D) {X : C}
    (x : ( ((K.functorHom L) ⊗ (L.functorHom M)) ⊗ (M.functorHom N)).obj X) :
    (α_ ((K.functorHom L).obj X) ((L.functorHom M).obj X) ((M.functorHom N).obj X)).hom x =
    ⟨x.1.1, x.1.2, x.2⟩ := rfl

noncomputable instance enrichedCategory : EnrichedCategory (C ⥤ Type max v' v u) (C ⥤ D) where
  Hom := functorHom
  id F := natTransEquiv (𝟙 F)
  comp F G H := { app := fun X ⟨f, g⟩ => f.comp g }

noncomputable def functorHomWhiskerRight {K K' : C ⥤ D} (f : K ⟶ K') (L : C ⥤ D) :
    (functorHom K' L) ⟶ (functorHom K L) :=
  (λ_ _).inv ≫ natTransEquiv f ▷ _ ≫ eComp (C ⥤ Type max v' v u) K K' L

@[simp]
lemma natTransEquiv_id {K : C ⥤ D} : natTransEquiv (𝟙 K) = eId (C ⥤ Type max v' v u) K := by aesop

@[simp]
lemma natTransEquiv_comp {K L M : C ⥤ D} (f : K ⟶ L) (g : L ⟶ M) :
    natTransEquiv (f ≫ g) = (λ_ _).inv ≫ (natTransEquiv f ⊗ natTransEquiv g) ≫
      eComp _ K L M := by aesop

@[simp]
lemma sHomWhiskerRight_id (K L : C ⥤ D) : functorHomWhiskerRight (𝟙 K) L = 𝟙 _ := by
  simp only [functorHomWhiskerRight, natTransEquiv_id]
  sorry

@[simp, reassoc]
lemma sHomWhiskerRight_comp {K K' K'' : C ⥤ D} (f : K ⟶ K') (f' : K' ⟶ K'') (L : C ⥤ D) :
    functorHomWhiskerRight (f ≫ f') L =
    functorHomWhiskerRight f' L ≫ functorHomWhiskerRight f L := by
  dsimp [functorHomWhiskerRight]
  sorry

/-- The morphism `sHom K L ⟶ sHom K L'` induced by a morphism `L ⟶ L'`. -/
noncomputable def functorHomWhiskerLeft (K : C ⥤ D) {L L' : C ⥤ D} (g : L ⟶ L') :
    functorHom K L ⟶ functorHom K L' :=
  (ρ_ _).inv ≫ _ ◁ natTransEquiv g ≫ eComp _ K L L'

  @[simp]
lemma sHomWhiskerLeft_id (K L : C ⥤ D) : functorHomWhiskerLeft K (𝟙 L) = 𝟙 _ := by
  simp [functorHomWhiskerLeft, natTransEquiv_id, e_id_comp]
  sorry

@[simp, reassoc]
lemma functorHomWhiskerLeft_comp (K : C ⥤ D) {L L' L'' : C ⥤ D} (g : L ⟶ L') (g' : L' ⟶ L'') :
    functorHomWhiskerLeft K (g ≫ g') =
    functorHomWhiskerLeft K g ≫ functorHomWhiskerLeft K g' := by
  dsimp [functorHomWhiskerLeft]
  simp only [natTransEquiv_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc, ← e_assoc]
  sorry

@[reassoc]
lemma functorHom_whisker_exchange {K K' L L' : C ⥤ D} (f : K ⟶ K') (g : L ⟶ L') :
    functorHomWhiskerLeft K' g ≫ functorHomWhiskerRight f L' =
      functorHomWhiskerRight f L ≫ functorHomWhiskerLeft K g :=
  ((ρ_ _).inv ≫ _ ◁ natTransEquiv g ≫ (λ_ _).inv ≫ natTransEquiv f ▷ _) ≫=
    (e_assoc _ K K' L L').symm

attribute [local simp] functorHom_whisker_exchange

variable (C D) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ SSet.{v}` which sends `K : Cᵒᵖ` and `L : C` to `sHom K.unop L`. -/
@[simps]
noncomputable def functorHomFunctor : (C ⥤ D)ᵒᵖ ⥤ (C ⥤ D) ⥤ (C ⥤ Type max v' v u) where
  obj K :=
    { obj := fun L => functorHom K.unop L
      map := fun φ => functorHomWhiskerLeft K.unop φ }
  map φ :=
    { app := fun L => functorHomWhiskerRight φ.unop L }

def HomObjEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G.HomObj H F) where
  toFun a := ⟨fun X y x ↦ a.app X (y, x), fun φ y ↦ by
    ext x
    erw [congr_fun (a.naturality φ) (y, x)]
    rfl ⟩
  invFun a := ⟨fun X ⟨x, y⟩ ↦ a.app X x y, fun X Y f ↦ by
    ext ⟨x, y⟩
    erw [congr_fun (a.naturality f x) y]
    rfl ⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

/-- The bijection between morphisms `F ⊗ G ⟶ H` and morphisms `F ⟶ G.ihom H`. -/
def prodHomEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (F ⟶ functorHom G H) :=
  (HomObjEquiv F G H).trans (Functor.functorHomEquiv G H F).symm

/-- `K⬝X : C ⥤ D` such that `[K⬝X, -] ≅ [K, [X, -]] ` -/
class Tensor (K : C ⥤ Type max v' v u) (X : C ⥤ D) where
  obj : C ⥤ D
  iso : (functorHomFunctor C D).obj (Opposite.op obj) ≅
    (functorHomFunctor C D).obj (Opposite.op X) ⋙ (functorHomFunctor C (Type max v' v u)).obj (Opposite.op K)
  α' : K ⟶ functorHom X obj
  fac (Y : C ⥤ D) : (prodHomEquiv _ _ _).symm (iso.hom.app Y) =
    _ ◁ α' ≫ (β_ _ _).hom ≫ eComp _ X obj Y
