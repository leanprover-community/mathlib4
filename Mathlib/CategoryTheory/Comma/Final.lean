/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!

-/


namespace CategoryTheory

open CategoryTheory Limits Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

section ArbitraryUniverses

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

@[simps]
def canonicalFunctor' (b₀ : B) : CostructuredArrow L (R.obj b₀) ⥤ Comma L R where
  obj X := Comma.mk X.left b₀ X.hom
  map {X Y} f :=
    { left := f.left
      right := 𝟙 b₀ }

#check toCostructuredArrow

@[simps! obj map]
def canonicalFunctor (b₀ : B) :
    CostructuredArrow L (R.obj b₀) ⥤ CostructuredArrow (Comma.snd L R) b₀ :=
  Functor.toCostructuredArrow (canonicalFunctor' L R b₀) _ _ (fun _ => 𝟙 b₀) (by aesop_cat)

@[simps!]
def backToA (b₀ : B) : CostructuredArrow (Comma.snd L R) b₀ ⥤ A :=
  CostructuredArrow.proj _ _ ⋙ Comma.fst _ _

@[simps! obj map]
def backwards (b₀ : B) : CostructuredArrow (Comma.snd L R) b₀ ⥤ CostructuredArrow L (R.obj b₀) :=
  Functor.toCostructuredArrow (backToA L R b₀) _ _ (fun Y => Y.left.hom ≫ R.map Y.hom) fun f => by
    have := f.w
    dsimp at this ⊢
    rw [reassoc_of% f.left.w, ← R.map_comp, this, Category.comp_id]

def adjunction (b₀ : B) : backwards L R b₀ ⊣ canonicalFunctor L R b₀ := by
  refine' Adjunction.mkOfHomEquiv ⟨fun X Y => _, _, _⟩
  · dsimp
    refine' ⟨_, _, _, fun f => CostructuredArrow.hom_ext _ _ <| Comma.hom_ext _ _ _ _⟩
    · exact fun f => CostructuredArrow.homMk (CommaMorphism.mk f.left X.hom (by simp)) (by simp)
    · refine' fun f => CostructuredArrow.homMk f.left.left _
      have fw : f.left.right = X.hom := by simpa using f.w
      have flw : L.map f.left.left ≫ Y.hom = X.left.hom ≫ R.map f.left.right := by
        simpa using f.left.w
      simp [flw, fw]
    · aesop_cat
    · simp
    · simpa using f.w.symm
  · simp
  · aesop_cat

theorem cofinal_canonicalFunctor (b₀ : B) : Functor.Final (canonicalFunctor L R b₀) :=
  Functor.final_of_adjunction (adjunction L R b₀)

end ArbitraryUniverses

section SmallCategory
variable {C : Type (max u₁ v₁)} [Category.{v₁} C]
variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

-- noncomputable def bleb : B ⥤

noncomputable def bla (F : Comma L R ⥤ C) [HasColimits C] : B ⥤ C :=
  (lan (Comma.snd L R)).obj F

noncomputable def blubb [HasColimits C] (F : Comma L R ⥤ C) : B ⥤ C :=
  R ⋙ (lan L).obj (_ ⋙ F)

theorem innerFunctor_aux {C : Type*} [Category C] {D : Type*} [Category D] {I : Type*} [Category I]
  {G : I ⥤ C} {F : C ⥤ D} {X Y : I} (f : G.obj X ⟶ G.obj Y) {Z : D} (h : ∀ X, F.obj (G.obj X) ⟶ Z)
  (he : X = Y) (hf : f ≫ G.map (eqToHom he.symm) = 𝟙 _) : F.map f ≫ h _ = h _ := by
  cases he
  simp only [eqToHom_refl, map_id, Category.comp_id] at hf
  rw [hf]
  simp

@[simps]
noncomputable def innerFunctor (F : Comma L R ⥤ C) [HasColimits C] : B ⥤ C where
  obj b₀ := colimit (canonicalFunctor' L R b₀ ⋙ F)
  map {b b'} f := by
    refine ?_ ≫ colimit.pre (canonicalFunctor' L R _ ⋙ F) (CostructuredArrow.map (S := L) (R.map f))
    apply colimMap
    refine ⟨fun X => F.map (CommaMorphism.mk (𝟙 X.left) f (by simp)), ?_⟩
    intros X Y g
    dsimp
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    aesop_cat
  map_id b := by
    ext X
    simp only [comp_obj, Functor.comp_map, id_eq, eq_mpr_eq_cast, ι_colimMap_assoc, colimit.ι_pre,
      Category.comp_id] at *
    apply innerFunctor_aux _ (colimit.ι (canonicalFunctor' L R b ⋙ F)) (by simp)
    simp [Comma.hom_ext_iff]
  map_comp {X Y Z} f g := by
    ext W
    simp
    sorry

noncomputable def colimitComparison (F : Comma L R ⥤ C) [HasColimits C] :
    colimit F ≅ colimit (innerFunctor L R F) :=
  (lanCompColimIso (Comma.snd L R)).symm.app F ≪≫
    HasColimit.isoOfNatIso (NatIso.ofComponents (fun b₀ => by { sorry  })
      _)
#check L

end SmallCategory

-- instance final_fst (L : A ⥤ T) (R : B ⥤ T) [Functor.Final R] : Functor.Final (Comma.fst L R) := by
--   constructor
--   intro X

--   sorry

end CategoryTheory
