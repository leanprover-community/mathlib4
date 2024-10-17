/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Grothendieck

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
variable {C : Type (max v₁ u₂)} [Category.{max v₁ v₂} C]
variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

variable [HasColimitsOfSize.{v₁} C]


noncomputable def bla (F : Comma L R ⥤ C) : B ⥤ C :=
  (lan (Comma.snd L R)).obj F

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
  sorry

/-- `CostructuredArrow L` induces a strict functor `T ⥤ Cat`. -/
@[simps]
def CostructuredArrow.functor : T ⥤ Cat where
  obj t := .of <| CostructuredArrow L t
  map f := CostructuredArrow.map f
  map_id t := by
    apply Functor.ext
    intro
    simp [CostructuredArrow.map, Comma.mapRight]
    simp
  map_comp f g := by
    apply Functor.ext
    intro
    simp [CostructuredArrow.map, Comma.mapRight]
    simp

@[simps]
def CostructuredArrow.grothendieckCommaFunctor :
    Grothendieck (R ⋙ CostructuredArrow.functor L) ⥤ Comma L R where
  obj := fun P => ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map := fun f => ⟨f.fiber.left, f.base, by simp⟩

@[simps]
def Comma.toCostructuredArrowGrothendieck :
    Comma L R ⥤ Grothendieck (R ⋙ CostructuredArrow.functor L) where
  obj := fun X => ⟨X.right, CostructuredArrow.mk X.hom⟩
  map := fun f => ⟨f.right, CostructuredArrow.homMk f.left⟩
  map_id X := by
    apply Grothendieck.ext
    · simp
    · rfl
  map_comp f g := by
    apply Grothendieck.ext
    · simp
    · rfl

example : Grothendieck (R ⋙ CostructuredArrow.functor L) ≌ Comma L R where
  functor := CostructuredArrow.grothendieckCommaFunctor _ _
  inverse := Comma.toCostructuredArrowGrothendieck _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

variable (C) [HasColimits C]

def Grothendieck.pre {C D : Type*} [Category C] [Category D] (F : D ⥤ Cat) (G : C ⥤ D) :
    Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj := fun X => ⟨G.obj X.base, X.fiber⟩
  map := fun f => ⟨G.map f.base, f.fiber⟩
  map_id := fun X => by {simp; fapply Grothendieck.ext; dsimp; exact G.map_id _; simp }
  map_comp := fun f g => by {simp; fapply Grothendieck.ext; dsimp; exact G.map_comp _ _; simp }

/-- Fully pointfree phrasing of 3.4.3 (i) -/
def colimThm :
    colim (J := Comma L R) (C := C) ≅
    (whiskeringLeft _ _ _).obj (CostructuredArrow.grothendieckCommaFunctor L R) ⋙ colim := by
  sorry  -- TODO make pointfree version of finality condition

/-- Kan-free phrasing of 2.3.4, to be proven by #17531 -/
def thm234 (α : A ⥤ C) :
    colimit α ≅ colimit (J := Grothendieck (CostructuredArrow.functor L))
      (CostructuredArrow.grothendieckCommaFunctor L (𝟭 _) ⋙ Comma.fst _ _ ⋙ α) :=
  _

/-- This is still missing somehow -/
def final_of_colimit_iso_colimit {C : Type*}  [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : C ⥤ D)
    [∀ (G : D ⥤ E), HasColimit G]
    [∀ (G : D ⥤ E), HasColimit (F ⋙ G)]
    (h : ∀ (G : D ⥤ E), colimit (F ⋙ G) ≅ colimit G) :
    Final F := sorry

/-- 3.4.3 (ii)-/
example [R.Final] : (Comma.fst L R).Final := by
  apply final_of_colimit_iso_colimit (E := Type v₁)
  intro α
  let β := (Comma.fst L R) ⋙ α
  symm
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  letI fR' : Final R' := sorry
  exact thm234.{v₁, v₁, v₁ + 1} _ L α ≪≫
    (Final.colimitIso R' _).symm ≪≫
    ((colimThm.{v₁, v₁, v₁ + 1} (Type v₁) L R).symm).app β

end SmallCategory

end CategoryTheory
