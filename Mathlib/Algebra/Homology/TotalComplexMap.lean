import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Linear

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  {I₁ I₂ I : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [DecidableEq I] (K : HomologicalComplex₂ C c₁ c₂) (c : ComplexShape I)
  [TotalComplexShape c₁ c₂ c]

abbrev _root_.CategoryTheory.Functor.PreservesTotalComplex :=
  ∀ n, PreservesColimit (Discrete.functor
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)) F

variable [K.HasTotal c] [F.PreservesTotalComplex K c]

instance hasTotalOfPreserves : ((F.mapHomologicalComplex₂ c₁ c₂).obj K).HasTotal c := fun n =>
  hasColimitOfIso (F := (Discrete.functor (K.toGradedObject.mapObjFun
    (ComplexShape.π c₁ c₂ c) n)) ⋙ F) (Discrete.natIso (fun _ => Iso.refl _))

noncomputable def mapTotalXIso (n : I) :
    (((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c).X n ≅ F.obj ((K.total c).X n) := by
  let s := (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)
  have : HasCoproduct (fun x => s x) := inferInstanceAs (HasCoproduct s)
  letI : PreservesColimit (Discrete.functor s) F :=
    inferInstanceAs (PreservesColimit (Discrete.functor
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)) F)
  have : HasCoproduct (fun x => F.obj (s x)) :=
    inferInstanceAs (HasCoproduct
      (((F.mapHomologicalComplex₂ c₁ c₂).obj K).toGradedObject.mapObjFun
        (ComplexShape.π c₁ c₂ c) n))
  exact asIso (Limits.sigmaComparison F s)

section

variable (i₁ : I₁) (i₂ : I₂) (n : I)

@[reassoc (attr := simp)]
lemma ι_mapTotalXIso_hom (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = n) :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c i₁ i₂ n h ≫ (mapTotalXIso F K c n).hom =
      F.map (K.ιTotal c i₁ i₂ n h) := by
  let s := (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) n)
  have : HasCoproduct (fun x => F.obj (s x)) :=
    inferInstanceAs (HasCoproduct
      (((F.mapHomologicalComplex₂ c₁ c₂).obj K).toGradedObject.mapObjFun
        (ComplexShape.π c₁ c₂ c) n))
  apply ι_comp_sigmaComparison F s

@[reassoc (attr := simp)]
lemma map_ι_mapTotalXIso_inv (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = n) :
    F.map (K.ιTotal c i₁ i₂ n h) ≫ (mapTotalXIso F K c n).inv =
      ((F.mapHomologicalComplex₂ c₁ c₂).obj K).ιTotal c i₁ i₂ n h := by
  rw [← ι_mapTotalXIso_hom, assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma mapHomologicalComplex₂_d₁ :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).d₁ c i₁ i₂ n =
      F.map (K.d₁ c i₁ i₂ n) ≫ (mapTotalXIso F K c n).inv := by
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · by_cases h₂ : ComplexShape.π c₁ c₂ c (c₁.next i₁, i₂) = n
    · simp [d₁_eq _ _ h₁ _ _ h₂]
    · simp [d₁_eq_zero' _ _ h₁ _ _ h₂]
  · simp [d₁_eq_zero _ _ _ _ _ h₁]

@[reassoc (attr := simp)]
lemma mapHomologicalComplex₂_d₂ :
    ((F.mapHomologicalComplex₂ c₁ c₂).obj K).d₂ c i₁ i₂ n =
      F.map (K.d₂ c i₁ i₂ n) ≫ (mapTotalXIso F K c n).inv := by
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · by_cases h₂ : ComplexShape.π c₁ c₂ c (i₁, c₂.next i₂) = n
    · simp [d₂_eq _ _ _ h₁ _ h₂]
    · simp [d₂_eq_zero' _ _ _ h₁ _ h₂]
  · simp [d₂_eq_zero _ _ _ _ _ h₁]

end

noncomputable def mapTotalIso : ((F.mapHomologicalComplex₂ c₁ c₂).obj K).total c ≅
    (F.mapHomologicalComplex c).obj (K.total c) :=
  HomologicalComplex.Hom.isoOfComponents (mapTotalXIso F K c) (by
    intros
    ext
    simp [-Functor.map_comp, ← F.map_comp])

end HomologicalComplex₂
