import Mathlib.Algebra.Homology.Embedding.StupidFiltration
import Mathlib.Algebra.Homology.TotalComplex

open CategoryTheory Category Limits ComplexShape

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Limits

variable [IsIdempotentComplete C] {I : Type*}
  {X : I → C} (Y : I → C)
  (hX : ∀ (i : I), DirectFactor (X i) (Y i))

lemma hasCoproduct_of_direct_factor [HasCoproduct Y] : HasCoproduct X := by
  let p : ∐ Y ⟶ ∐ Y := Sigma.map (fun i => (hX i).r ≫ (hX i).s)
  obtain ⟨S, h, fac⟩ := directFactor_of_isIdempotentComplete _ p (by aesop_cat)
  refine ⟨Cofan.mk S (fun i => (hX i).s ≫ Sigma.ι Y i ≫ h.r),
    mkCofanColimit _ (fun c => h.s ≫ Sigma.desc (fun i => (hX i).r ≫ c.inj i))
      (fun c i => by simp [p, reassoc_of% fac])
      (fun c m hm => ?_)⟩
  dsimp at m ⊢
  rw [← cancel_epi h.r]
  ext i
  simp [← hm, reassoc_of% fac, p]
  simp only [← assoc]
  congr 1
  rw [← cancel_mono h.s]
  simp [fac, p]

end Limits

end CategoryTheory

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Preadditive C] [IsIdempotentComplete C]
  {ι₁ ι₂ ι : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {K : HomologicalComplex₂ C c₁ c₂} (L : HomologicalComplex₂ C c₁ c₂)
  (c : ComplexShape ι) [TotalComplexShape c₁ c₂ c]
  (h : ∀ i₁ i₂, DirectFactor ((K.X i₁).X i₂) ((L.X i₁).X i₂))

lemma hasTotal_of_directFactor [L.HasTotal c] : K.HasTotal c :=
  fun i => hasCoproduct_of_direct_factor
    (GradedObject.mapObjFun L.toGradedObject (π c₁ c₂ c) i) (fun _ => h _ _)

variable {ι₁' : Type*} {c₁' : ComplexShape ι₁'} (e : c₁'.Embedding c₁) [e.IsRelIff]
  [HasZeroObject C]

instance [K.HasTotal c] : HomologicalComplex₂.HasTotal (K.stupidTrunc e) c :=
  hasTotal_of_directFactor K c
    (fun i₁ i₂ => (K.stupidTruncDirectFactor e i₁).map (HomologicalComplex.eval _ _ i₂))

end HomologicalComplex₂

namespace ComplexShape

open Embedding

lemma embeddingUpIntGE_monotone (a a' : ℤ) (h : a' ≤ a):
    (embeddingUpIntGE a).Subset (embeddingUpIntGE a') where
  subset := by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
    rintro _ ⟨l, rfl⟩
    exact ⟨k + l, by dsimp; omega⟩

end ComplexShape

namespace CochainComplex

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

noncomputable abbrev stupidFiltrationGEFunctor :
    ℤᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ComplexShape.Embedding.stupidTruncGEFiltration
    (fun n => ComplexShape.embeddingUpIntGE n.unop)
      (fun _ _ φ => ComplexShape.embeddingUpIntGE_monotone _ _ (leOfHom φ.unop)) C

variable {C}
variable (K L : CochainComplex C ℤ)

noncomputable abbrev stupidFiltrationGE : ℤᵒᵖ ⥤ CochainComplex C ℤ :=
  stupidFiltrationGEFunctor C ⋙ ((evaluation _ _).obj K)

end CochainComplex

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Abelian C] {ι : Type*} (c : ComplexShape ι)

noncomputable abbrev rowFiltrationGEFunctor :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c ⥤ HomologicalComplex₂ C (up ℤ) c :=
  CochainComplex.stupidFiltrationGEFunctor _

instance (n : ℤᵒᵖ) {ι' : Type*} {c' : ComplexShape ι'}
    (K : HomologicalComplex₂ C (up ℤ) c) [TotalComplexShape (up ℤ) c c'] [K.HasTotal c']:
    (((rowFiltrationGEFunctor C _).obj n).obj K).HasTotal c' := by
  dsimp [rowFiltrationGEFunctor]
  infer_instance

variable {C c}

noncomputable def rowFiltration (K : HomologicalComplex₂ C (up ℤ) c) :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c :=
  rowFiltrationGEFunctor C c ⋙ ((evaluation _ _).obj K)

noncomputable def rowFiltrationMap {K L : HomologicalComplex₂ C (up ℤ) c} (φ : K ⟶ L) :
    K.rowFiltration ⟶ L.rowFiltration :=
  whiskerLeft _ ((evaluation _ _).map φ)

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
variable [K.HasTotal (up ℤ)]

instance (n : ℤᵒᵖ) : (K.rowFiltration.obj n).HasTotal (up ℤ) := by
  dsimp [rowFiltration]
  infer_instance


end HomologicalComplex₂
