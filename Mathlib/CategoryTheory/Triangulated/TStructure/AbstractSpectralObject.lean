import Mathlib.CategoryTheory.Triangulated.SpectralObject

open CategoryTheory Category Limits Pretriangulated

variable (C : Type _) [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace CategoryTheory

namespace Triangulated

namespace SpectralObject

structure CandidateAbstractSpectralObject where
  ι : Type _
  hι : Category ι
  bot : ι
  top : ι
  isInitial_bot : IsInitial bot
  isTerminal_top : IsTerminal top
  truncLT : ι ⥤ C ⥤ C
  truncGE : ι ⥤ C ⥤ C
  truncLTObjTopIso' : truncLT.obj top ≅ 𝟭 C
  truncGEObjBotIso' : truncGE.obj bot ≅ 𝟭 C
  truncLTδGE : truncGE ⟶ truncLT ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ)))

variable {C}
variable (F : CandidateAbstractSpectralObject C)

namespace CandidateAbstractSpectralObject

instance : Bot F.ι := ⟨F.bot⟩
instance : Top F.ι := ⟨F.top⟩
instance : Category F.ι := F.hι

def fromBot (a : F.ι) : ⊥ ⟶ a := F.isInitial_bot.to a
def toTop (a : F.ι) : a ⟶ ⊤ := F.isTerminal_top.from a

@[reassoc (attr := simp)]
lemma comp_toTop {a b : F.ι} (φ : a ⟶ b) : φ ≫ F.toTop b = F.toTop a := by
  apply F.isTerminal_top.hom_ext

@[reassoc (attr := simp)]
lemma fromBot_comp {a b : F.ι} (φ : a ⟶ b) : F.fromBot a ≫ φ = F.fromBot b := by
  apply F.isInitial_bot.hom_ext

def truncLTObjTopIso : F.truncLT.obj ⊤ ≅ 𝟭 C := F.truncLTObjTopIso'
def truncGEObjBotIso : F.truncGE.obj ⊥ ≅ 𝟭 C := F.truncGEObjBotIso'

def truncLTι (a : F.ι) : F.truncLT.obj a ⟶ 𝟭 C :=
  F.truncLT.map (F.toTop a) ≫ F.truncLTObjTopIso.hom

@[reassoc (attr := simp)]
lemma truncLTmap_ι {a b : F.ι} (φ : a ⟶ b) :
    F.truncLT.map φ ≫ F.truncLTι b = F.truncLTι a := by
  dsimp only [truncLTι]
  simp only [← Functor.map_comp_assoc, comp_toTop]

def truncGEπ (a : F.ι) : 𝟭 C ⟶ F.truncGE.obj a :=
  F.truncGEObjBotIso.inv ≫ F.truncGE.map (F.fromBot a)

@[reassoc (attr := simp)]
lemma truncGEπ_map {a b : F.ι} (φ : a ⟶ b) :
    F.truncGEπ a ≫ F.truncGE.map φ = F.truncGEπ b := by
  dsimp only [truncGEπ]
  simp only [assoc, ← Functor.map_comp, fromBot_comp]

def triangleLTGE : F.ι ⥤ C ⥤ Triangle C where
  obj a := Triangle.functorMk (F.truncLTι a) (F.truncGEπ a) (F.truncLTδGE.app a)
  map φ := Triangle.functorHomMk' (F.truncLT.map φ) (𝟙 _) ((F.truncGE.map φ))
    (by simp) (by simp ) (by simp)

class IsDistinguishedTriangleLTGE where
  distinguished (a : F.ι) (X : C) : (F.triangleLTGE.obj a).obj X ∈ distTriang C

def truncGELT : Arrow F.ι ⥤ C ⥤ C where
  obj D := F.truncLT.obj D.right ⋙ F.truncGE.obj D.left
  map φ := F.truncLT.map φ.right ◫ F.truncGE.map φ.left

def triangleLTGEPrecompTruncGELT : Arrow₂ F.ι ⥤ C ⥤ Triangle C :=
  (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C (Triangle C)))).obj
    (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.triangleLTGE)

lemma triangleLTGEPrecompTruncGELT_distinguished
    [hF : F.IsDistinguishedTriangleLTGE] (D : Arrow₂ F.ι) (X : C) :
    (F.triangleLTGEPrecompTruncGELT.obj D).obj X ∈ distTriang C :=
  hF.distinguished D.X₁ _

@[simp]
def TruncGEToTruncGEGE.app (a b : F.ι) :
    F.truncGE.obj b ⟶ F.truncGE.obj a ⋙ F.truncGE.obj b :=
  whiskerRight (F.truncGEπ a) (F.truncGE.obj b)

@[simp]
def TruncLTLTToTruncLT.app (a b : F.ι) :
    F.truncLT.obj b ⋙ F.truncLT.obj a ⟶ F.truncLT.obj a :=
  whiskerRight (F.truncLTι b) (F.truncLT.obj a)

@[simps]
def truncGEToTruncGEGE : Arrow.rightFunc ⋙ F.truncGE ⟶
    (((whiskeringRight₂ (Arrow F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.leftFunc ⋙ F.truncGE)).obj (Arrow.rightFunc ⋙ F.truncGE) where
  app D := (TruncGEToTruncGEGE.app F) D.left D.right
  naturality D₁ D₂ φ := by
    ext X
    dsimp
    simp only [NatTrans.naturality, NatTrans.naturality_assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, truncGEπ_map]

@[simps]
def truncLTLTToTruncLT :
    (((whiskeringRight₂ (Arrow F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.rightFunc ⋙ F.truncLT)).obj (Arrow.leftFunc ⋙ F.truncLT) ⟶
        Arrow.leftFunc ⋙ F.truncLT where
  app D := (TruncLTLTToTruncLT.app F) D.left D.right
  naturality D₁ D₂ φ := by
    ext X
    dsimp
    simp only [NatTrans.naturality, assoc, ← Functor.map_comp,
      ← NatTrans.comp_app, truncLTmap_ι]

class IsCompatible where
  isIso_truncGEToTruncGEGE : IsIso F.truncGEToTruncGEGE
  isIso_truncLTLTToTruncLT : IsIso F.truncLTLTToTruncLT
  truncGEπ_compatibility' (a : F.ι) (X : C) :
    (F.truncGE.obj a).map ((F.truncGEπ a).app X) =
      (F.truncGEπ a).app ((F.truncGE.obj a).obj X)

variable [F.IsCompatible]

attribute [instance] IsCompatible.isIso_truncGEToTruncGEGE
  IsCompatible.isIso_truncLTLTToTruncLT

@[simps! hom]
noncomputable def truncGEIsoTruncGEGE := asIso F.truncGEToTruncGEGE

@[simps! hom]
noncomputable def truncLTLTIsoTruncLT := asIso F.truncLTLTToTruncLT

@[simps!]
noncomputable def truncGEGELTIsoTruncGELT :
  Arrow₂.δ₀ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.truncGE) :=
  NatIso.ofComponents (fun D => isoWhiskerLeft (F.truncLT.obj D.X₂)
    (F.truncGEIsoTruncGEGE.app (Arrow₂.δ₂.obj D))) (fun {D₁ D₂} φ => by
      ext X
      dsimp [truncGELT]
      simp only [assoc, Functor.map_comp, NatTrans.naturality, NatTrans.naturality_assoc]
      simp only [← Functor.map_comp]
      congr 2
      simp only [← NatTrans.naturality, ← NatTrans.naturality_assoc, Functor.id_map,
        ← NatTrans.comp_app, truncGEπ_map])

def truncGELTπ := whiskerRight Arrow₂.δ₁Toδ₀ F.truncGELT

lemma truncGEπ_compatibility (a : F.ι) (X : C) :
    (F.truncGE.obj a).map ((F.truncGEπ a).app X) =
      (F.truncGEπ a).app ((F.truncGE.obj a).obj X) :=
  IsCompatible.truncGEπ_compatibility' _ _

@[reassoc]
lemma truncGEGELTIsoTruncGELT_compatibility (D : Arrow₂ F.ι) (X : C) :
  (F.truncGELTπ.app D).app X ≫ (F.truncGEGELTIsoTruncGELT.hom.app D).app X =
    (F.truncGEπ D.X₁).app (((truncGELT F).obj (Arrow₂.δ₁.obj D)).obj X) := by
  dsimp [truncGELTπ, truncGELT]
  simp only [Functor.map_id, NatTrans.id_app, comp_id,
    ← NatTrans.naturality, truncGEπ_compatibility]
  exact (congr_app (F.truncGEπ_map D.f) (((F.truncGE.obj D.X₀).obj ((F.truncLT.obj D.X₂).obj X))))

@[simps!]
noncomputable def truncGELTIsoTruncGELTLT :
  Arrow₂.δ₂ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.obj₂ ⋙ F.truncLT)).obj (Arrow₂.δ₂ ⋙ F.truncGELT) :=
  Iso.symm
    (NatIso.ofComponents (fun D => isoWhiskerRight ((F.truncLTLTIsoTruncLT.app
      (Arrow₂.δ₀.obj D))) (F.truncGE.obj D.X₀)) (fun {D₁ D₂} φ => by
        ext X
        dsimp [truncGELT]
        simp only [assoc, NatTrans.naturality_assoc, ← Functor.map_comp]
        congr 2
        rw [NatTrans.naturality, ← NatTrans.comp_app, truncLTmap_ι]))

def truncLTGE : Arrow F.ι ⥤ C ⥤ C where
  obj D := F.truncGE.obj D.left ⋙ F.truncLT.obj D.right
  map φ := F.truncGE.map φ.left ◫ F.truncLT.map φ.right

/-def truncLTGEIsoTruncGELT : F.truncLTGE ≅ F.truncGELT := sorry

noncomputable def truncGELTLTIsoTruncGELT :
    (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.obj₂ ⋙ F.truncLT)).obj (Arrow₂.δ₂ ⋙ F.truncGELT) ≅
    (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.truncLT) :=
  (NatIso.ofComponents (fun D => isoWhiskerLeft (F.truncLT.obj D.X₂)
    (F.truncLTGEIsoTruncGELT.app (Arrow₂.δ₂.obj D)).symm) (fun {D₁ D₂} φ => by
      ext X
      have eq := congr_app (F.truncLTGEIsoTruncGELT.inv.naturality
        (Arrow₂.δ₂.map φ)) ((F.truncLT.obj D₂.X₂).obj X)
      have eq' := (F.truncLTGEIsoTruncGELT.inv.app (Arrow.mk D₁.f)).naturality ((F.truncLT.map φ.τ₂).app X)
      simp only [NatTrans.naturality_assoc, assoc, Functor.map_comp, NatTrans.naturality]
      dsimp [truncGELT, truncLTGE] at eq eq' ⊢
      simp only [assoc] at eq eq' ⊢
      rw [eq, reassoc_of% eq']
      congr 1
      simp only [NatTrans.naturality_assoc, Functor.map_comp, assoc, NatTrans.naturality]
      simp only [← Functor.map_comp, NatTrans.naturality]))

noncomputable def truncLTGELTIsoTruncGELT :
  Arrow₂.δ₂ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ F.ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.truncLT) :=
  F.truncGELTIsoTruncGELTLT ≪≫ F.truncGELTLTIsoTruncGELT

def truncGELTι := whiskerRight Arrow₂.δ₂Toδ₁ F.truncGELT

@[reassoc]
lemma truncLTGELTIsoTruncGELT_compatibility (D : Arrow₂ F.ι) (X : C) :
    (F.truncLTGELTIsoTruncGELT.hom.app D).app X ≫
      (F.truncLTι D.X₁).app ((F.truncGELT.obj (Arrow₂.δ₁.obj D)).obj X) =
    ((F.truncGELTι).app D).app X := sorry

noncomputable def truncGELTδ : Arrow₂.δ₀ ⋙ F.truncGELT ⟶
    Arrow₂.δ₂ ⋙ F.truncGELT ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) := by
  refine' F.truncGEGELTIsoTruncGELT.hom ≫ (((whiskeringRight₂ (Arrow₂ F.ι) (C ⥤ C) (C ⥤ C) (C ⥤ C)).obj
    (whiskeringLeft C C C)).obj (Arrow₂.δ₁ ⋙ F.truncGELT)).map (whiskerLeft Arrow₂.obj₁ F.truncLTδGE) ≫ _ ≫
    whiskerRight F.truncLTGELTIsoTruncGELT.inv
      ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ)))
  exact { app := fun D => 𝟙 _ }

@[simps]
noncomputable def triangle : Arrow₂ F.ι ⥤ C ⥤ Triangle C where
  obj D := Triangle.functorMk (F.truncGELTι.app D) (F.truncGELTπ.app D) (F.truncGELTδ.app D)
  map φ := Triangle.functorHomMk' ((Arrow₂.δ₂ ⋙ F.truncGELT).map φ)
      (((Arrow₂.δ₁ ⋙ F.truncGELT).map φ)) ((((Arrow₂.δ₀ ⋙ F.truncGELT).map φ)))
        (F.truncGELTι.naturality φ).symm (F.truncGELTπ.naturality φ).symm
        (F.truncGELTδ.naturality φ).symm

@[simps!]
noncomputable def triangleObjIsoTriangleLTGEPrecompTruncGELTObj (D : Arrow₂ F.ι) :
    F.triangle.obj D ≅ F.triangleLTGEPrecompTruncGELT.obj D := by
  refine' Triangle.functorIsoMk _ _ (F.truncLTGELTIsoTruncGELT.app D) (Iso.refl _)
    (F.truncGEGELTIsoTruncGELT.app D) _ _ _
  . ext X
    dsimp [triangleLTGEPrecompTruncGELT]
    rw [comp_id]
    exact (F.truncLTGELTIsoTruncGELT_compatibility D X).symm
  . ext X
    dsimp [triangleLTGEPrecompTruncGELT]
    rw [id_comp]
    exact F.truncGEGELTIsoTruncGELT_compatibility D X
  . ext X
    dsimp [truncGELTδ, triangleLTGEPrecompTruncGELT, whiskeringRight₂, triangleLTGE]
    erw [id_comp, assoc, assoc, ← Functor.map_comp, ← NatTrans.comp_app, Iso.inv_hom_id_app,
      NatTrans.id_app, Functor.map_id, id_comp, Functor.map_id, comp_id]

noncomputable def triangleIsoTriangleLTGEPrecompTruncGELT : F.triangle ≅ F.triangleLTGEPrecompTruncGELT :=
  NatIso.ofComponents F.triangleObjIsoTriangleLTGEPrecompTruncGELTObj (fun φ => by
    ext X
    . exact congr_app (F.truncLTGELTIsoTruncGELT.hom.naturality φ) X
    . dsimp [triangle, triangleLTGEPrecompTruncGELT, triangleLTGE]
      rw [comp_id, id_comp]
    . exact congr_app (F.truncGEGELTIsoTruncGELT.hom.naturality φ) X)

lemma triangle_distinguished
    [F.IsDistinguishedTriangleLTGE] (D : Arrow₂ F.ι) (X : C) :
    (F.triangle.obj D).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (F.triangleLTGEPrecompTruncGELT_distinguished D X) _
    (((F.triangleIsoTriangleLTGEPrecompTruncGELT).app D).app X)

noncomputable def spectralObject [F.IsDistinguishedTriangleLTGE] (X : C) :
    SpectralObject C F.ι where
  ω₁ := ((whiskeringRight (Arrow F.ι) _ _).obj ((evaluation C C).obj X)).obj F.truncGELT
  δ := whiskerRight F.truncGELTδ ((evaluation C C).obj X)
  distinguished' D := F.triangle_distinguished D X-/

end CandidateAbstractSpectralObject

end SpectralObject

end Triangulated

end CategoryTheory
