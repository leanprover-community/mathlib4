import Mathlib.CategoryTheory.Triangulated.SpectralObjectNew

open CategoryTheory Category Limits Pretriangulated

variable (C : Type _) [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace CategoryTheory

namespace Triangulated

namespace SpectralObject

variable (ι : Type _) [Preorder ι] [OrderBot ι] [OrderTop ι]

structure AbstractSpectralObject where
  truncLT : ι ⥤ C ⥤ C
  truncGE : ι ⥤ C ⥤ C
  truncLTObjTopIso' : truncLT.obj ⊤ ≅ 𝟭 C
  truncGEObjBotIso' : truncGE.obj ⊥ ≅ 𝟭 C
  truncGEδLT : truncGE ⟶ truncLT ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ)))

variable {C ι}
variable (F : AbstractSpectralObject C ι)

namespace AbstractSpectralObject

def truncLTObjTopIso : F.truncLT.obj ⊤ ≅ 𝟭 C := F.truncLTObjTopIso'
def truncGEObjBotIso : F.truncGE.obj ⊥ ≅ 𝟭 C := F.truncGEObjBotIso'

def truncLTι (a : ι) : F.truncLT.obj a ⟶ 𝟭 C :=
  F.truncLT.map (homOfLE le_top) ≫ F.truncLTObjTopIso.hom

@[reassoc (attr := simp)]
lemma truncLTmap_ι {a b : ι} (φ : a ⟶ b) :
    F.truncLT.map φ ≫ F.truncLTι b = F.truncLTι a := by
  dsimp only [truncLTι]
  simp only [← Functor.map_comp_assoc]
  congr 1

def truncGEπ (a : ι) : 𝟭 C ⟶ F.truncGE.obj a :=
  F.truncGEObjBotIso.inv ≫ F.truncGE.map (homOfLE bot_le)

@[reassoc (attr := simp)]
lemma truncGEπ_map {a b : ι} (φ : a ⟶ b) :
    F.truncGEπ a ≫ F.truncGE.map φ = F.truncGEπ b := by
  dsimp only [truncGEπ]
  simp only [assoc, ← Functor.map_comp]
  congr 1

instance : IsIso (F.truncLTι ⊤) := by
  dsimp [truncLTι]
  erw [Functor.map_id, id_comp]
  infer_instance

instance : IsIso (F.truncGEπ ⊥) := by
  dsimp [truncGEπ]
  erw [Functor.map_id, comp_id]
  infer_instance


@[simps]
def triangleLTGE : ι ⥤ C ⥤ Triangle C where
  obj a := Triangle.functorMk (F.truncLTι a) (F.truncGEπ a) (F.truncGEδLT.app a)
  map φ := Triangle.functorHomMk' (F.truncLT.map φ) (𝟙 _) ((F.truncGE.map φ))
    (by simp) (by simp ) (by simp)

def truncGELT : Arrow ι ⥤ C ⥤ C where
  obj D := F.truncLT.obj D.right ⋙ F.truncGE.obj D.left
  map φ := F.truncLT.map φ.right ◫ F.truncGE.map φ.left

def triangleLTGEPrecompTruncGELT : Arrow₂ ι ⥤ C ⥤ Triangle C :=
  (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C (Triangle C)))).obj
    (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.triangleLTGE)

@[simp]
def TruncGEToTruncGEGE.app (a b : ι) :
    F.truncGE.obj b ⟶ F.truncGE.obj a ⋙ F.truncGE.obj b :=
  whiskerRight (F.truncGEπ a) (F.truncGE.obj b)

@[simp]
def TruncLTLTToTruncLT.app (a b : ι) :
    F.truncLT.obj b ⋙ F.truncLT.obj a ⟶ F.truncLT.obj a :=
  whiskerRight (F.truncLTι b) (F.truncLT.obj a)

@[simps]
def truncGEToTruncGEGE : Arrow.rightFunc ⋙ F.truncGE ⟶
    (((whiskeringRight₂ (Arrow ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.leftFunc ⋙ F.truncGE)).obj (Arrow.rightFunc ⋙ F.truncGE) where
  app D := (TruncGEToTruncGEGE.app F) D.left D.right
  naturality D₁ D₂ φ := by
    ext X
    dsimp
    simp only [NatTrans.naturality, NatTrans.naturality_assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, truncGEπ_map]

@[simps]
def truncLTLTToTruncLT :
    (((whiskeringRight₂ (Arrow ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.rightFunc ⋙ F.truncLT)).obj (Arrow.leftFunc ⋙ F.truncLT) ⟶
        Arrow.leftFunc ⋙ F.truncLT where
  app D := (TruncLTLTToTruncLT.app F) D.left D.right
  naturality D₁ D₂ φ := by
    ext X
    dsimp
    simp only [NatTrans.naturality, assoc, ← Functor.map_comp,
      ← NatTrans.comp_app, truncLTmap_ι]

def truncLTGE : Arrow ι ⥤ C ⥤ C where
  obj D := F.truncGE.obj D.left ⋙ F.truncLT.obj D.right
  map φ := F.truncGE.map φ.left ◫ F.truncLT.map φ.right

def truncLTGELTSelfToTruncLTGE :
    (((whiskeringRight₂ (Arrow ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.rightFunc ⋙ F.truncLT)).obj F.truncLTGE ⟶ F.truncLTGE where
  app D := whiskerRight (F.truncLTι D.right) (F.truncLTGE.obj D)
  naturality {D₁ D₂} φ:= by
    ext X
    dsimp
    simp only [NatTrans.naturality, assoc, ← Functor.map_comp,
      ← NatTrans.comp_app, truncLTmap_ι]

def truncLTGELTSelfToTruncGELT :
    (((whiskeringRight₂ (Arrow ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow.rightFunc ⋙ F.truncLT)).obj F.truncLTGE ⟶ F.truncGELT where
  app D := whiskerLeft (F.truncGELT.obj D) (F.truncLTι D.right)
  naturality {D₁ D₂} φ := by
    ext
    dsimp [truncLTGE, truncGELT]
    simp only [NatTrans.naturality_assoc, assoc, NatTrans.naturality,
      Functor.id_obj, Functor.id_map]
    simp only [← assoc]
    congr 2
    rw [← NatTrans.comp_app, truncLTmap_ι]

class IsCompatible where
  isIso_truncGEToTruncGEGE : IsIso F.truncGEToTruncGEGE := by infer_instance
  isIso_truncLTLTToTruncLT : IsIso F.truncLTLTToTruncLT := by infer_instance
  isIso_truncLTGELTSelfToTruncLTGE : IsIso F.truncLTGELTSelfToTruncLTGE := by infer_instance
  isIso_truncLTGELTSelfToTruncGELT : IsIso F.truncLTGELTSelfToTruncGELT := by infer_instance
  truncGEπ_compatibility' (a : ι) (X : C) :
    (F.truncGE.obj a).map ((F.truncGEπ a).app X) =
      (F.truncGEπ a).app ((F.truncGE.obj a).obj X)
  truncLTι_compatibility' (a : ι) (X : C) :
    (F.truncLT.obj a).map ((F.truncLTι a).app X) =
      (F.truncLTι a).app ((F.truncLT.obj a).obj X)
  distinguished (a : ι) (X : C) : (F.triangleLTGE.obj a).obj X ∈ distTriang C

variable [F.IsCompatible]

lemma triangleLTGEPrecompTruncGELT_distinguished (D : Arrow₂ ι) (X : C) :
    (F.triangleLTGEPrecompTruncGELT.obj D).obj X ∈ distTriang C :=
  IsCompatible.distinguished _ _

attribute [instance] IsCompatible.isIso_truncGEToTruncGEGE
  IsCompatible.isIso_truncLTLTToTruncLT IsCompatible.isIso_truncLTGELTSelfToTruncLTGE
  IsCompatible.isIso_truncLTGELTSelfToTruncGELT

@[simps! hom]
noncomputable def truncGEIsoTruncGEGE := asIso F.truncGEToTruncGEGE

@[simps! hom]
noncomputable def truncLTLTIsoTruncLT := asIso F.truncLTLTToTruncLT

@[simps!]
noncomputable def truncGEGELTIsoTruncGELT :
  Arrow₂.δ₀ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C C))).obj
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

lemma truncGEπ_compatibility (a : ι) (X : C) :
    (F.truncGE.obj a).map ((F.truncGEπ a).app X) =
      (F.truncGEπ a).app ((F.truncGE.obj a).obj X) :=
  IsCompatible.truncGEπ_compatibility' _ _

lemma truncLTι_compatibility (a : ι) (X : C) :
    (F.truncLT.obj a).map ((F.truncLTι a).app X) =
      (F.truncLTι a).app ((F.truncLT.obj a).obj X) :=
  IsCompatible.truncLTι_compatibility' _ _

@[reassoc]
lemma truncGEGELTIsoTruncGELT_compatibility (D : Arrow₂ ι) (X : C) :
  (F.truncGELTπ.app D).app X ≫ (F.truncGEGELTIsoTruncGELT.hom.app D).app X =
    (F.truncGEπ D.X₁).app (((truncGELT F).obj (Arrow₂.δ₁.obj D)).obj X) := by
  dsimp [truncGELTπ, truncGELT]
  simp only [Functor.map_id, NatTrans.id_app, comp_id,
    ← NatTrans.naturality, truncGEπ_compatibility]
  exact (congr_app (F.truncGEπ_map D.f) (((F.truncGE.obj D.X₀).obj ((F.truncLT.obj D.X₂).obj X))))

@[simps!]
noncomputable def truncGELTIsoTruncGELTLT :
  Arrow₂.δ₂ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.obj₂ ⋙ F.truncLT)).obj (Arrow₂.δ₂ ⋙ F.truncGELT) :=
  Iso.symm
    (NatIso.ofComponents (fun D => isoWhiskerRight ((F.truncLTLTIsoTruncLT.app
      (Arrow₂.δ₀.obj D))) (F.truncGE.obj D.X₀)) (fun {D₁ D₂} φ => by
        ext X
        dsimp [truncGELT]
        simp only [assoc, NatTrans.naturality_assoc, ← Functor.map_comp]
        congr 2
        rw [NatTrans.naturality, ← NatTrans.comp_app, truncLTmap_ι]))

noncomputable def truncLTGELTSelfIsoTruncLTGE := asIso F.truncLTGELTSelfToTruncLTGE
noncomputable def truncLTGELTSelfIsoTruncGELT := asIso F.truncLTGELTSelfToTruncGELT

noncomputable def truncLTGEIsoTruncGELT : F.truncLTGE ≅ F.truncGELT :=
  F.truncLTGELTSelfIsoTruncLTGE.symm ≪≫ F.truncLTGELTSelfIsoTruncGELT

@[reassoc]
lemma truncLTGEIsoTruncGELT_compatibility {a b : ι} (φ : a ⟶ b) (X : C) :
    (F.truncLTGEIsoTruncGELT.hom.app (Arrow.mk φ)).app X ≫
      (F.truncGE.obj a).map ((F.truncLTι b).app X) =
      (F.truncLTι b).app ((F.truncGE.obj a).obj X) := by
  have eq₁ := congr_app (F.truncLTGELTSelfIsoTruncLTGE.hom_inv_id_app (Arrow.mk φ)) X
  rw [NatTrans.comp_app] at eq₁
  dsimp [truncLTGEIsoTruncGELT]
  simp only [← cancel_epi ((F.truncLTGELTSelfIsoTruncLTGE.hom.app (Arrow.mk φ)).app X), assoc,
    reassoc_of% eq₁, NatTrans.id_app, id_comp]
  dsimp [truncLTGELTSelfIsoTruncGELT, truncLTGELTSelfIsoTruncLTGE,
    truncLTGELTSelfToTruncGELT, truncLTGELTSelfToTruncLTGE, asIso, truncLTGE, truncGELT]
  simp only [NatTrans.naturality, Functor.id_obj, Functor.id_map]

noncomputable def truncGELTLTIsoTruncGELT :
    (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.obj₂ ⋙ F.truncLT)).obj (Arrow₂.δ₂ ⋙ F.truncGELT) ≅
    (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.truncLT) :=
  (NatIso.ofComponents (fun D => isoWhiskerLeft (F.truncLT.obj D.X₂)
    (F.truncLTGEIsoTruncGELT.app (Arrow₂.δ₂.obj D)).symm) (fun {D₁ D₂} φ => by
      ext X
      have eq := congr_app (F.truncLTGEIsoTruncGELT.inv.naturality
        (Arrow₂.δ₂.map φ)) ((F.truncLT.obj D₂.X₂).obj X)
      have eq' := (F.truncLTGEIsoTruncGELT.inv.app (Arrow.mk D₁.f)).naturality
        ((F.truncLT.map φ.τ₂).app X)
      simp only [NatTrans.naturality_assoc, assoc, Functor.map_comp, NatTrans.naturality]
      dsimp [truncGELT, truncLTGE] at eq eq' ⊢
      simp only [assoc] at eq eq' ⊢
      rw [eq, reassoc_of% eq']
      congr 1
      simp only [NatTrans.naturality_assoc, Functor.map_comp, assoc, NatTrans.naturality]
      simp only [← Functor.map_comp, NatTrans.naturality]))

noncomputable def truncLTGELTIsoTruncGELT :
  Arrow₂.δ₂ ⋙ F.truncGELT ≅
    (((whiskeringRight₂ (Arrow₂ ι) _ _ _).obj ((whiskeringLeft C C C))).obj
      (Arrow₂.δ₁ ⋙ F.truncGELT)).obj (Arrow₂.obj₁ ⋙ F.truncLT) :=
  F.truncGELTIsoTruncGELTLT ≪≫ F.truncGELTLTIsoTruncGELT

def truncGELTι := whiskerRight Arrow₂.δ₂Toδ₁ F.truncGELT

@[reassoc]
lemma truncLTGELTIsoTruncGELT_compatibility' (D : Arrow₂ ι) (X : C) :
    (F.truncLTGELTIsoTruncGELT.inv.app D).app X ≫
      ((F.truncGELTι).app D).app X =
    (F.truncLTι D.X₁).app ((F.truncGELT.obj (Arrow₂.δ₁.obj D)).obj X) := by
  dsimp [truncLTGELTIsoTruncGELT, truncGELTι, truncGELT,
    truncLTLTIsoTruncLT, truncGELTLTIsoTruncGELT]
  rw [Functor.map_id, NatTrans.id_app, id_comp, assoc, ← Functor.map_comp,
    NatTrans.naturality, F.truncLTι_compatibility, ← NatTrans.comp_app, truncLTmap_ι,
    truncLTGEIsoTruncGELT_compatibility]

@[reassoc]
lemma truncLTGELTIsoTruncGELT_compatibility (D : Arrow₂ ι) (X : C) :
    (F.truncLTGELTIsoTruncGELT.hom.app D).app X ≫
      (F.truncLTι D.X₁).app ((F.truncGELT.obj (Arrow₂.δ₁.obj D)).obj X) =
    ((F.truncGELTι).app D).app X := by
  simp only [← truncLTGELTIsoTruncGELT_compatibility',
    ← NatTrans.comp_app, Iso.hom_inv_id_assoc]

noncomputable def truncGELTδ : Arrow₂.δ₀ ⋙ F.truncGELT ⟶
    Arrow₂.δ₂ ⋙ F.truncGELT ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) := by
  refine' F.truncGEGELTIsoTruncGELT.hom ≫
    (((whiskeringRight₂ (Arrow₂ ι) (C ⥤ C) (C ⥤ C) (C ⥤ C)).obj
      (whiskeringLeft C C C)).obj (Arrow₂.δ₁ ⋙ F.truncGELT)).map
        (whiskerLeft Arrow₂.obj₁ F.truncGEδLT) ≫ _ ≫
    whiskerRight F.truncLTGELTIsoTruncGELT.inv
      ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ)))
  exact { app := fun D => 𝟙 _ }

@[simps]
noncomputable def triangle : Arrow₂ ι ⥤ C ⥤ Triangle C where
  obj D := Triangle.functorMk (F.truncGELTι.app D) (F.truncGELTπ.app D) (F.truncGELTδ.app D)
  map φ := Triangle.functorHomMk' ((Arrow₂.δ₂ ⋙ F.truncGELT).map φ)
      (((Arrow₂.δ₁ ⋙ F.truncGELT).map φ)) ((((Arrow₂.δ₀ ⋙ F.truncGELT).map φ)))
        (F.truncGELTι.naturality φ).symm (F.truncGELTπ.naturality φ).symm
        (F.truncGELTδ.naturality φ).symm

@[simps!]
noncomputable def triangleObjIsoTriangleLTGEPrecompTruncGELTObj (D : Arrow₂ ι) :
    F.triangle.obj D ≅ F.triangleLTGEPrecompTruncGELT.obj D := by
  refine' Triangle.functorIsoMk _ _ (F.truncLTGELTIsoTruncGELT.app D) (Iso.refl _)
    (F.truncGEGELTIsoTruncGELT.app D) _ _ _
  · ext X
    dsimp [triangleLTGEPrecompTruncGELT]
    rw [comp_id]
    exact (F.truncLTGELTIsoTruncGELT_compatibility D X).symm
  · ext X
    dsimp [triangleLTGEPrecompTruncGELT]
    rw [id_comp]
    exact F.truncGEGELTIsoTruncGELT_compatibility D X
  · ext X
    dsimp [truncGELTδ, triangleLTGEPrecompTruncGELT, whiskeringRight₂, triangleLTGE]
    simp only [Functor.map_id, id_comp, assoc]
    rw [← Functor.map_comp, ← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app]
    erw [Functor.map_id, comp_id]

noncomputable def triangleIsoTriangleLTGEPrecompTruncGELT :
    F.triangle ≅ F.triangleLTGEPrecompTruncGELT :=
  NatIso.ofComponents F.triangleObjIsoTriangleLTGEPrecompTruncGELTObj (fun φ => by
    ext X
    · exact congr_app (F.truncLTGELTIsoTruncGELT.hom.naturality φ) X
    · dsimp [triangle, triangleLTGEPrecompTruncGELT, triangleLTGE]
      rw [comp_id, id_comp]
    · exact congr_app (F.truncGEGELTIsoTruncGELT.hom.naturality φ) X)

lemma triangle_distinguished (D : Arrow₂ ι) (X : C) :
    (F.triangle.obj D).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (F.triangleLTGEPrecompTruncGELT_distinguished D X) _
    (((F.triangleIsoTriangleLTGEPrecompTruncGELT).app D).app X)

set_option maxHeartbeats 800000 in
@[simps]
noncomputable def spectralObject (X : C) :
    SpectralObjectNew C ι where
  ω₁ :=
    { obj := fun D => (F.truncGELT.obj (Arrow.mk (D.map' 0 1))).obj X
      map := fun {D₁ D₂} f => (F.truncGELT.map
        { left := by exact ComposableArrows.app' f 0
          right := by exact ComposableArrows.app' f 1 }).app X
      map_id := fun D => by
        change ((F.truncGELT).map (𝟙 (Arrow.mk (D.map' 0 1)))).app X = _
        simp
      map_comp := fun {D₁ D₂ d₃} f g => by
        dsimp
        conv_rhs =>
          rw [← NatTrans.comp_app, ← Functor.map_comp] }
  δ' :=
    { app := fun D => (F.truncGELTδ.app (Arrow₂.mk (D.map' 0 1) (D.map' 1 2))).app X
      naturality := fun {D₁ D₂} f => by
        dsimp
        let φ : Arrow₂.mk (D₁.map' 0 1) (D₁.map' 1 2) ⟶
            Arrow₂.mk (D₂.map' 0 1) (D₂.map' 1 2) :=
          { τ₀ := f.app 0
            τ₁ := f.app 1
            τ₂ := f.app 2 }
        exact congr_app (F.truncGELTδ.naturality φ) X }
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    exact F.triangle_distinguished (Arrow₂.mk f g) X

--@[simps]
--noncomputable def spectralObject (X : C) :
--    SpectralObject C ι where
--  ω₁ := ((whiskeringRight (Arrow ι) _ _).obj ((evaluation C C).obj X)).obj F.truncGELT
--  δ := whiskerRight F.truncGELTδ ((evaluation C C).obj X)
--  distinguished' D := F.triangle_distinguished D X

end AbstractSpectralObject

end SpectralObject

end Triangulated

end CategoryTheory
