import Mathlib.CategoryTheory.Abelian.Basic

namespace CategoryTheory

open Limits Category

variable (C D : Type _) [Category C] [Category D]

/-- A short complex in a category `C` with zero morphisms is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`. -/
structure ShortComplex [HasZeroMorphisms C] where
  /-- the three objects of a `ShortComplex` -/
  {X₁ X₂ X₃ : C}
  /-- the first morphism of a `ShortComplex` -/
  f : X₁ ⟶ X₂
  /-- the second morphism of a `ShortComplex` -/
  g : X₂ ⟶ X₃
  /-- the composition of the two given morphisms is zero -/
  zero : f ≫ g = 0

namespace ShortComplex

attribute [reassoc (attr := simp)] ShortComplex.zero

variable {C}
variable [HasZeroMorphisms C]

/-- Morphisms of short complexes are the commutative diagrams of the obvious shape. -/
@[ext]
structure Hom (S₁ S₂ : ShortComplex C) where
  /-- the morphism on the left objects -/
  τ₁ : S₁.X₁ ⟶ S₂.X₁
  /-- the morphism on the middle objects -/
  τ₂ : S₁.X₂ ⟶ S₂.X₂
  /-- the morphism on the right objects -/
  τ₃ : S₁.X₃ ⟶ S₂.X₃
  /-- the left commutative square of a morphism in `ShortComplex` -/
  comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by aesop_cat
  /-- the right commutative square of a morphism in `ShortComplex` -/
  comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by aesop_cat

attribute [reassoc] Hom.comm₁₂ Hom.comm₂₃
attribute [local simp] Hom.comm₁₂ Hom.comm₂₃ Hom.comm₁₂_assoc Hom.comm₂₃_assoc

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

/-- The identity morphism of a short complex. -/
@[simps]
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃

instance : Category (ShortComplex C) :=
{ Hom := Hom,
  id := Hom.id,
  comp := Hom.comp, }

@[ext]
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) :
    f = g :=
  Hom.ext _ _ h₁ h₂ h₃

/-- A constructor for morphisms in `ShortComplex C` when the commutativity conditions
are not obvious. -/
@[simps]
def Hom.mk' {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
  (τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
  (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁ ⟶ S₂ :=
⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
  (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
  (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
  (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl

attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃

instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩

variable (S₁ S₂)

@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl

variable {S₁ S₂}

instance : HasZeroMorphisms (ShortComplex C) where

/-- The first projection functor `ShortComplex C ⥤ C`. -/
@[simps]
def π₁ : ShortComplex C ⥤ C where
  obj S := S.X₁
  map f := f.τ₁

/-- The second projection functor `ShortComplex C ⥤ C`. -/
@[simps]
def π₂ : ShortComplex C ⥤ C where
  obj S := S.X₂
  map f := f.τ₂

/-- The third projection functor `ShortComplex C ⥤ C`. -/
@[simps]
def π₃ : ShortComplex C ⥤ C where
  obj S := S.X₃
  map f := f.τ₃

instance π₁_preserves_zero_morphisms :
  Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) := { }
instance π₂_preserves_zero_morphisms :
  Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) := { }
instance π₃_preserves_zero_morphisms :
  Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) := { }

instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₁ :=
  (inferInstance : IsIso (π₁.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₂ :=
  (inferInstance : IsIso (π₂.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₃ :=
  (inferInstance : IsIso (π₃.mapIso (asIso f)).hom)

/-- The natural transformation `π₁ ⟶ π₂` induced by `S.f` for all `S : ShortComplex C`. -/
@[simps]
def π₁_to_π₂ : (π₁ : _ ⥤ C) ⟶ π₂ where
  app S := S.f

/-- The natural transformation `π₂ ⟶ π₃` induced by `S.g` for all `S : ShortComplex C`. -/
@[simps]
def π₂_to_π₃ : (π₂ : _ ⥤ C) ⟶ π₃ where
  app S := S.g

@[reassoc (attr := simp)]
lemma π₁_to_π₂_comp_π₂_to_π₃ : (π₁_to_π₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂_to_π₃ = 0 := by
  aesop_cat

variable {D}
variable [HasZeroMorphisms D]

/-- The short complex in `D` obtained by applying a functor `F : C ⥤ D` to a
short complex in `C`, assuming that `F` preserves zero morphisms. -/
@[simps]
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] : ShortComplex D :=
  ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])

/-- The morphism of short complexes `S.map F ⟶ S.map G` induced by
a natural transformation `F ⟶ G`. -/
@[simps]
def mapNatTrans {F G : C ⥤ D} [F.PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] (τ : F ⟶ G) : S.map F ⟶ S.map G where
  τ₁ := τ.app _
  τ₂ := τ.app _
  τ₃ := τ.app _

/-- The isomorphism of short complexes `S.map F ≅ S.map G` induced by
a natural isomorphism `F ≅ G`. -/
@[simps]
def mapNatIso {F G : C ⥤ D} [F.PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] (τ : F ≅ G) : S.map F ≅ S.map G where
  hom := S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv

/-- The functor `ShortComplex C ⥤ ShortComplex D` induced by a functor `C ⥤ D` which
preserves zero morphisms. -/
@[simps]
def _root_.CategoryTheory.Functor.mapShortComplex
  (F : C ⥤ D) [F.PreservesZeroMorphisms] :
  ShortComplex C ⥤ ShortComplex D where
  obj S := S.map F
  map φ :=
  { τ₁ := F.map φ.τ₁
    τ₂ := F.map φ.τ₂
    τ₃ := F.map φ.τ₃
    comm₁₂ := by
      dsimp
      simp only [← F.map_comp, φ.comm₁₂]
    comm₂₃ := by
      dsimp
      simp only [← F.map_comp, φ.comm₂₃] }

/-- A constructor for isomorphisms in the category `ShortComplex C`-/
@[simps]
def mkIso (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
  (comm₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom) (comm₂₃ : e₂.hom ≫ S₂.g = S₁.g ≫ e₃.hom) :
  S₁ ≅ S₂ where
  hom := ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩
  inv := Hom.mk' e₁.inv e₂.inv e₃.inv
    (by rw [← cancel_mono e₂.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
      ← comm₁₂, e₁.inv_hom_id_assoc])
    (by rw [← cancel_mono e₃.hom, assoc, assoc, e₃.inv_hom_id, comp_id,
        ← comm₂₃, e₂.inv_hom_id_assoc])

lemma isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f :=
  IsIso.of_iso (mkIso (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃) (by aesop_cat) (by aesop_cat))

/-- The opposite short_complex in `Cᵒᵖ` associated to a short complex in `C`. -/
@[simps]
def op : ShortComplex Cᵒᵖ :=
  mk S.g.op S.f.op (by simp only [← op_comp, S.zero] ; rfl)

/-- The opposite morphism in `short_complex Cᵒᵖ` associated to a morphism in `short_complex C` -/
@[simps]
def op_map (φ : S₁ ⟶ S₂) : S₂.op ⟶ S₁.op where
  τ₁ := φ.τ₃.op
  τ₂ := φ.τ₂.op
  τ₃ := φ.τ₁.op
  comm₁₂ := by
    dsimp
    simp only [← op_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← op_comp, φ.comm₁₂]

/-- The short_complex in `C` associated to a short complex in `Cᵒᵖ`. -/
@[simps]
def unop (S : ShortComplex Cᵒᵖ) : ShortComplex C :=
  mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero] ; rfl)

/-- The morphism in `ShortComplex C` associated to a morphism in `ShortComplex Cᵒᵖ` -/
@[simps]
def unop_map {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop where
  τ₁ := φ.τ₃.unop
  τ₂ := φ.τ₂.unop
  τ₃ := φ.τ₁.unop
  comm₁₂ := by
    dsimp
    simp only [← unop_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← unop_comp, φ.comm₁₂]

variable (C)

/-- The obvious functor `(ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ`. -/
@[simps]
def op_functor : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  obj S := (Opposite.unop S).op
  map φ := op_map φ.unop

/-- The obvious functor `ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ`. -/
@[simps]
def unop_functor : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  obj S := Opposite.op (S.unop)
  map φ := (unop_map φ).op

/-- The obvious equivalence of categories `(ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ`. -/
@[simps]
def op_equiv : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  functor := op_functor C
  inverse := unop_functor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {C}

abbrev unop_op (S : ShortComplex Cᵒᵖ) : S.unop.op ≅ S := (op_equiv C).counitIso.app S
abbrev op_unop (S : ShortComplex C) : S.op.unop ≅ S :=
  Iso.unop ((op_equiv C).unitIso.app (Opposite.op S))

end ShortComplex

end CategoryTheory
