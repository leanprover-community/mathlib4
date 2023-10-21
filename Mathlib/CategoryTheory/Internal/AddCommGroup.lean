import Mathlib.CategoryTheory.Internal.Basic
import Mathlib.CategoryTheory.Internal.ObjOperation

namespace CategoryTheory

open Limits

namespace Internal

open ConcreteCategory

variable {C D : Type _} [Category C] [Category D]

def addCommGroup (G : Internal AddCommGroupCat C) (X : C) :
    AddCommGroup (X ⟶ G.obj) :=
{ zero := (addCommGroupCat_zero.onInternal G).app _ PUnit.unit
  add := fun a b => (addCommGroupCat_add.onInternal G).app _ ⟨a, b⟩
  add_zero := congr_fun (congr_app (addCommGroupCat_add_zero.onInternal G) (Opposite.op X))
  zero_add := congr_fun (congr_app (addCommGroupCat_zero_add.onInternal G) (Opposite.op X))
  add_assoc := fun a b c =>
    congr_fun (congr_app (addCommGroupCat_add_assoc.onInternal G) _) ⟨a, ⟨b, c⟩⟩
  neg := (addCommGroupCat_neg.onInternal G).app (Opposite.op X)
  add_left_neg := congr_fun (congr_app (addCommGroupCat_add_left_neg.onInternal G) (Opposite.op X))
  add_comm := fun a b =>
    congr_fun (congr_app (addCommGroupCat_add_comm.onInternal G) (Opposite.op X)) ⟨a, b⟩ }

@[simp]
lemma addCommGroup_add (G : Internal AddCommGroupCat C) {X : C} (a b : X ⟶ G.obj) :
    letI := addCommGroup G X
    a + b = (addCommGroupCat_add.onInternal G).app _ ⟨a, b⟩ := rfl

@[simp]
def addCommGroup_addMonoidHom (G : Internal AddCommGroupCat C) {X Y : C} (f : X ⟶ Y) :
    letI := addCommGroup G X
    letI := addCommGroup G Y
    (Y ⟶ G.obj) →+ (X ⟶ G.obj) :=
  letI := addCommGroup G X
  letI := addCommGroup G Y
  AddMonoidHom.mk' (fun φ => f ≫ φ)
    (fun a b => (congr_fun ((addCommGroupCat_add.onInternal G).naturality f.op) ⟨a, b⟩).symm)

@[simp]
def addCommGroup_addMonoidHom' {G₁ G₂ : Internal AddCommGroupCat C} (f : G₁ ⟶ G₂) (f_obj : G₁.obj ⟶ G₂.obj)
  (h : f_obj = (Internal.objFunctor _ _).map f) (X : C) :
    letI := addCommGroup G₁ X
    letI := addCommGroup G₂ X
    (X ⟶ G₁.obj) →+ (X ⟶ G₂.obj) :=
  letI := addCommGroup G₁ X
  letI := addCommGroup G₂ X
  AddMonoidHom.mk' (fun φ => φ ≫ f_obj)
    (fun a b => (congr_fun (congr_app
      (addCommGroupCat_add.onInternal_naturality f f_obj h) _) ⟨a, b⟩).symm)

structure AddCommGroupCatObjOperations (G : C)
    [HasTerminal C] [HasBinaryProduct G G] [HasBinaryProduct G (G ⨯ G)] :=
  zero : ObjOperation₀ G
  neg : ObjOperation₁ G
  add : ObjOperation₂ G
  add_assoc : add.assoc
  add_zero : add.add_zero zero
  zero_add : add.zero_add zero
  add_comm : add.comm
  add_left_neg : add.add_left_neg neg zero

namespace AddCommGroupCatObjOperations

section

variable {G : C} [HasTerminal C] [HasBinaryProduct G G] [HasBinaryProduct G (G ⨯ G)]
  (h : AddCommGroupCatObjOperations G)

noncomputable def presheaf_obj (Y : C) : AddCommGroup (Y ⟶ G) where
  zero := ((ObjOperation₀.yonedaEquiv G) h.zero).app (Opposite.op Y) PUnit.unit
  neg := ((ObjOperation₁.yonedaEquiv G) h.neg).app (Opposite.op Y)
  add a b := ((ObjOperation₂.yonedaEquiv G) h.add).app (Opposite.op Y) ⟨a, b⟩
  add_assoc a b c := congr_fun (congr_app ((ObjOperation₂.assoc_iff h.add).1 h.add_assoc) (Opposite.op Y)) ⟨a, b, c⟩
  add_zero a := congr_fun (congr_app ((ObjOperation₂.add_zero_iff h.add h.zero).1 h.add_zero) (Opposite.op Y)) a
  zero_add a := congr_fun (congr_app ((ObjOperation₂.zero_add_iff h.add h.zero).1 h.zero_add) (Opposite.op Y)) a
  add_left_neg a := congr_fun (congr_app ((ObjOperation₂.add_left_neg_iff h.add h.neg h.zero).1 h.add_left_neg) (Opposite.op Y)) a
  add_comm a b := congr_fun (congr_app ((ObjOperation₂.comm_iff h.add).1 h.add_comm) (Opposite.op Y)) ⟨a, b⟩

@[simp]
noncomputable def presheaf_map {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    letI := h.presheaf_obj Y₁
    letI := h.presheaf_obj Y₂
    AddCommGroupCat.of (Y₂ ⟶ G) ⟶ AddCommGroupCat.of (Y₁ ⟶ G) := by
  letI := h.presheaf_obj Y₁
  letI := h.presheaf_obj Y₂
  refine' AddCommGroupCat.ofHom (AddMonoidHom.mk' (fun g => f ≫ g)
    (fun a b => (congr_fun (((ObjOperation₂.yonedaEquiv G) h.add).naturality f.op) ⟨a, b⟩).symm))

noncomputable def presheaf : Cᵒᵖ ⥤ AddCommGroupCat := by
  letI := fun (Y : C) => h.presheaf_obj Y
  exact
  { obj := fun Y => AddCommGroupCat.of (Y.unop ⟶ G)
    map := fun f => h.presheaf_map f.unop }

@[simps]
noncomputable def internal :
  Internal AddCommGroupCat C where
  obj := G
  presheaf := h.presheaf
  iso := Iso.refl _

@[simp]
lemma internal_presheaf_add {X : C} (x y : X ⟶ G) :
  @HAdd.hAdd (h.internal.presheaf.obj (Opposite.op X))
    (h.internal.presheaf.obj (Opposite.op X)) _ _ x y = prod.lift x y ≫ h.add := rfl

@[simps]
noncomputable def map (F : C ⥤ D)
    [HasTerminal D] [HasBinaryProduct (F.obj G) (F.obj G)]
    [HasBinaryProduct (F.obj G) (F.obj (G ⨯ G))]
    [HasBinaryProduct (F.obj G) (F.obj G ⨯ F.obj G)]
    [PreservesLimit (Functor.empty C) F] [PreservesLimit (pair G G) F]
    [PreservesLimit (pair G (G ⨯ G)) F] :
    AddCommGroupCatObjOperations (F.obj G) where
  zero := h.zero.map F
  neg := h.neg.map F
  add := h.add.map F
  add_assoc := h.add_assoc.map F
  add_comm := h.add_comm.map F
  add_zero := h.add_zero.map F
  zero_add := h.zero_add.map F
  add_left_neg := h.add_left_neg.map F

end

section

variable (G : Internal AddCommGroupCat C) [HasTerminal C] [HasBinaryProduct G.obj G.obj]
  [HasBinaryProduct G.obj (G.obj ⨯ G.obj)]

noncomputable def ofInternal : AddCommGroupCatObjOperations G.obj where
  zero := (ObjOperation₀.yonedaEquiv G.obj).symm (addCommGroupCat_zero.onInternal G)
  neg := (ObjOperation₁.yonedaEquiv G.obj).symm (addCommGroupCat_neg.onInternal G)
  add := (ObjOperation₂.yonedaEquiv G.obj).symm (addCommGroupCat_add.onInternal G)
  add_assoc := (ObjOperation₂.assoc_iff _).2
    (by simpa only [Equiv.apply_symm_apply] using (addCommGroupCat_add_assoc.onInternal G))
  add_zero := (ObjOperation₂.add_zero_iff _ _ ).2
    (by simpa only [Equiv.apply_symm_apply] using (addCommGroupCat_add_zero.onInternal G))
  zero_add := (ObjOperation₂.zero_add_iff _ _ ).2
    (by simpa only [Equiv.apply_symm_apply] using (addCommGroupCat_zero_add.onInternal G))
  add_comm := (ObjOperation₂.comm_iff _).2
    (by simpa only [Equiv.apply_symm_apply] using (addCommGroupCat_add_comm.onInternal G))
  add_left_neg := (ObjOperation₂.add_left_neg_iff _ _ _ ).2
    (by simpa only [Equiv.apply_symm_apply] using (addCommGroupCat_add_left_neg.onInternal G))

end

section

variable {G₁ G₂ G₃ G₄ : C} [HasTerminal C]
  [HasBinaryProduct G₁ G₁] [HasBinaryProduct G₁ (G₁ ⨯ G₁)]
  [HasBinaryProduct G₂ G₂] [HasBinaryProduct G₂ (G₂ ⨯ G₂)]
  [HasBinaryProduct G₃ G₃] [HasBinaryProduct G₃ (G₃ ⨯ G₃)]
  [HasBinaryProduct G₄ G₄] [HasBinaryProduct G₄ (G₄ ⨯ G₄)]
  (h₁ : AddCommGroupCatObjOperations G₁)
  (h₂ : AddCommGroupCatObjOperations G₂)
  (h₃ : AddCommGroupCatObjOperations G₃)
  (h₄ : AddCommGroupCatObjOperations G₄)

@[ext]
structure Hom where
  map : G₁ ⟶ G₂
  map_add : h₁.add ≫ map = prod.map map map ≫ h₂.add := by aesop_cat

namespace Hom

attribute [reassoc] map_add

@[simps]
def id : Hom h₁ h₁ where
  map := 𝟙 _

variable {h₁ h₂ h₃ h₄}

@[simps]
def comp (φ : Hom h₁ h₂) (ψ : Hom h₂ h₃) : Hom h₁ h₃ where
  map := φ.map ≫ ψ.map
  map_add := by simp only [Hom.map_add, Hom.map_add_assoc, prod.map_map_assoc]

@[simp] lemma id_comp (φ : Hom h₁ h₂) : (id h₁).comp φ = φ := by aesop_cat
@[simp] lemma comp_id (φ : Hom h₁ h₂) : φ.comp (id h₂) = φ := by aesop_cat
@[simp] lemma assoc (φ₁ : Hom h₁ h₂) (φ₂ : Hom h₂ h₃) (φ₃ : Hom h₃ h₄) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by aesop_cat

def internal (φ : Hom h₁ h₂) : h₁.internal ⟶ h₂.internal where
  app X :=
    letI := h₁.presheaf_obj X.unop
    letI := h₂.presheaf_obj X.unop
    show (X.unop ⟶ G₁) →+ (X.unop ⟶ G₂) from AddMonoidHom.mk' (fun x₁ => x₁ ≫ φ.map)
      (fun a b => by
        dsimp
        rw [internal_presheaf_add, internal_presheaf_add]
        simp only [Category.assoc, φ.map_add, prod.lift_map_assoc])
  naturality _ _ _ := by ext ; apply Category.assoc

-- simp does not work with this lemma, only erw, why?
lemma internal_app_apply (φ : Hom h₁ h₂) (X : C) (x : X ⟶ G₁) :
    φ.internal.app (Opposite.op X) x = x ≫ φ.map := rfl

section
variable {G₁ G₂ : Internal AddCommGroupCat C} [HasTerminal C]
  [HasBinaryProduct G₁.obj G₁.obj] [HasBinaryProduct G₁.obj (G₁.obj ⨯ G₁.obj)]
  [HasBinaryProduct G₂.obj G₂.obj] [HasBinaryProduct G₂.obj (G₂.obj ⨯ G₂.obj)]

@[simps]
def ofInternal (φ : G₁ ⟶ G₂) : Hom (ofInternal G₁) (ofInternal G₂) where
  map := (Internal.objFunctor _ _).map φ
  map_add := by
    dsimp only [AddCommGroupCatObjOperations.ofInternal]
    apply (ObjOperation₂.yonedaEquiv' _ _ _).injective
    rw [ObjOperation₂.yonedaEquiv'_apply_comp]
    erw [Equiv.apply_symm_apply]
    rw [← Operation₂.onInternal_naturality addCommGroupCat_add φ _ rfl]
    erw [ObjOperation₂.yonedaEquiv'_comp_apply, Equiv.apply_symm_apply]

end

end Hom

end

end AddCommGroupCatObjOperations

section

variable (C)
variable [HasTerminal C] [HasBinaryProducts C]

protected structure Ab where
  obj : C
  str : AddCommGroupCatObjOperations obj

instance : Category (Internal.Ab C) where
  Hom G₁ G₂ := AddCommGroupCatObjOperations.Hom G₁.str G₂.str
  id G := AddCommGroupCatObjOperations.Hom.id G.str
  comp f g := AddCommGroupCatObjOperations.Hom.comp f g

namespace Ab

variable {C}

@[simps]
def mk' {G : C} (h : AddCommGroupCatObjOperations G) : Internal.Ab C where
  obj := G
  str := h

@[ext]
lemma hom_ext {G₁ G₂ : Internal.Ab C} (φ φ' : G₁ ⟶ G₂) (h : φ.map = φ'.map) : φ = φ' :=
  AddCommGroupCatObjOperations.Hom.ext _ _ h

@[simp]
lemma id_map (G : Internal.Ab C) : AddCommGroupCatObjOperations.Hom.map (𝟙 G) = 𝟙 G.obj := rfl

@[simp]
lemma comp_map {G₁ G₂ G₃ : Internal.Ab C} (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃) :
  (φ ≫ ψ).map = φ.map ≫ ψ.map := rfl

variable (C)

def forget : Internal.Ab C ⥤ C where
  obj G := G.obj
  map f := f.map

namespace Equivalence

@[simps]
noncomputable def functor : Internal.Ab C ⥤ Internal AddCommGroupCat C where
  obj G :=  G.str.internal
  map φ := φ.internal
  map_id G := by
    apply NatTrans.ext
    ext ⟨X⟩ (f : X ⟶ G.obj)
    dsimp
    erw [AddCommGroupCatObjOperations.Hom.internal_app_apply]
    simp only [id_map, Category.comp_id]
  map_comp {G₁ G₂ G₃} φ φ' := by
    apply NatTrans.ext
    ext ⟨X⟩ (f : X ⟶ G₁.obj)
    dsimp
    erw [AddCommGroupCatObjOperations.Hom.internal_app_apply,
      AddCommGroupCatObjOperations.Hom.internal_app_apply,
      AddCommGroupCatObjOperations.Hom.internal_app_apply]
    simp only [comp_map, Category.assoc]

@[simps]
noncomputable def inverse : Internal AddCommGroupCat C ⥤ Internal.Ab C where
  obj G := mk' (AddCommGroupCatObjOperations.ofInternal G)
  map φ := AddCommGroupCatObjOperations.Hom.ofInternal φ
  map_id G := by
    ext
    dsimp
    apply Functor.map_id
  map_comp _ _ := by
    ext
    dsimp
    apply Functor.map_comp

noncomputable def inverseCompForgetIso :
    inverse C ⋙ Internal.Ab.forget _ ≅ objFunctor _ _ :=
  NatIso.ofComponents (fun F => Iso.refl _) (by aesop_cat)

noncomputable def functorCompObjFunctorIso :
    functor C ⋙ objFunctor _ _ ≅ Internal.Ab.forget _ :=
  NatIso.ofComponents (fun F => Iso.refl _) (fun {G₁ G₂ f} => by
    dsimp [forget]
    simp only [Category.comp_id, Category.id_comp]
    apply yoneda.map_injective
    simp only [Internal.map_objFunctor_map,
      AddCommGroupCatObjOperations.internal_obj,
      AddCommGroupCatObjOperations.internal_presheaf,
      AddCommGroupCatObjOperations.internal_iso, Iso.refl_hom,
      Iso.refl_inv, Category.id_comp]
    erw [Category.comp_id]
    rfl)

end Equivalence

/-def equivalence : Internal.Ab C ≌ Internal AddCommGroupCat C where
  functor := Equivalence.functor C
  inverse := Equivalence.inverse C
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry-/

end Ab

end

end Internal

namespace Functor

variable {C D : Type _}
  [Category C] [HasTerminal C] [HasBinaryProducts C]
  [Category D] [HasTerminal D] [HasBinaryProducts D]
  (F : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimit (empty C) F]

@[simps]
noncomputable def mapInternalAb : Internal.Ab C ⥤ Internal.Ab D where
  obj G := Internal.Ab.mk' (G.str.map F)
  map {G₁ G₂} f :=
    { map := F.map f.map
      map_add := by
        dsimp [Internal.ObjOperation₂.map]
        simp only [Category.assoc]
        have eq := F.congr_map f.map_add
        simp only [F.map_comp] at eq
        rw [eq]
        simp only [← Category.assoc]
        congr 1
        rw [← cancel_mono (PreservesLimitPair.iso F G₂.obj G₂.obj).hom,
          ← cancel_epi (PreservesLimitPair.iso F G₁.obj G₁.obj).hom]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
        simp only [PreservesLimitPair.iso_hom]
        ext
        · simp only [Category.assoc, prodComparison_fst, prod.map_fst,
          prodComparison_fst_assoc, ← F.map_comp]
        · simp only [Category.assoc, prodComparison_snd, prod.map_snd,
          prodComparison_snd_assoc, ← F.map_comp] }

noncomputable def mapInternalAddCommGroupCat :
    Internal AddCommGroupCat C ⥤ Internal AddCommGroupCat D :=
  Internal.Ab.Equivalence.inverse C ⋙ F.mapInternalAb ⋙
    Internal.Ab.Equivalence.functor D

noncomputable def mapInternalAbCompForgetIso :
    F.mapInternalAb ⋙ Internal.Ab.forget _ ≅
      Internal.Ab.forget _ ⋙ F :=
  NatIso.ofComponents (fun F => Iso.refl _) (by aesop_cat)

noncomputable def mapInternalAddCommGroupCatCompObjFunctorIso :
    F.mapInternalAddCommGroupCat ⋙ Internal.objFunctor _ _ ≅
      Internal.objFunctor _ _ ⋙ F :=
  calc (Internal.Ab.Equivalence.inverse C ⋙ F.mapInternalAb ⋙
    Internal.Ab.Equivalence.functor D) ⋙ Internal.objFunctor _ _  ≅
    Internal.Ab.Equivalence.inverse C ⋙ F.mapInternalAb ⋙ Internal.Ab.forget _ :=
      isoWhiskerLeft (Internal.Ab.Equivalence.inverse C ⋙ F.mapInternalAb)
          (Internal.Ab.Equivalence.functorCompObjFunctorIso D)
  _ ≅ Internal.Ab.Equivalence.inverse C ⋙ Internal.Ab.forget _ ⋙ F :=
      isoWhiskerLeft _ F.mapInternalAbCompForgetIso
  _ ≅ _ := isoWhiskerRight (Internal.Ab.Equivalence.inverseCompForgetIso C) F

end Functor

end CategoryTheory
