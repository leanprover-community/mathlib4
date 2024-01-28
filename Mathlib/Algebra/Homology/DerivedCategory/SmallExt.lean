import Mathlib.Algebra.Homology.DerivedCategory.LargeExt
import Mathlib.Logic.Small.Group

universe w w' w'' v u u' u''

noncomputable def addEquivShrink (α : Type v) [AddCommGroup α] [Small.{w} α] :
    α ≃+ Shrink α where
  toEquiv := equivShrink α
  map_add' := by simp

namespace CategoryTheory

namespace ShortComplex

namespace Exact

variable {S : ShortComplex AddCommGroupCat.{v}} (hS : S.Exact)

lemma small_X₂ (h₁ : Small.{w} S.X₁) (h₃ : Small.{w} S.X₃) : Small.{w} S.X₂ := by
  rw [S.ab_exact_iff] at hS
  let g' : S.X₂ → S.g.range := fun x₂ => ⟨S.g x₂, ⟨_, rfl⟩⟩
  have hg' : Function.Surjective g' := fun ⟨x, hx⟩ => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩
  obtain ⟨s, hs⟩ : ∃ (s : S.g.range → S.X₂), ∀ x, g' (s x) = x :=
    ⟨fun x => (hg' x).choose, fun x => (hg' x).choose_spec⟩
  let π : (S.X₁ × S.g.range) → S.X₂ := fun ⟨x₁, y⟩ => S.f x₁ + s y
  have hπ : Function.Surjective π := by
    rintro x₂
    let x₃ : S.g.range := ⟨S.g x₂, ⟨_, rfl⟩⟩
    obtain ⟨x₁, hx₁⟩ := hS (x₂ - s x₃) (by
      simpa only [map_sub, sub_eq_zero, Subtype.mk.injEq] using (hs x₃).symm)
    exact ⟨⟨x₁, x₃⟩, by simp only [hx₁, sub_add_cancel]⟩
  exact small_of_surjective.{w} hπ

end Exact

end ShortComplex

open Limits

section

variable {C : Type*} [Category C]

@[simps]
def equivHomOfIsos {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃ (X' ⟶ Y') where
  toFun f := e.inv ≫ f ≫ e'.hom
  invFun g := e.hom ≫ g ≫ e'.inv
  left_inv := by aesop_cat
  right_inv := by aesop_cat

@[simps!]
def addEquivHomOfIsos [Preadditive C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := equivHomOfIsos e e'
  map_add' := by aesop_cat

end

namespace Functor

variable {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Full F] [Faithful F]

@[simps]
def equivHomOfFullOfFaithful (X Y : C) : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := by aesop_cat
  right_inv := by aesop_cat

@[simps!]
def addEquivHomOfFullOfFaithful [Preadditive C] [Preadditive D] [F.Additive] (X Y : C) :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) where
  toEquiv := F.equivHomOfFullOfFaithful X Y
  map_add' f g := by aesop_cat

end Functor

section

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{w'} D] (L : C ⥤ D) [L.IsLocalization W]
  {D' : Type u''} [Category.{w''} D'] (L' : C ⥤ D') [L'.IsLocalization W]
  (X Y : C)

namespace MorphismProperty

class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

noncomputable def localizationsEquivHom :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  ((Localization.uniq L L' W).functor.equivHomOfFullOfFaithful (L.obj X) (L.obj Y)).trans
    (equivHomOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

noncomputable def localizationsAddEquivHom [Preadditive C] [Preadditive D] [Preadditive D']
    [L.Additive] [L'.Additive] [HasFiniteProducts C] [HasFiniteProducts D] :
    (L.obj X ⟶ L.obj Y) ≃+ (L'.obj X ⟶ L'.obj Y) := by
  have : (Localization.uniq L L' W).functor.Additive := by
    rw [← Localization.functor_additive_iff L W L' (Localization.uniq L L' W).functor]
    infer_instance
  exact ((Localization.uniq L L' W).functor.addEquivHomOfFullOfFaithful (L.obj X) (L.obj Y)).trans
    (addEquivHomOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  have e := localizationsEquivHom W W.Q L X Y
  constructor
  · intro h
    have := h.small
    exact small_map e.symm
  · intro h
    exact ⟨small_map e⟩

end MorphismProperty

end

end CategoryTheory

namespace DerivedCategory

open CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} C]

noncomputable abbrev uniq : DerivedCategory.{w} C ≌ DerivedCategory.{w'} C :=
  (Localization.uniq DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.qis C (ComplexShape.up ℤ)))

instance : (uniq.{w, w'} C).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

noncomputable instance : (uniq.{w, w'} C).functor.CommShift ℤ :=
  Functor.CommShift.localized' (uniq.{w, w'} C).functor DerivedCategory.Q
    (HomologicalComplex.qis C (ComplexShape.up ℤ)) ℤ DerivedCategory.Q

noncomputable def QCompUniqFunctorIso : DerivedCategory.Q ⋙ (uniq.{w, w'} C).functor ≅ DerivedCategory.Q :=
  Localization.Lifting.iso _ (HomologicalComplex.qis C (ComplexShape.up ℤ)) _ _

instance : NatTrans.CommShift (QCompUniqFunctorIso.{w, w'} C).hom ℤ := by
  apply Functor.CommShift.localized'_compatibility

instance shiftFunctorAdditive (n : ℤ) : (shiftFunctor (DerivedCategory.{w} C) n).Additive := inferInstance

-- this is buggy...
instance [∀ (n : ℤ), (shiftFunctor (DerivedCategory.{w} C) n).Additive] :
    (uniq.{w, w'} C).functor.IsTriangulated where
  map_distinguished T hT := by
    rw [mem_distTriang_iff] at hT ⊢
    obtain ⟨K, L, f, ⟨e⟩⟩ := hT
    refine' ⟨_, _, f, ⟨(uniq.{w, w'} C).functor.mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso (QCompUniqFunctorIso.{w, w'} C)).app _⟩⟩

noncomputable def singleFunctorCompUniqFunctor (n : ℤ) :
    singleFunctor.{w} C n ⋙ (uniq.{w, w'} C).functor ≅ singleFunctor.{w'} C n :=
  isoWhiskerRight ((SingleFunctors.evaluation C (DerivedCategory.{w} C) n).mapIso
      (singleFunctorsPostCompQIso.{w} C)) (uniq.{w, w'} C).functor ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (QCompUniqFunctorIso.{w, w'} C) ≪≫
    ((SingleFunctors.evaluation C (DerivedCategory.{w'} C) n).mapIso
      (singleFunctorsPostCompQIso.{w'} C)).symm

end DerivedCategory

namespace CategoryTheory

open Category

namespace Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

class HasSmallExt : Prop where
  hasSmallLocalizedHom (X Y : C) (n : ℕ) :
    MorphismProperty.HasSmallLocalizedHom.{w}
      (HomologicalComplex.qis C (ComplexShape.up ℤ))
      ((CochainComplex.singleFunctor C 0).obj X)
      ((CochainComplex.singleFunctor C (-n)).obj Y)

lemma hasSmallExt_iff_hasSmallLocalizedHom :
    HasSmallExt.{w} C ↔
      ∀ (X Y : C) (n : ℕ), MorphismProperty.HasSmallLocalizedHom.{w}
      (HomologicalComplex.qis C (ComplexShape.up ℤ))
      ((CochainComplex.singleFunctor C 0).obj X)
      ((CochainComplex.singleFunctor C (-n)).obj Y) :=
  ⟨fun h => h.hasSmallLocalizedHom, fun h => ⟨h⟩⟩

variable {C}

noncomputable def largeExtAddEquivHom [HasDerivedCategory.{w'} C] (X Y : C) (n : ℕ) :
    LargeExt X Y n ≃+
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-n)).obj Y)) :=
  (LargeExt.addEquiv.{w'} X Y n).trans
    (addEquivHomOfIsos
      (((SingleFunctors.evaluation _ _ 0).mapIso
        (DerivedCategory.singleFunctorsPostCompQIso C)).app X)
      (((DerivedCategory.singleFunctors C).shiftIso n (-n) 0 (by linarith)).app Y ≪≫
        ((SingleFunctors.evaluation _ _ (-n : ℤ)).mapIso
        (DerivedCategory.singleFunctorsPostCompQIso C)).app Y))

variable (C)

lemma hasSmallExt_iff_small_largeExt [HasDerivedCategory.{w'} C] :
    HasSmallExt.{w} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w} (LargeExt X Y n) := by
  suffices ∀ (X Y : C) (n : ℕ), Small.{w}
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-n)).obj Y)) ↔
      Small.{w} (LargeExt X Y n) by
    simp only [hasSmallExt_iff_hasSmallLocalizedHom,
      MorphismProperty.hasSmallLocalizedHom_iff _ DerivedCategory.Q, this]
  intro X Y n
  exact small_congr (largeExtAddEquivHom X Y n).symm

instance [HasDerivedCategory.{w} C] : HasSmallExt.{w} C := by
  rw [hasSmallExt_iff_small_largeExt]
  intro X Y n
  infer_instance

instance : HasSmallExt.{max u v} C := by
  have : HasDerivedCategory.{max u v} C :=
    MorphismProperty.HasLocalization.standard _
  infer_instance

instance [HasDerivedCategory.{w'} C] [h : HasSmallExt.{w} C] (X Y : C) (n : ℕ) :
    Small.{w} (LargeExt X Y n) := by
  rw [hasSmallExt_iff_small_largeExt] at h
  infer_instance

variable {C}

def SmallExt [HasSmallExt.{w} C] (X Y : C) (n : ℕ) : Type w :=
  have : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  Shrink (LargeExt.{max u v} X Y n)

noncomputable instance [HasSmallExt.{w} C] (X Y : C) (n : ℕ) :
    AddCommGroup (SmallExt.{w} X Y n) := by
  dsimp [SmallExt]
  infer_instance

abbrev newExt [HasSmallExt.{v} C] (X Y : C) (n : ℕ) : Type v := SmallExt.{v} X Y n

noncomputable def largeExtAddEquivLargeExt [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} C]
    (X Y : C) (n : ℕ) :
    LargeExt.{w} X Y n ≃+ LargeExt.{w'} X Y n :=
  (LargeExt.addEquiv.{w} X Y n).trans
    ((ShiftedHom.map'AddEquiv (DerivedCategory.uniq.{w, w'} C).functor
      ((DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).app X)
      ((DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).app Y) (n : ℤ)).trans
      (LargeExt.addEquiv.{w'} X Y n).symm)

noncomputable def smallExtAddEquivLargeExt [HasSmallExt.{w} C] [HasDerivedCategory.{w'} C]
    (X Y : C) (n : ℕ) :
    SmallExt.{w} X Y n ≃+ LargeExt.{w'} X Y n :=
  letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  (addEquivShrink (LargeExt.{max u v} X Y n)).symm.trans
    (largeExtAddEquivLargeExt.{max u v, w'} X Y n)

variable [HasSmallExt.{w} C]

noncomputable instance (X Y Z : C) :
    HasGradedHMul (SmallExt.{w} Y Z) (SmallExt.{w} X Y) (SmallExt.{w} X Z) where
  γhmul' p q r h α β :=
    letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
    equivShrink (LargeExt.{max u v} X Z r)
      (((equivShrink (LargeExt Y Z p)).symm α) •[h]
        ((equivShrink (LargeExt X Y q)).symm β))

lemma SmallExt.γhmul_eq {X Y Z : C} {p q r : ℕ}
    (α : SmallExt.{w} Y Z p) (β : SmallExt.{w} X Y q) (h : p + q = r) :
    letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
    α •[h] β = equivShrink (LargeExt.{max u v} X Z r)
      (((equivShrink (LargeExt Y Z p)).symm α) •[h]
        ((equivShrink (LargeExt X Y q)).symm β)) := rfl

lemma largeExtAddEquivLargeExt_γhmul [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} C]
    {X Y Z : C} {p q r : ℕ}
    (α : LargeExt.{w} Y Z p) (β : LargeExt.{w} X Y q) (h : p + q = r) :
    largeExtAddEquivLargeExt.{w, w'} X Z r (α •[h] β) =
      largeExtAddEquivLargeExt.{w, w'} Y Z p α •[h] largeExtAddEquivLargeExt.{w, w'} X Y q β  := by
  obtain ⟨f, rfl⟩ := (LargeExt.equiv _ _ _).symm.surjective α
  obtain ⟨g, rfl⟩ := (LargeExt.equiv _ _ _).symm.surjective β
  rw [LargeExt.ext_iff]
  dsimp only [largeExtAddEquivLargeExt, ShiftedHom.map'AddEquiv, EquivLike.coe,
    ShiftedHom.map'Equiv, AddEquiv.trans]
  simp only [AddEquiv.toEquiv_eq_coe, Iso.app_hom, Iso.app_inv, ShiftedHom.γhmul_mk₀,
    ShiftedHom.mk₀_γhmul, AddEquiv.toEquiv_symm, Equiv.toFun_as_coe, Equiv.coe_trans,
    AddEquiv.coe_toEquiv_symm, Equiv.coe_fn_mk, Equiv.invFun_as_coe, EquivLike.coe_coe,
    AddEquiv.coe_mk, Function.comp_apply, LargeExt.addEquiv_apply, LargeExt.γhmul_hom, Nat.cast_mul,
    LargeExt.equiv_symm_apply_hom, LargeExt.addEquiv_symm_apply_hom]
  erw [← ShiftedHom.map'_comp, ShiftedHom.map'_zsmul]
  rfl

lemma smallExtAddEquivLargeExt_γhmul [HasDerivedCategory.{w'} C] {X Y Z : C} {p q r : ℕ}
    (α : SmallExt.{w} Y Z p) (β : SmallExt.{w} X Y q) (h : p + q = r) :
    smallExtAddEquivLargeExt X Z r (α •[h] β) =
      smallExtAddEquivLargeExt Y Z p α •[h] smallExtAddEquivLargeExt X Y q β  := by
  letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  dsimp [smallExtAddEquivLargeExt, addEquivShrink, AddEquiv.trans, DFunLike.coe]
  dsimp [EquivLike.coe]
  rw [SmallExt.γhmul_eq, Equiv.symm_apply_apply, largeExtAddEquivLargeExt_γhmul]

lemma smallExtAddEquivLargeExt_symm_γhmul [HasDerivedCategory.{w'} C] {X Y Z : C} {p q r : ℕ}
    (α : LargeExt.{w'} Y Z p) (β : LargeExt.{w'} X Y q) (h : p + q = r) :
    (smallExtAddEquivLargeExt X Z r).symm (α •[h] β) =
      (smallExtAddEquivLargeExt Y Z p).symm α •[h] (smallExtAddEquivLargeExt X Y q).symm β := by
  apply (smallExtAddEquivLargeExt X Z r).injective
  simp [smallExtAddEquivLargeExt_γhmul]

end Abelian

namespace ShortComplex

open CategoryTheory Abelian

namespace ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C} (hS : S.ShortExact)

lemma largeExtAddEquivLargeExt_largeExtClass
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} C] :
    largeExtAddEquivLargeExt.{w, w'} _ _ _ (largeExtClass.{w} hS) = largeExtClass.{w'} hS := by
  have := DerivedCategory.shiftFunctorAdditive.{w} C
  rw [LargeExt.ext_iff]
  dsimp [largeExtClass]
  rw [hS.eq_singleδ_iff_distinguished]
  refine' Pretriangulated.isomorphic_distinguished _ ((DerivedCategory.uniq.{w, w'} C).functor.map_distinguished _
    (ShortComplex.ShortExact.singleTriangle_distinguished.{w} hS)) _ (Iso.symm _)
  refine' Pretriangulated.Triangle.isoMk _ _
    ((DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).app S.X₁)
    ((DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).app S.X₂)
    ((DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).app S.X₃)
    _ _ _
  · exact (DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).hom.naturality S.f
  · exact (DerivedCategory.singleFunctorCompUniqFunctor.{w, w'} C 0).hom.naturality S.g
  · dsimp only [largeExtAddEquivLargeExt, ShiftedHom.map'AddEquiv, DFunLike.coe, EquivLike.coe,
      ShiftedHom.map'Equiv]
    dsimp
    simp only [ShiftedHom.map'_eq, Category.assoc, Iso.app_inv, Iso.app_hom,
      ShiftedHom.γhmul_mk₀, ShiftedHom.mk₀_γhmul]
    erw [Iso.hom_inv_id_app_assoc]
    rw [ShiftedHom.map_eq, assoc]
    rfl

noncomputable def smallExtClass [HasSmallExt.{w} C] : SmallExt.{w} S.X₃ S.X₁ 1 :=
  letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  (smallExtAddEquivLargeExt.{w, max u v} S.X₃ S.X₁ 1).symm hS.largeExtClass

lemma smallExtAddEquivLargeExt_smallExtClass [HasDerivedCategory.{w'} C] [HasSmallExt.{w} C] :
    smallExtAddEquivLargeExt.{w, w'} _ _ _ (smallExtClass.{w} hS) = largeExtClass.{w'} hS := by
  letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  have h : smallExtAddEquivLargeExt.{w, w'} _ _ _ (smallExtClass.{w} hS) =
      (largeExtAddEquivLargeExt.{max u v, w'} S.X₃ S.X₁ 1)
      ((largeExtAddEquivLargeExt.{max u v, max u v} S.X₃ S.X₁ 1).symm
      (largeExtClass.{max u v} hS)) := by
    dsimp only [smallExtAddEquivLargeExt, smallExtClass, AddEquiv.trans, AddEquiv.symm,
      DFunLike.coe, EquivLike.coe, Equiv.toFun, addEquivShrink, Equiv.symm, Equiv.trans,
      Function.comp]
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
      Equiv.toFun_as_coe, Equiv.symm_apply_apply, AddEquiv.coe_toEquiv]
  rw [h, ← largeExtAddEquivLargeExt_largeExtClass.{max u v, max u v} hS,
    AddEquiv.symm_apply_apply, largeExtAddEquivLargeExt_largeExtClass.{max u v, w'} hS]

end ShortExact

end ShortComplex

end CategoryTheory
