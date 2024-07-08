/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Ext groups in abelian categories

Let `C` be an abelian category (with `C : Type u` and `Category.{v} C`).
In this file, we introduce the assumption `HasExt.{w} C` which asserts
that morphisms between single complexes in arbitrary degrees in
the derived category of `C` are `w`-small. Under this assumption,
we define `Ext.{w} X Y n : Type w` as shrunk versions of suitable
types of morphisms in the derived category. In particular, when `C` has
enough projectives or enough injectives, the property `HasExt.{v} C`
shall hold (TODO).

Note: in certain situations, `w := v` shall be the preferred
choice of universe (e.g. if `C := ModuleCat.{v} R` with `R : Type v`).
However, in the development of the API for Ext-groups, it is important
to keep a larger degree of generality for universes, as `w < v`
may happen in certain situations. Indeed, if `X : Scheme.{u}`,
then the underlying category of the étale site of `X` shall be a large
category. However, the category `Sheaf X.Etale AddCommGroupCat.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGroupCat.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGroupCat.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

## TODO
* compute `Ext X Y 0`
* define the class in `Ext S.X₃ S.X₁ 1` of a short exact short complex `S`
* construct the long exact sequences of `Ext`.

-/

universe w' w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

-- TODO: when the canonical t-structure is formalized, replace `n : ℤ` by `n : ℕ`
lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    refine (small_congr ?_).1 (h X Y (b - a))
    exact (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor _ a)).homEquiv.trans
      ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv

lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

variable {C}

variable [HasExt.{w} C]

namespace Abelian

/-- A Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w} C]`. -/
def Ext (X Y : C) (n : ℕ) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)

namespace Ext

variable {X Y Z T : C}

/-- The composition of `Ext`. -/
noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by omega)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by omega) =
      α.comp (β.comp γ h₂₃) (by omega) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by omega)

@[simp]
lemma comp_assoc_of_second_deg_zero
    {a₁ a₃ a₁₃ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T a₃)
    (h₁₃ : a₁ + a₃ = a₁₃) :
    (α.comp β (add_zero _)).comp γ h₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃ := by
  apply comp_assoc
  omega

@[simp]
lemma comp_assoc_of_third_deg_zero
    {a₁ a₂ a₁₂ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T 0)
    (h₁₂ : a₁ + a₂ = a₁₂) :
    (α.comp β h₁₂).comp γ (add_zero _) = α.comp (β.comp γ (add_zero _)) h₁₂ := by
  apply comp_assoc
  omega

section

variable [HasDerivedCategory.{w'} C]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bijection
between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
noncomputable def homEquiv {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X)
      ((singleFunctor C 0).obj Y) (n : ℤ) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) Q

/-- The morphism in the derived category which corresponds to an element in `Ext X Y a`. -/
noncomputable abbrev hom {a : ℕ} (α : Ext X Y a) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (a : ℤ) :=
  homEquiv α

@[simp]
lemma comp_hom {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by omega) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

lemma ext_iff {n : ℕ} {α β : Ext X Y n} : α = β ↔ α.hom = β.hom :=
  ⟨fun h ↦ by rw [h], ext⟩

end

/-- The canonical map `(X ⟶ Y) → Ext X Y 0`. -/
noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

@[simp 1100]
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g) := by
  letI := HasDerivedCategory.standard C; ext; simp

@[simp 1100]
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (α : Ext Z T n) :
    (mk₀ f).comp ((mk₀ g).comp α (zero_add n)) (zero_add n) =
      (mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← mk₀_comp_mk₀, comp_assoc]
  omega

variable {n : ℕ}

/-! The abelian group structure on `Ext X Y n` is defined by transporting the
abelian group structure on the constructed derived category
(given by `HasDerivedCategory.standard`). This constructed derived category
is used in order to obtain most of the compatibilities satisfied by
this abelian group structure. It is then shown that the bijection
`homEquiv` between `Ext X Y n` and Hom-types in the derived category
cane be promoted to an additive equivalence for any `[HasDerivedCategory C]` instance. -/

noncomputable instance : AddCommGroup (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  homEquiv.addCommGroup

/-- The map from `Ext X Y n` to a `ShiftedHom` type in the *constructed* derived
category given by `HasDerivedCategory.standard`: this definition is introduced
only in order to prove properties of the abelian group structure on `Ext`-groups.
Do not use this definition: use the more general `hom` instead. -/
noncomputable abbrev hom' (α : Ext X Y n) :
  letI := HasDerivedCategory.standard C
  ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) :=
  letI := HasDerivedCategory.standard C
  α.hom

private lemma add_hom' (α β : Ext X Y n) : (α + β).hom' = α.hom' + β.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

private lemma neg_hom' (α : Ext X Y n) : (-α).hom' = -α.hom' :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

variable (X Y n) in
private lemma zero_hom' : (0 : Ext X Y n).hom' = 0 :=
  letI := HasDerivedCategory.standard C
  homEquiv.symm.injective (Equiv.symm_apply_apply _ _)

@[simp]
lemma add_comp (α₁ α₂ : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  letI := HasDerivedCategory.standard C; ext; simp [add_hom']

@[simp]
lemma comp_add (α : Ext X Y n) {m : ℕ} (β₁ β₂ : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  letI := HasDerivedCategory.standard C; ext; simp [add_hom']

@[simp]
lemma neg_comp (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    (-α).comp β h = -α.comp β h := by
  letI := HasDerivedCategory.standard C; ext; simp [neg_hom']

@[simp]
lemma comp_neg (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (-β) h = -α.comp β h := by
  letI := HasDerivedCategory.standard C; ext; simp [neg_hom']

variable (X n) in
@[simp]
lemma zero_comp {m : ℕ} (β : Ext Y Z m) (p : ℕ) (h : n + m = p) :
    (0 : Ext X Y n).comp β h = 0 := by
  letI := HasDerivedCategory.standard C; ext; simp [zero_hom']

@[simp]
lemma comp_zero (α : Ext X Y n) (Z : C) (m : ℕ) (p : ℕ) (h : n + m = p) :
    α.comp (0 : Ext Y Z m) h = 0 := by
  letI := HasDerivedCategory.standard C; ext; simp [zero_hom']

@[simp]
lemma mk₀_id_comp (α : Ext X Y n) :
    (mk₀ (𝟙 X)).comp α (zero_add n) = α := by
  letI := HasDerivedCategory.standard C; ext; simp

@[simp]
lemma comp_mk₀_id (α : Ext X Y n) :
    α.comp (mk₀ (𝟙 Y)) (add_zero n) = α := by
  letI := HasDerivedCategory.standard C; ext; simp

variable (X Y) in
@[simp]
lemma mk₀_zero : mk₀ (0 : X ⟶ Y) = 0 := by
  letI := HasDerivedCategory.standard C; ext; simp [zero_hom']

section

variable [HasDerivedCategory.{w'} C]

variable (X Y n) in
@[simp]
lemma zero_hom : (0 : Ext X Y n).hom = 0 := by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this, comp_hom, hβ, ShiftedHom.comp_zero]

attribute [local instance] preservesBinaryBiproductsOfPreservesBiproducts

lemma biprod_ext {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n}
    (h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).comp β (zero_add n))
    (h₂ : (mk₀ biprod.inr).comp α (zero_add n) = (mk₀ biprod.inr).comp β (zero_add n)) :
    α = β := by
  letI := HasDerivedCategory.standard C
  rw [ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

@[simp]
lemma add_hom (α β : Ext X Y n) : (α + β).hom = α.hom + β.hom := by
  let α' : Ext (X ⊞ X) Y n := (mk₀ biprod.fst).comp α (zero_add n)
  let β' : Ext (X ⊞ X) Y n := (mk₀ biprod.snd).comp β (zero_add n)
  have eq₁ : α + β = (mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (α' + β') (zero_add n) := by
    simp [α', β']
  have eq₂ : α' + β' = homEquiv.symm (α'.hom + β'.hom) := by
    apply biprod_ext
    all_goals ext; simp [α', β', ← Functor.map_comp]
  simp only [eq₁, eq₂, comp_hom, Equiv.apply_symm_apply, ShiftedHom.comp_add]
  congr
  · dsimp [α']
    rw [comp_hom, mk₀_hom, mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_fst, Functor.map_id, ShiftedHom.mk₀_id_comp]
  · dsimp [β']
    rw [comp_hom, mk₀_hom, mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_snd, Functor.map_id, ShiftedHom.mk₀_id_comp]

lemma neg_hom (α : Ext X Y n) : (-α).hom = -α.hom := by
  rw [← add_right_inj α.hom, ← add_hom, add_right_neg, add_right_neg, zero_hom]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the additive
bijection between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
noncomputable def homAddEquiv {n : ℕ} :
    Ext.{w} X Y n ≃+
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  toEquiv := homEquiv
  map_add' := by simp

@[simp]
lemma homAddEquiv_apply (α : Ext X Y n) : homAddEquiv α = α.hom := rfl

end

@[simps!]
noncomputable def postcomp (β : Ext Y Z n) (X : C) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →+ Ext X Z b :=
  AddMonoidHom.mk' (fun α => α.comp β h) (by simp)

@[simps!]
noncomputable def precomp (α : Ext X Y n) (Z : C) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →+ Ext X Z b :=
  AddMonoidHom.mk' (fun β => α.comp β h) (by simp)

end Ext

end Abelian

open Abelian

namespace ShortComplex

variable (S : ShortComplex C)

lemma ext_mk₀_f_comp_ext_mk₀_g : (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0 := by simp

namespace ShortExact

variable {S}
variable (hS : S.ShortExact)

/-- The class in `Ext S.X₃ S.X₁ 1` that is attached to a short exact
short complex `S` in an abelian category. -/
noncomputable def extClass : Ext.{w} S.X₃ S.X₁ 1 := by
  let W := (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  let S' := S.map (CochainComplex.singleFunctor C 0)
  have hS' : S'.ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  let K := CochainComplex.mappingCone S'.f
  let w : K ⟶ S'.X₃ := CochainComplex.mappingCone.descShortComplex S'
  have hw : W w := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  let δ : K ⟶ S'.X₁⟦(1 : ℤ)⟧ := (CochainComplex.mappingCone.triangle S'.f).mor₃
  have : HasSmallLocalizedShiftedHom.{w} W ℤ S'.X₃ S'.X₁ := by
    dsimp [W, S']
    infer_instance
  have : HasSmallLocalizedHom.{w} W S'.X₃ K := by
    rw [Localization.hasSmallLocalizedHom_iff_target W S'.X₃ w hw]
    dsimp [W, S']
    apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)
  have : HasSmallLocalizedShiftedHom.{w} W ℤ K S'.X₁ := by
    rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ w hw S'.X₁]
    dsimp [W, S']
    infer_instance
  change SmallHom W S'.X₃ (S'.X₁⟦(1 : ℤ)⟧)
  exact (SmallHom.mkInv w hw).comp (SmallHom.mk W δ)

@[simp]
lemma extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ := by
  let W := (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  let S' := S.map (CochainComplex.singleFunctor C 0)
  have hS' : S'.ShortExact := hS.map_of_exact (HomologicalComplex.single _ _ _)
  let K := CochainComplex.mappingCone S'.f
  let w : K ⟶ S'.X₃ := CochainComplex.mappingCone.descShortComplex S'
  have hw : W w := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  let δ : K ⟶ S'.X₁⟦(1 : ℤ)⟧ := (CochainComplex.mappingCone.triangle S'.f).mor₃
  have : HasSmallLocalizedShiftedHom.{w} W ℤ S'.X₃ S'.X₁ := by
    dsimp [W, S']
    infer_instance
  have : HasSmallLocalizedHom.{w} W S'.X₃ K := by
    rw [Localization.hasSmallLocalizedHom_iff_target W S'.X₃ w hw]
    dsimp [W, S']
    apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)
  have : HasSmallLocalizedShiftedHom.{w} W ℤ K S'.X₁ := by
    rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ w hw S'.X₁]
    dsimp [W, S']
    infer_instance
  change SmallShiftedHom.equiv W Q ((SmallHom.mkInv w hw).comp (SmallHom.mk W δ)) = _
  dsimp [SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp, Iso.homToEquiv_apply]
  rw [SmallHom.equiv_mkInv, SmallHom.equiv_mk]
  simp
  dsimp [singleδ, triangleOfSESδ, δ, w, S']
  rw [Category.assoc, singleFunctorsPostcompQIso_hom_hom,
    singleFunctorsPostcompQIso_inv_hom]
  erw [Category.id_comp, Functor.map_id, Category.comp_id]
  rfl

@[simp]
lemma comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]
lemma extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

end ShortExact

end ShortComplex

end CategoryTheory
