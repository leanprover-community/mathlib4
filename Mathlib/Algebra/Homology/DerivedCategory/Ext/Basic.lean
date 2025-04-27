/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
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
category. However, the category `Sheaf X.Etale AddCommGrp.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGrp.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGrp.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

-/

<<<<<<< HEAD
=======
assert_not_exists TwoSidedIdeal

>>>>>>> origin/jriou_localization_bump_deps
universe w'' w' w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ) (_ : 0 ≤ n), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_lt a b
    · refine (small_congr ?_).1 (h X Y (b - a) (by simpa))
      exact (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor _ a)).homEquiv.trans
        ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv
    · suffices Subsingleton ((Q.obj ((CochainComplex.singleFunctor C 0).obj X))⟦a⟧ ⟶
          (Q.obj ((CochainComplex.singleFunctor C 0).obj Y))⟦b⟧) from inferInstance
      constructor
      intro x y
      rw [← cancel_mono ((Q.commShiftIso b).inv.app _),
        ← cancel_epi ((Q.commShiftIso a).hom.app _)]
      have : (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧).IsStrictlyLE (-a) :=
        CochainComplex.isStrictlyLE_shift _ 0 _ _ (by omega)
      have : (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧).IsStrictlyGE (-b) :=
        CochainComplex.isStrictlyGE_shift _ 0 _ _ (by omega)
      apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _ _ (-a) (-b) (by
        omega)).elim

lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

lemma HasExt.standard : HasExt.{max u v} C := by
  letI := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _

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

end

/-- The canonical map `(X ⟶ Y) → Ext X Y 0`. -/
noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

@[simp]
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g) := by
  letI := HasDerivedCategory.standard C; ext; simp

@[simp]
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (α : Ext Z T n) :
    (mk₀ f).comp ((mk₀ g).comp α (zero_add n)) (zero_add n) =
      (mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← mk₀_comp_mk₀, comp_assoc]
  omega


variable (X Y) in
lemma mk₀_bijective : Function.Bijective (mk₀ (X := X) (Y := Y)) := by
  letI := HasDerivedCategory.standard C
  have h : (singleFunctor C 0).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e : (X ⟶ Y) ≃ Ext X Y 0 :=
    (h.homEquiv.trans (ShiftedHom.homEquiv _ (by simp))).trans homEquiv.symm
  have he : e.toFun = mk₀ := by
    ext f : 1
    dsimp [e]
    apply homEquiv.injective
    apply (Equiv.apply_symm_apply _ _).trans
    symm
    apply SmallShiftedHom.equiv_mk₀
  rw [← he]
  exact e.bijective

/-- The bijection `Ext X Y 0 ≃ (X ⟶ Y)`. -/
@[simps! symm_apply]
noncomputable def homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y) :=
  (Equiv.ofBijective _ (mk₀_bijective X Y)).symm

@[simp]
lemma mk₀_homEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (homEquiv₀ f) = f :=
  homEquiv₀.left_inv f

variable {n : ℕ}

/-! The abelian group structure on `Ext X Y n` is defined by transporting the
abelian group structure on the constructed derived category
(given by `HasDerivedCategory.standard`). This constructed derived category
is used in order to obtain most of the compatibilities satisfied by
this abelian group structure. It is then shown that the bijection
`homEquiv` between `Ext X Y n` and Hom-types in the derived category
can be promoted to an additive equivalence for any `[HasDerivedCategory C]` instance. -/

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
  letI := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
lemma comp_add (α : Ext X Y n) {m : ℕ} (β₁ β₂ : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  letI := HasDerivedCategory.standard C; ext; simp [this, add_hom']

@[simp]
lemma neg_comp (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    (-α).comp β h = -α.comp β h := by
  letI := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

@[simp]
lemma comp_neg (α : Ext X Y n) {m : ℕ} (β : Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (-β) h = -α.comp β h := by
  letI := HasDerivedCategory.standard C; ext; simp [this, neg_hom']

variable (X n) in
@[simp]
lemma zero_comp {m : ℕ} (β : Ext Y Z m) (p : ℕ) (h : n + m = p) :
    (0 : Ext X Y n).comp β h = 0 := by
  letI := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

@[simp]
lemma comp_zero (α : Ext X Y n) (Z : C) (m : ℕ) (p : ℕ) (h : n + m = p) :
    α.comp (0 : Ext Y Z m) h = 0 := by
  letI := HasDerivedCategory.standard C; ext; simp [this, zero_hom']

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

lemma mk₀_add (f g : X ⟶ Y) : mk₀ (f + g) = mk₀ f + mk₀ g := by
  letI := HasDerivedCategory.standard C; ext; simp [add_hom', ShiftedHom.mk₀]

/-- The additive bijection `Ext X Y 0 ≃+ (X ⟶ Y)`. -/
@[simps! symm_apply]
noncomputable def addEquiv₀ : Ext X Y 0 ≃+ (X ⟶ Y) where
  toEquiv := homEquiv₀
  map_add' x y := by apply
    homEquiv₀.symm.injective (by simp [mk₀_add])

@[simp]
lemma mk₀_addEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (addEquiv₀ f) = f :=
  addEquiv₀.left_inv f

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts in
lemma biprod_ext {X₁ X₂ : C} {α β : Ext (X₁ ⊞ X₂) Y n}
    (h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).comp β (zero_add n))
    (h₂ : (mk₀ biprod.inr).comp α (zero_add n) = (mk₀ biprod.inr).comp β (zero_add n)) :
    α = β := by
  letI := HasDerivedCategory.standard C
  rw [Ext.ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

variable [HasDerivedCategory.{w'} C]

variable (X Y n) in
@[simp]
lemma zero_hom : (0 : Ext X Y n).hom = 0 := by
  let β : Ext 0 Y n := 0
  have hβ : β.hom = 0 := by apply (Functor.map_isZero _ (isZero_zero C)).eq_of_src
  have : (0 : Ext X Y n) = (0 : Ext X 0 0).comp β (zero_add n) := by simp [β]
  rw [this, comp_hom, hβ, ShiftedHom.comp_zero]

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
  rw [← add_right_inj α.hom, ← add_hom, add_neg_cancel, add_neg_cancel, zero_hom]

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

variable (X Y Z) in
/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
noncomputable def bilinearComp (a b c : ℕ) (h : a + b = c) :
    Ext X Y a →+ Ext Y Z b →+ Ext X Z c :=
  AddMonoidHom.mk' (fun α ↦ AddMonoidHom.mk' (fun β ↦ α.comp β h) (by simp)) (by aesop)

/-- The postcomposition `Ext X Y a →+ Ext X Z b` with `β : Ext Y Z n` when `a + n = b`. -/
noncomputable abbrev postcomp (β : Ext Y Z n) (X : C) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →+ Ext X Z b :=
  (bilinearComp X Y Z a n b h).flip β

/-- The precomposition `Ext Y Z a →+ Ext X Z b` with `α : Ext X Y n` when `n + a = b`. -/
noncomputable abbrev precomp (α : Ext X Y n) (Z : C) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →+ Ext X Z b :=
  bilinearComp X Y Z n a b h α

end Ext

/-- Auxiliary definition for `extFunctor`. -/
@[simps]
noncomputable def extFunctorObj (X : C) (n : ℕ) : C ⥤ AddCommGrp.{w} where
  obj Y := AddCommGrp.of (Ext X Y n)
  map f := AddCommGrp.ofHom ((Ext.mk₀ f).postcomp _ (add_zero n))
  map_comp f f' := by
    ext α
    dsimp [AddCommGrp.ofHom]
    rw [← Ext.mk₀_comp_mk₀]
    symm
    apply Ext.comp_assoc
    omega

/-- The functor `Cᵒᵖ ⥤ C ⥤ AddCommGrp` which sends `X : C` and `Y : C`
to `Ext X Y n`. -/
@[simps]
noncomputable def extFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ AddCommGrp.{w} where
  obj X := extFunctorObj X.unop n
  map {X₁ X₂} f :=
    { app := fun Y ↦ AddCommGrp.ofHom (AddMonoidHom.mk'
        (fun α ↦ (Ext.mk₀ f.unop).comp α (zero_add _)) (by simp))
      naturality := fun {Y₁ Y₂} g ↦ by
        ext α
        dsimp
        symm
        apply Ext.comp_assoc
        all_goals omega }
  map_comp {X₁ X₂ X₃} f f' := by
    ext Y α
    dsimp
    rw [← Ext.mk₀_comp_mk₀]
    apply Ext.comp_assoc
    all_goals omega

section ChangeOfUniverse

namespace Ext

variable [HasExt.{w'} C] {X Y : C} {n : ℕ}

/-- Up to an equivalence, the type `Ext.{w} X Y n` does not depend on the universe `w`. -/
noncomputable def chgUniv : Ext.{w} X Y n ≃ Ext.{w'} X Y n :=
  SmallShiftedHom.chgUniv.{w', w}

lemma homEquiv_chgUniv [HasDerivedCategory.{w''} C] (e : Ext.{w} X Y n) :
    homEquiv.{w'', w'} (chgUniv.{w'} e) = homEquiv.{w'', w} e := by
  apply SmallShiftedHom.equiv_chgUniv

end Ext

end ChangeOfUniverse

end Abelian

open Abelian

variable (C) in
lemma hasExt_iff_small_ext :
    HasExt.{w'} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w'} (Ext.{w} X Y n) := by
  letI := HasDerivedCategory.standard C
  simp only [hasExt_iff, small_congr Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to ℕ using hn
    exact h X Y n

end CategoryTheory
