/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.ShortComplex.Abelian

#align_import category_theory.abelian.injective_resolution from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Main result

When the underlying category is abelian:
* `CategoryTheory.InjectiveResolution.desc`: Given `I : InjectiveResolution X` and
  `J : InjectiveResolution Y`, any morphism `X ⟶ Y` admits a descent to a chain map
  `J.cocomplex ⟶ I.cocomplex`. It is a descent in the sense that `I.ι` intertwines the descent and
  the original morphism, see `CategoryTheory.InjectiveResolution.desc_commutes`.
* `CategoryTheory.InjectiveResolution.descHomotopy`: Any two such descents are homotopic.
* `CategoryTheory.InjectiveResolution.homotopyEquiv`: Any two injective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.injectiveResolutions`: If every object admits an injective resolution, we can
  construct a functor `injectiveResolutions C : C ⥤ HomotopyCategory C`.

* `CategoryTheory.exact_f_d`: `f` and `Injective.d f` are exact.
* `CategoryTheory.InjectiveResolution.of`: Hence, starting from a monomorphism `X ⟶ J`, where `J`
  is injective, we can apply `Injective.d` repeatedly to obtain an injective resolution of `X`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ShortComplex

variable [Abelian C] {S : ShortComplex C}

def Exact.descToInjective (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.X₃ ⟶ J := by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp)]
lemma Exact.comp_descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.g ≫ hS.descToInjective f hf = f := by
  have := hS.mono_fromOpcycles
  dsimp [descToInjective ]
  simp only [← p_fromOpcycles, Category.assoc, Injective.comp_factorThru, p_descOpcycles]

end ShortComplex

open Injective

namespace InjectiveResolution
set_option linter.uppercaseLean3 false -- `InjectiveResolution`

section

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- Auxiliary construction for `desc`. -/
def descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
  factorThru (f ≫ I.ι.f 0) (J.ι.f 0)
#align category_theory.InjectiveResolution.desc_f_zero CategoryTheory.InjectiveResolution.descFZero

end

section Abelian

variable [Abelian C]

lemma exact₀ {Z : C} (I : InjectiveResolution Z) :
    (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
  ShortComplex.exact_of_f_is_kernel _ I.isLimitFork

lemma exact_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ):
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n+1) (n+2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp)
    (by simp only [CochainComplex.next]; linarith)).1 (I.cocomplex_exactAt_succ n)

/-- Auxiliary construction for `desc`. -/
def descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
  ShortComplex.Exact.descToInjective J.exact₀
    (descFZero f I J ≫ I.cocomplex.d 0 1) (by
      dsimp
      simp [← Category.assoc, descFZero])
#align category_theory.InjectiveResolution.desc_f_one CategoryTheory.InjectiveResolution.descFOne

@[simp]
theorem descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ I.cocomplex.d 0 1 := by
  apply ShortComplex.Exact.comp_descToInjective J.exact₀
#align category_theory.InjectiveResolution.desc_f_one_zero_comm CategoryTheory.InjectiveResolution.descFOne_zero_comm

/-- Auxiliary construction for `desc`. -/
def descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : ℕ)
    (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ'g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      J.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨ShortComplex.Exact.descToInjective (J.exact_succ n)
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      by apply ShortComplex.Exact.comp_descToInjective (J.exact_succ n)⟩
#align category_theory.InjectiveResolution.desc_f_succ CategoryTheory.InjectiveResolution.descFSucc

/-- A morphism in `C` descends to a chain map between injective resolutions. -/
def desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩
#align category_theory.InjectiveResolution.desc CategoryTheory.InjectiveResolution.desc

/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι := by
  ext
  simp [desc, descFOne, descFZero]
#align category_theory.InjectiveResolution.desc_commutes CategoryTheory.InjectiveResolution.desc_commutes

-- Now that we've checked this property of the descent, we can seal away the actual definition.
/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  ShortComplex.Exact.descToInjective I.exact₀ (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)
#align category_theory.InjectiveResolution.desc_homotopy_zero_zero CategoryTheory.InjectiveResolution.descHomotopyZeroZero

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0 := by
  apply ShortComplex.Exact.comp_descToInjective I.exact₀

/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  ShortComplex.Exact.descToInjective (I.exact_succ 0)
    (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1) (by
      rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
        HomologicalComplex.Hom.comm, sub_self])
#align category_theory.InjectiveResolution.desc_homotopy_zero_one CategoryTheory.InjectiveResolution.descHomotopyZeroOne

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm =
      f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1 := by
  apply ShortComplex.Exact.comp_descToInjective (I.exact_succ 0)

/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  ShortComplex.Exact.descToInjective (I.exact_succ (n+1))
    (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])
#align category_theory.InjectiveResolution.desc_homotopy_zero_succ CategoryTheory.InjectiveResolution.descHomotopyZeroSucc

@[reassoc (attr := simp)]
def comp_descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n+2) (n+3) ≫ descHomotopyZeroSucc f n g g' w =
      f.f (n + 2) - g' ≫ J.cocomplex.d _ _ := by
  apply ShortComplex.Exact.comp_descToInjective (I.exact_succ (n+1))

/-- Any descent of the zero morphism is homotopic to zero. -/
def descHomotopyZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp)
       fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩
#align category_theory.InjectiveResolution.desc_homotopy_zero CategoryTheory.InjectiveResolution.descHomotopyZero

/-- Two descents of the same morphism are homotopic. -/
def descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))
#align category_theory.InjectiveResolution.desc_homotopy CategoryTheory.InjectiveResolution.descHomotopy

/-- The descent of the identity morphism is homotopic to the identity cochain map. -/
def descIdHomotopy (X : C) (I : InjectiveResolution X) :
    Homotopy (desc (𝟙 X) I I) (𝟙 I.cocomplex) := by
  apply descHomotopy (𝟙 X) <;> simp
#align category_theory.InjectiveResolution.desc_id_homotopy CategoryTheory.InjectiveResolution.descIdHomotopy

/-- The descent of a composition is homotopic to the composition of the descents. -/
def descCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (K : InjectiveResolution Z) :
    Homotopy (desc (f ≫ g) K I) (desc f J I ≫ desc g K J) := by
  apply descHomotopy (f ≫ g) <;> simp
#align category_theory.InjectiveResolution.desc_comp_homotopy CategoryTheory.InjectiveResolution.descCompHomotopy

-- We don't care about the actual definitions of these homotopies.
/-- Any two injective resolutions are homotopy equivalent. -/
def homotopyEquiv {X : C} (I J : InjectiveResolution X) :
    HomotopyEquiv I.cocomplex J.cocomplex where
  hom := desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
  homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans <| by
    simpa [Category.id_comp] using descIdHomotopy _ _
  homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans <| by
    simpa [Category.id_comp] using descIdHomotopy _ _
#align category_theory.InjectiveResolution.homotopy_equiv CategoryTheory.InjectiveResolution.homotopyEquiv

@[reassoc (attr := simp)] -- Porting note: Originally `@[simp, reassoc.1]`
theorem homotopyEquiv_hom_ι {X : C} (I J : InjectiveResolution X) :
    I.ι ≫ (homotopyEquiv I J).hom = J.ι := by simp [homotopyEquiv]
#align category_theory.InjectiveResolution.homotopy_equiv_hom_ι CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι

@[reassoc (attr := simp)] -- Porting note: Originally `@[simp, reassoc.1]`
theorem homotopyEquiv_inv_ι {X : C} (I J : InjectiveResolution X) :
    J.ι ≫ (homotopyEquiv I J).inv = I.ι := by simp [homotopyEquiv]
#align category_theory.InjectiveResolution.homotopy_equiv_inv_ι CategoryTheory.InjectiveResolution.homotopyEquiv_inv_ι

end Abelian

end InjectiveResolution

section

variable [Abelian C]

abbrev injectiveResolution' (Z : C) [HasInjectiveResolution Z] : InjectiveResolution Z :=
  (HasInjectiveResolution.out (Z := Z)).some

/-- An arbitrarily chosen injective resolution of an object. -/
abbrev injectiveResolution (Z : C) [HasInjectiveResolution Z] : CochainComplex C ℕ :=
  (injectiveResolution' Z).cocomplex
#align category_theory.injective_resolution CategoryTheory.injectiveResolution

/-- The cochain map from cochain complex consisting of `Z` supported in degree `0`
back to the arbitrarily chosen injective resolution `injectiveResolution Z`. -/
abbrev injectiveResolution.ι (Z : C) [HasInjectiveResolution Z] :
    (CochainComplex.single₀ C).obj Z ⟶ injectiveResolution Z :=
  (injectiveResolution' Z).ι
#align category_theory.injective_resolution.ι CategoryTheory.injectiveResolution.ι

/-- The descent of a morphism to a cochain map between the arbitrarily chosen injective resolutions.
-/
abbrev injectiveResolution.desc {X Y : C} (f : X ⟶ Y) [HasInjectiveResolution X]
    [HasInjectiveResolution Y] : injectiveResolution X ⟶ injectiveResolution Y :=
  InjectiveResolution.desc f _ _
#align category_theory.injective_resolution.desc CategoryTheory.injectiveResolution.desc

@[reassoc (attr := simp)]
lemma injectiveResolution.desc_comm {X Y : C} (f : X ⟶ Y) [HasInjectiveResolution X]
    [HasInjectiveResolution Y] :
    (injectiveResolution.ι X).f 0 ≫ (injectiveResolution.desc f).f 0 =
      f ≫ (injectiveResolution.ι Y).f 0 := by
  rw [← HomologicalComplex.comp_f, InjectiveResolution.desc_commutes,
    HomologicalComplex.comp_f, CochainComplex.single₀_map_f_0]

variable (C)
variable [HasInjectiveResolutions C]

/-- Taking injective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed cochain complexes and chain maps up to homotopy).
-/
def injectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.up ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (injectiveResolution X)
  map f := (HomotopyCategory.quotient _ _).map (injectiveResolution.desc f)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descCompHomotopy
#align category_theory.injective_resolutions CategoryTheory.injectiveResolutions

variable {C}

def InjectiveResolution.iso {X : C} (I : InjectiveResolution X) :
    (injectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj I.cocomplex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

@[reassoc]
lemma InjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (injectiveResolutions C).map f ≫ J.iso.hom =
      I.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  apply HomotopyCategory.eq_of_homotopy
  apply descHomotopy f
  all_goals aesop_cat

@[reassoc]
lemma InjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    I.iso.inv ≫ (injectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ J.iso.inv := by
  rw [← cancel_mono (J.iso).hom, Category.assoc, iso_hom_naturality f I J φ comm,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

section

variable [Abelian C] [EnoughInjectives C]

--theorem exact_f_d {X Y : C} (f : X ⟶ Y) : Exact f (d f) :=
--  (Abelian.exact_iff _ _).2 <|
--    ⟨by simp, zero_of_comp_mono (ι _) <| by rw [Category.assoc, kernel.condition]⟩
--#align category_theory.exact_f_d CategoryTheory.exact_f_d

theorem exact_f_d {X Y : C} (f : X ⟶ Y) : (ShortComplex.mk f (d f) (by simp)).Exact := by
  let α : ShortComplex.mk f (cokernel.π f) (by simp) ⟶ ShortComplex.mk f (d f) (by simp) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Injective.ι _  }
  have : Epi α.τ₁ := by dsimp; infer_instance
  have : IsIso α.τ₂ := by dsimp; infer_instance
  have : Mono α.τ₃ := by dsimp; infer_instance
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  apply ShortComplex.exact_of_g_is_cokernel
  apply cokernelIsCokernel

end

namespace InjectiveResolution

/-!
Our goal is to define `InjectiveResolution.of Z : InjectiveResolution Z`.
The `0`-th object in this resolution will just be `Injective.under Z`,
i.e. an arbitrarily chosen injective object with a map from `Z`.
After that, we build the `n+1`-st object as `Injective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Injective.d`.
-/


variable [Abelian C] [EnoughInjectives C]

/-- Auxiliary definition for `InjectiveResolution.of`. -/
@[simps!]
def ofCocomplex (Z : C) : CochainComplex C ℕ :=
  CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun ⟨_, _, f⟩ =>
    ⟨Injective.syzygies f, Injective.d f, by simp⟩
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.of_cocomplex CategoryTheory.InjectiveResolution.ofCocomplex

-- Porting note: the ι field in `of` was very, very slow. To assist,
-- implicit arguments were filled in and this particular proof was broken
-- out into a separate result
theorem ofCocomplex_sq_01_comm (Z : C) :
    Injective.ι Z ≫ HomologicalComplex.d (ofCocomplex Z) 0 1 =
    HomologicalComplex.d ((CochainComplex.single₀ C).obj Z) 0 1 ≫ 0 := by
  simp only [ofCocomplex_d, eq_self_iff_true, eqToHom_refl, Category.comp_id,
    dite_eq_ite, if_true, comp_zero]
  erw [cokernel.condition_assoc, zero_comp]

lemma ofCocomplex_exactAt_succ (Z : C) (n : ℕ) : (ofCocomplex Z).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+1+1) (by simp) (by simp)]
  obtain (_|n) := n
  all_goals
    dsimp [ofCocomplex, CochainComplex.mk', HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', CochainComplex.mk, CochainComplex.of]
    simp
    apply exact_f_d

-- Porting note: still very slow but with `ofCocomplex_sq_01_comm` and
-- `exact_ofCocomplex` as separate results it is more reasonable
/-- In any abelian category with enough injectives,
`InjectiveResolution.of Z` constructs an injective resolution of the object `Z`.
-/
irreducible_def of (Z : C) : InjectiveResolution Z :=
  { cocomplex := ofCocomplex Z
    ι :=
      CochainComplex.mkHom
        ((CochainComplex.single₀ C).obj Z) (ofCocomplex Z) (Injective.ι Z) 0
          (ofCocomplex_sq_01_comm Z) fun n _ => by
          -- Porting note: used to be ⟨0, by ext⟩
            use 0
            apply HasZeroObject.from_zero_ext
    injective := by rintro (_ | _ | _ | n) <;> · apply Injective.injective_under
    hι := ⟨fun n => by
      cases n
      · rw [CochainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros]
        · exact ⟨Injective.ι_mono Z, by simpa using exact_f_d (Injective.ι Z)⟩
        all_goals rfl
      · rw [quasiIsoAt_iff_exactAt]
        apply ofCocomplex_exactAt_succ
        apply CochainComplex.single₀_exactAt⟩ }
    --exact₀ := by simpa using exact_f_d (Injective.ι Z)
    --exact := exact_ofCocomplex Z
    --mono := Injective.ι_mono Z }
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.of CategoryTheory.InjectiveResolution.of


instance (priority := 100) (Z : C) : HasInjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasInjectiveResolutions C where out _ := inferInstance

end InjectiveResolution

end CategoryTheory

namespace HomologicalComplex.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If `X` is a cochain complex of injective objects and we have a quasi-isomorphism
`f : Y[0] ⟶ X`, then `X` is an injective resolution of `Y`. -/
def HomologicalComplex.Hom.fromSingle₀InjectiveResolution (X : CochainComplex C ℕ) (Y : C)
    (f : (CochainComplex.single₀ C).obj Y ⟶ X) [QuasiIso f] (H : ∀ n, Injective (X.X n)) :
    InjectiveResolution Y where
  cocomplex := X
  ι := f
  injective := H
set_option linter.uppercaseLean3 false in
#align homological_complex.hom.homological_complex.hom.from_single₀_InjectiveResolution HomologicalComplex.Hom.HomologicalComplex.Hom.fromSingle₀InjectiveResolution

end HomologicalComplex.Hom
