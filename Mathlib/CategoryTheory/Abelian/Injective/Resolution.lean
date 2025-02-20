/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison
-/
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Data.Set.Subsingleton
import Mathlib.Tactic.AdaptationNote

/-!
# Abelian categories with enough injectives have injective resolutions

## Main results
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

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Injective

namespace InjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

/-- Auxiliary construction for `desc`. -/
def descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
  factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

end

section Abelian

variable [Abelian C]

lemma exact₀ {Z : C} (I : InjectiveResolution Z) :
    (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
  ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

/-- Auxiliary construction for `desc`. -/
def descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
  J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]
theorem descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ I.cocomplex.d 0 1 := by
  apply J.exact₀.comp_descToInjective

/-- Auxiliary construction for `desc`. -/
def descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : InjectiveResolution Z) (n : ℕ)
    (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ'g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      J.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

/-- A morphism in `C` descends to a chain map between injective resolutions. -/
def desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.cocomplex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι := by
  ext
  simp [desc, descFOne, descFZero]

@[reassoc (attr := simp)]
lemma desc_commutes_zero {Y Z : C} (f : Z ⟶ Y)
    (I : InjectiveResolution Y) (J : InjectiveResolution Z) :
    J.ι.f 0 ≫ (desc f I J).f 0 = f ≫ I.ι.f 0 :=
  (HomologicalComplex.congr_hom (desc_commutes f I J) 0).trans (by simp)

-- Now that we've checked this property of the descent, we can seal away the actual definition.
/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0 :=
  I.exact₀.comp_descToInjective  _ _

/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroOne {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm =
      f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/-- An auxiliary definition for `descHomotopyZero`. -/
def descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroSucc {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n+2) (n+3) ≫ descHomotopyZeroSucc f n g g' w =
      f.f (n + 2) - g' ≫ J.cocomplex.d _ _ :=
  (I.exact_succ (n+1)).comp_descToInjective  _ _

/-- Any descent of the zero morphism is homotopic to zero. -/
def descHomotopyZero {Y Z : C} {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two descents of the same morphism are homotopic. -/
def descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : InjectiveResolution Y} {J : InjectiveResolution Z}
    (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))

/-- The descent of the identity morphism is homotopic to the identity cochain map. -/
def descIdHomotopy (X : C) (I : InjectiveResolution X) :
    Homotopy (desc (𝟙 X) I I) (𝟙 I.cocomplex) := by
  apply descHomotopy (𝟙 X) <;> simp

/-- The descent of a composition is homotopic to the composition of the descents. -/
def descCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (K : InjectiveResolution Z) :
    Homotopy (desc (f ≫ g) K I) (desc f J I ≫ desc g K J) := by
  apply descHomotopy (f ≫ g) <;> simp

-- We don't care about the actual definitions of these homotopies.
/-- Any two injective resolutions are homotopy equivalent. -/
def homotopyEquiv {X : C} (I J : InjectiveResolution X) :
    HomotopyEquiv I.cocomplex J.cocomplex where
  hom := desc (𝟙 X) J I
  inv := desc (𝟙 X) I J
  homotopyHomInvId := (descCompHomotopy (𝟙 X) (𝟙 X) I J I).symm.trans <| by
    simpa [id_comp] using descIdHomotopy _ _
  homotopyInvHomId := (descCompHomotopy (𝟙 X) (𝟙 X) J I J).symm.trans <| by
    simpa [id_comp] using descIdHomotopy _ _

@[reassoc (attr := simp)]
theorem homotopyEquiv_hom_ι {X : C} (I J : InjectiveResolution X) :
    I.ι ≫ (homotopyEquiv I J).hom = J.ι := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
theorem homotopyEquiv_inv_ι {X : C} (I J : InjectiveResolution X) :
    J.ι ≫ (homotopyEquiv I J).inv = I.ι := by simp [homotopyEquiv]

end Abelian

end InjectiveResolution

section

variable [Abelian C]

/-- An arbitrarily chosen injective resolution of an object. -/
abbrev injectiveResolution (Z : C) [HasInjectiveResolution Z] : InjectiveResolution Z :=
  (HasInjectiveResolution.out (Z := Z)).some

variable (C)
variable [HasInjectiveResolutions C]

/-- Taking injective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed cochain complexes and chain maps up to homotopy).
-/
def injectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.up ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (injectiveResolution X).cocomplex
  map f := (HomotopyCategory.quotient _ _).map (InjectiveResolution.desc f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descCompHomotopy
variable {C}

/-- If `I : InjectiveResolution X`, then the chosen `(injectiveResolutions C).obj X`
is isomorphic (in the homotopy category) to `I.cocomplex`. -/
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
  all_goals aesop

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

theorem exact_f_d {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (d f) (by simp)).Exact := by
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


variable [Abelian C] [EnoughInjectives C] (Z : C)

-- The construction of the injective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

/-- Auxiliary definition for `InjectiveResolution.of`. -/
def ofCocomplex : CochainComplex C ℕ :=
  CochainComplex.mk' (Injective.under Z) (Injective.syzygies (Injective.ι Z))
    (Injective.d (Injective.ι Z)) fun f => ⟨_, Injective.d f, by simp⟩

lemma ofCocomplex_d_0_1 :
    (ofCocomplex Z).d 0 1 = d (Injective.ι Z) := by
  simp [ofCocomplex]

lemma ofCocomplex_exactAt_succ (n : ℕ) :
    (ofCocomplex Z).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  dsimp [ofCocomplex, CochainComplex.mk', CochainComplex.mk, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor']
  simp only [CochainComplex.of_d]
  match n with
  | 0 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ 0).f)
  | n+1 => apply exact_f_d ((CochainComplex.mkAux _ _ _
      (d (Injective.ι Z)) (d (d (Injective.ι Z))) _ _ (n+1)).f)

instance (n : ℕ) : Injective ((ofCocomplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Injective.injective_under

/-- In any abelian category with enough injectives,
`InjectiveResolution.of Z` constructs an injective resolution of the object `Z`.
-/
irreducible_def of : InjectiveResolution Z where
  cocomplex := ofCocomplex Z
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨Injective.ι Z,
    by rw [ofCocomplex_d_0_1, cokernel.condition_assoc, zero_comp]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨exact_f_d (Injective.ι Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
          (by simp [ofCocomplex])
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · apply ofCocomplex_exactAt_succ
      · apply CochainComplex.exactAt_succ_single_obj⟩

instance (priority := 100) (Z : C) : HasInjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasInjectiveResolutions C where out _ := inferInstance

end InjectiveResolution

end CategoryTheory
