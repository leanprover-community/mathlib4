import Mathlib.Algebra.Homology.QuasiIso

open CategoryTheory Category Limits Preadditive

@[simp]
lemma CategoryTheory.Limits.kernel.map_id {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  simp only [← cancel_mono (kernel.ι f), lift_ι, comp_id, id_comp]

@[simp]
lemma CategoryTheory.Limits.kernel.map_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f]  [HasKernel f'] (q : Y ⟶ Y')
    (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  simp only [← cancel_mono (kernel.ι f'), lift_ι, comp_zero, zero_comp]

namespace ChainComplex

variable {C : Type*} [Category C] [Abelian C]

section

variable {K L : ChainComplex C ℕ} (φ₀ : K.X 0 ⟶ L.X 0) (φ₁ : K.X 1 ⟶ L.X 1)
  (comm₀₁ : φ₁ ≫ L.d 1 0 = K.d 1 0 ≫ φ₀)
  (ind : ∀ {n : ℕ} (φ : K.X n ⟶ L.X n) (φ' : K.X (n + 1) ⟶ L.X (n + 1))
    (_ : φ' ≫ L.d (n + 1) n = K.d (n + 1) n ≫ φ), K.X (n + 2) ⟶ L.X (n + 2))
  (hind : ∀ {n : ℕ} (φ : K.X n ⟶ L.X n) (φ' : K.X (n + 1) ⟶ L.X (n + 1))
    (h : φ' ≫ L.d (n + 1) n = K.d (n + 1) n ≫ φ), ind φ φ' h ≫ L.d _ _ = K.d _ _ ≫ φ')

namespace homMkInduction

open Classical in
noncomputable def f : ∀ n, K.X n ⟶ L.X n
  | 0 => φ₀
  | 1 => φ₁
  | n + 2 =>
      if h : f (n + 1) ≫ L.d (n + 1) n = K.d (n + 1) n ≫ f n then ind _ _ h else 0

@[simp]
lemma f_zero : f φ₀ φ₁ ind 0 = φ₀ := rfl

@[simp]
lemma f_one : f φ₀ φ₁ ind 1 = φ₁ := rfl

lemma comm (n : ℕ) : f φ₀ φ₁ ind (n + 1) ≫ L.d _ _ = K.d _ _ ≫ f φ₀ φ₁ ind n := by
  induction n with
  | zero => exact comm₀₁
  | succ n hn =>
      dsimp [f]
      rw [dif_pos hn]
      apply hind

lemma f_succ_succ (n : ℕ) :
    f φ₀ φ₁ ind (n + 2) = ind (f φ₀ φ₁ ind n) (f φ₀ φ₁ ind (n + 1))
      (comm φ₀ φ₁ comm₀₁ ind hind n) :=
  dif_pos _

end homMkInduction

noncomputable def homMkInduction : K ⟶ L where
  f := homMkInduction.f φ₀ φ₁ ind
  comm' := by
    rintro _ n rfl
    exact homMkInduction.comm φ₀ φ₁ comm₀₁ ind hind n

@[simp]
lemma homMkInduction_f_0 : (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f 0 = φ₀ := rfl

@[simp]
lemma homMkInduction_f_1 : (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f 1 = φ₁ := rfl

@[simp]
lemma homMkInduction_f (n : ℕ) :
    (homMkInduction φ₀ φ₁ comm₀₁ ind hind).f (n + 2) =
      ind ((homMkInduction φ₀ φ₁ comm₀₁ ind hind).f n)
        ((homMkInduction φ₀ φ₁ comm₀₁ ind hind).f (n + 1)) (by simp) :=
  homMkInduction.f_succ_succ φ₀ φ₁ comm₀₁ ind hind n

end

variable {F : C ⥤ C} (π : F ⟶ 𝟭 C)

variable [HasKernels C]
variable (X Y Z : C) (φ φ' : X ⟶ Y) (ψ : Y ⟶ Z)

noncomputable def leftResolution' : ChainComplex C ℕ :=
  mk' _ _ (π.app X) (fun {X₀ X₁} f =>
    ⟨_, π.app (kernel f) ≫ kernel.ι _, by simp⟩)

noncomputable def leftResolution'XZeroIso : (leftResolution' π X).X 0 ≅ X := Iso.refl _
noncomputable def leftResolution'XOneIso : (leftResolution' π X).X 1 ≅ F.obj X := Iso.refl _

@[simp]
lemma leftResolution'_d_1_0 : (leftResolution' π X).d 1 0 =
    (leftResolution'XOneIso π X).hom ≫ π.app X ≫ (leftResolution'XZeroIso π X).inv := by
  simp [leftResolution'XOneIso, leftResolution'XZeroIso, leftResolution']

noncomputable def leftResolution'XIso (n : ℕ) :
    (leftResolution' π X).X (n + 2) ≅ F.obj (kernel ((leftResolution' π X).d (n + 1) n)) :=
  mk'XIso _ _ _ _ _ _ _ rfl rfl

@[simp]
lemma leftResolution'_d (n : ℕ) :
    (leftResolution' π X).d (n + 2) (n + 1) = (leftResolution'XIso π X n).hom ≫
      π.app _ ≫ kernel.ι ((leftResolution' π X).d (n + 1) n) := by apply mk'_d

attribute [irreducible] leftResolution'

attribute [local instance] epi_comp

section

variable [∀ X, Epi (π.app X)]

instance : Epi ((leftResolution' π X).d 1 0) := by
  rw [leftResolution'_d_1_0]
  infer_instance

lemma leftResolution'_exactAt (n : ℕ) : (leftResolution' π X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp only [prev]; omega) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  convert (epi_comp (leftResolution'XIso π X n).hom (π.app _))
  rw [← cancel_mono (kernel.ι _), kernel.lift_ι]
  simp

end

variable {X Y Z}

noncomputable def leftResolution'Map : leftResolution' π X ⟶ leftResolution' π Y :=
  homMkInduction ((leftResolution'XZeroIso π X).hom ≫ φ ≫ (leftResolution'XZeroIso π Y).inv)
    ((leftResolution'XOneIso π X).hom ≫ F.map φ ≫ (leftResolution'XOneIso π Y).inv)
    (by simp) (fun {n} φ φ' h => (leftResolution'XIso π X n).hom ≫
      F.map (kernel.map _ _ φ' φ h.symm) ≫ (leftResolution'XIso π Y n).inv) (by simp)

@[simp]
lemma leftResolution'Map_f_0 :
    (leftResolution'Map π φ).f 0 =
      (leftResolution'XZeroIso π X).hom ≫ φ ≫ (leftResolution'XZeroIso π Y).inv := by
  simp [leftResolution'Map]

@[simp]
lemma leftResolution'Map_f_1 :
    (leftResolution'Map π φ).f 1 =
      (leftResolution'XOneIso π X).hom ≫ F.map φ ≫ (leftResolution'XOneIso π Y).inv := by
  simp [leftResolution'Map]

@[simp]
lemma leftResolution'Map_f (n : ℕ) :
    (leftResolution'Map π φ).f (n + 2) =
      (leftResolution'XIso π X n).hom ≫
      F.map (kernel.map _ _ ((leftResolution'Map π φ).f (n + 1))
        ((leftResolution'Map π φ).f n) (by simp)) ≫ (leftResolution'XIso π Y n).inv :=
  homMkInduction_f _ _ _ _ (by simp) _

variable (X) in
@[simp]
lemma leftResolution'Map_id :
    leftResolution'Map π (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp [hn]

@[reassoc (attr := simp)]
lemma leftResolution'Map_comp :
    leftResolution'Map π (φ ≫ ψ) = leftResolution'Map π φ ≫ leftResolution'Map π ψ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp only [leftResolution'Map_f, hn, HomologicalComplex.comp_f, assoc,
          Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left, ← F.map_comp_assoc]
        congr 2
        simp [← cancel_mono (kernel.ι _)]

variable (K L) in
@[simp]
lemma leftResolution'Map_zero [F.PreservesZeroMorphisms] :
    leftResolution'Map π (0 : K ⟶ L) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp [hn]

@[simp]
lemma leftResolution'Map_add [F.Additive] :
    leftResolution'Map π (φ + φ') = leftResolution'Map π φ + leftResolution'Map π φ' := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
      obtain _|n := n
      · simp
      · simp only [leftResolution'Map_f, hn, HomologicalComplex.add_f_apply]
        rw [← comp_add, ← add_comp, ← F.map_add]
        congr 3
        aesop_cat

@[simps]
noncomputable def leftResolution'Functor : C ⥤ ChainComplex C ℕ where
  obj := leftResolution' π
  map φ := leftResolution'Map π φ

instance [F.PreservesZeroMorphisms] : (leftResolution'Functor π).PreservesZeroMorphisms where

instance [F.Additive] : (leftResolution'Functor π).Additive where

end ChainComplex
