import Mathlib.Algebra.Homology.HomologicalComplex

open CategoryTheory Category Limits

namespace ChainComplex

variable {C : Type*} [Category C] [Preadditive C]

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

namespace LeftResolution

variable [HasKernels C]
variable (X Y : C) (φ : X ⟶ Y)

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

variable {X Y}

noncomputable def leftResolution'Map : leftResolution' π X ⟶ leftResolution' π Y :=
  homMkInduction ((leftResolution'XZeroIso π X).hom ≫ φ ≫ (leftResolution'XZeroIso π Y).inv)
    ((leftResolution'XOneIso π X).hom ≫ F.map φ ≫ (leftResolution'XOneIso π Y).inv)
    (by simp) (fun {n} φ φ' h => (leftResolution'XIso π X n).hom ≫
      F.map (kernel.map _ _ φ' φ h.symm) ≫ (leftResolution'XIso π Y n).inv) (by simp)

end LeftResolution

end ChainComplex
