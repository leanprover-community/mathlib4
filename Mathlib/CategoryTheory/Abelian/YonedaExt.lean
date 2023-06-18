import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext
import Mathlib.Algebra.Homology.NewHomology

namespace HomologicalComplex

open CategoryTheory Limits

variable {C ι : Type _} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {c : ComplexShape ι} [DecidableEq ι]

noncomputable def fromSingleEquiv (A : C) (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j) :
    ((single C c i).obj A ⟶ K) ≃ { f : A ⟶ K.X i // f ≫ K.d i j = 0 } where
  toFun φ := ⟨(singleObjXSelf C c i A).inv ≫ φ.f i, by simp⟩
  invFun f :=
    { f := fun k =>
        if hk : k = i then
          (((single C c i).obj A).XIsoOfEq hk).hom ≫ (singleObjXSelf C c i A).hom ≫ f.1 ≫ (K.XIsoOfEq hk).inv
        else 0
      comm' := fun k l hkl => by
        by_cases hk : k = i
        . subst hk
          dsimp
          obtain rfl : l = j := (c.next_eq' hkl).symm.trans (c.next_eq' hij)
          dsimp
          simp only [Category.comp_id, Category.id_comp, ite_true, Category.assoc, zero_comp]
          rw [f.2, comp_zero]
        . dsimp
          rw [dif_neg hk, zero_comp, zero_comp] }
  left_inv φ := by
    ext k
    by_cases hk : k = i
    . subst hk
      dsimp
      simp
    . dsimp
      rw [dif_neg hk]
      apply IsZero.eq_of_src
      dsimp
      rw [if_neg hk]
      exact Limits.isZero_zero _
  right_inv f := by
    ext
    dsimp
    simp

noncomputable def toSingleEquiv (A : C) (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j) :
    (K ⟶ (single C c j).obj A) ≃ { f : K.X j ⟶ A // K.d i j ≫ f = 0 } where
  toFun φ := ⟨φ.f j ≫ (singleObjXSelf C c j A).hom, by
    simp only [← φ.comm_assoc, single_obj_d, zero_comp, comp_zero]⟩
  invFun f :=
    { f := fun k =>
        if hk : k = j then
          (K.XIsoOfEq hk).hom ≫ f.1 ≫ (singleObjXSelf C c j A).inv ≫ (((single C c j).obj A).XIsoOfEq hk).inv
        else 0
      comm' := fun k l hkl => by
        by_cases hk : l = j
        . subst hk
          dsimp
          obtain rfl : k = i := (c.prev_eq' hkl).symm.trans (c.prev_eq' hij)
          dsimp
          simp
          rw [reassoc_of% f.2, zero_comp]
        . dsimp
          rw [dif_neg hk, comp_zero, comp_zero] }
  left_inv φ := by
    ext k
    by_cases hk : k = j
    . subst hk
      dsimp
      simp
    . dsimp
      rw [dif_neg hk]
      apply IsZero.eq_of_tgt
      dsimp
      rw [if_neg hk]
      exact Limits.isZero_zero _
  right_inv f := by
    ext
    dsimp
    simp

end HomologicalComplex

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type _} [Category C] [Abelian C]

namespace Abelian

structure IteratedExtCategory (X₁ X₂ : C) (n : ℕ) where
  K : CochainComplex C ℤ
  hK₀ : K.IsStrictlyGE 0
  hK₁ : K.IsStrictlyLE (n+2)
  hK (n : ℤ) : IsZero (K.newHomology n)
  iso₁ : K.X (n+2) ≅ X₁
  iso₂ : K.X 0 ≅ X₂

attribute [instance] IteratedExtCategory.hK₀ IteratedExtCategory.hK₁

inductive YonedaExt' (X₁ X₂ : C) : ℕ → Type _
  | ofHom (f : X₁ ⟶ X₂) : YonedaExt' X₁ X₂ 0
  | ofExt (E : IteratedExtCategory X₁ X₂ n) : YonedaExt' X₁ X₂ (n+1)

namespace IteratedExtCategory

variable {X₁ X₂ : C} {n : ℕ} (E : IteratedExtCategory X₁ X₂ n)

--X₂                                                    X₁
--K.X 0 ⟶ K.X 1 ⟶ K.X 2 ⟶ ..... ⟶ K.X n ⟶ K.X (n+1) ⟶ K.X (n+2)

noncomputable def Z.X (d : ℤ) : C := if d = 1 then 0 else E.K.X (d+n+1)

--Z.X (-(n+1)) = X₂
--Z.X (-n) = K.X 1
--Z.X (-1) = K.X n
--Z.X 0 = K.X (n+1)

noncomputable def Z.XIso (d i : ℤ) (hi : d + n + 1 = i) (hd : d ≠ 1) :
    Z.X E d ≅ E.K.X i := eqToIso (by
  dsimp [Z.X]
  rw [if_neg hd]
  congr)

noncomputable def Z.d (a b : ℤ) : Z.X E a ⟶ Z.X E b :=
  if ha : a = 1 then 0
    else if hb : b = 1 then 0
      else
        (Z.XIso E a _ rfl ha).hom ≫ E.K.d _ _ ≫ (Z.XIso E b _ rfl hb).inv

noncomputable def Z : CochainComplex C ℤ where
  X := Z.X E
  d := Z.d E
  shape i j hij := by
    dsimp [Z.d]
    split_ifs
    . rfl
    . rfl
    . rw [E.K.shape, zero_comp, comp_zero]
      dsimp at hij ⊢
      intro
      apply hij
      linarith
  d_comp_d' i j k _ _ := by
    dsimp [Z.d]
    split_ifs <;> simp

noncomputable def ZXIso₂ (d : ℤ) (hi : d + n + 1 = 0) : E.Z.X d ≅ X₂ :=
  Z.XIso E d 0 hi (fun hd => by linarith) ≪≫ E.iso₂

lemma Z_d_eq (a b : ℤ) (i j : ℤ) (hi : a + n + 1 = i)
    (hj : b + n + 1 = j) (ha : a ≠ 1) (hb : b ≠ 1): E.Z.d a b =
    (Z.XIso E a i hi ha).hom ≫ E.K.d i j ≫ (Z.XIso E b j hj hb).inv := by
  subst hi hj
  dsimp [Z, Z.d]
  rw [dif_neg ha, dif_neg hb]

lemma isZero_Z_X_of_le (a : ℤ) (ha : a ≤ -n-2) : IsZero (E.Z.X a) := by
  dsimp [Z, Z.X]
  rw [if_neg] ; swap
  . rintro rfl
    have hn : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
    linarith
  exact E.K.isZero_of_isStrictlyGE 0 _ (by linarith)

noncomputable def ZToX₁ : E.Z ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₁ :=
  (HomologicalComplex.toSingleEquiv X₁ E.Z (-1) 0 (by simp)).symm
    ⟨(Z.XIso E 0 (n+1) (by linarith) (by linarith)).hom ≫ E.K.d (n+1) (n+2) ≫ E.iso₁.hom, by
      simp [E.Z_d_eq (-1) 0 n (n+1) (by linarith) (by linarith) (by linarith) (by linarith)]⟩

noncomputable def ZToX₂ (n' : ℤ) (hn' : n' + n + 1 = 0) :
    E.Z ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) n').obj X₂ :=
  (HomologicalComplex.toSingleEquiv X₂ E.Z (n'-1) n' (by simp)).symm
    ⟨(Z.XIso E n' 0 hn' (by linarith)).hom ≫ E.iso₂.hom, by
      apply IsZero.eq_of_src
      apply E.isZero_Z_X_of_le
      linarith⟩

end IteratedExtCategory

end Abelian

end CategoryTheory
