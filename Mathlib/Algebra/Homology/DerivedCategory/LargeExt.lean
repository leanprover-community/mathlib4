/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Ext groups in abelian categories

If `C` is an abelian category, we define types `LargeExt X Y n`
for objects `X` and `Y` in `C` and `n : ℕ` as a single-field structure
containing a shifted morphism in the derived category of `C`.
Then, we need to introduce an auxiliary universe `w` and the
assumption `HasDerivedCategory.{w} C` so that `LargeExt X Y n : Type w`.
(When using the constructed localized category, we may use `w := max u v`.)

Any short exact short complex `S` gives a class in `LargeExt S.X₃ S.X₁ 1`
(`ShortComplex.ShortExact.largeExtClass`), and we construct the
associated long exact sequences for `LargeExt`.

## TODO

* construct the equivalence `LargeExt X Y 0 ≃ (X ⟶ Y)`
* define the contravariant long exact sequence of `LargeExt`
* shrink the types `LargeExt X Y n` in order to define `SmallExt X Y n : Type w'`
when we know that the `Ext`-groups are `w'`-small, and redefine
`Ext := SmallExt.{v}` (which will work when `C` has enough projectives
or enough injectives).

-/

universe w v u

namespace CategoryTheory

open Category Limits DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace Abelian

variable (X Y Z T : C) (n : ℕ)

/-- The Ext-groups in an abelian category `C`, defined as a `Type w` when
`[HasDerivedCategory.{w} C]`. -/
@[ext]
structure LargeExt : Type w where
  /-- a shifted hom in the derived category -/
  hom : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)

namespace LargeExt

/-- The bijection between `LargeExt X Y n` and shifted homs in the derived category. -/
@[simps]
def equiv :
    LargeExt X Y n ≃
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  toFun := hom
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (LargeExt X Y n) := (equiv X Y n).addCommGroup

@[simp]
lemma add_hom (x y : LargeExt X Y n) : (x + y).hom = x.hom + y.hom := rfl

@[simp]
lemma sub_hom (x y : LargeExt X Y n) : (x - y).hom = x.hom - y.hom := rfl

@[simp]
lemma neg_hom (x : LargeExt X Y n) : (-x).hom = -x.hom := rfl

@[simp]
lemma zero_hom (X Y : C) (n : ℕ) : (0 : LargeExt X Y n).hom = 0 := rfl

@[simp]
lemma zsmul_hom (a : ℤ) (x : LargeExt X Y n) :
    (a • x).hom = a • x.hom := rfl

/-- The additive bijection between `LargeExt X Y n` and shifted homs in the derived category. -/
@[simps!]
def addEquiv :
    LargeExt X Y n ≃+
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  toEquiv := equiv X Y n
  map_add' := by simp

variable {X Y Z T}

/-- The canonical map `(X ⟶ Y) → LargeExt X Y 0`: -/
@[simps]
noncomputable def ofHom (f : X ⟶ Y) : LargeExt X Y 0 :=
  mk (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) rfl ((singleFunctor C 0).map f))

/-- The composition on `Ext`-groups. -/
@[simps]
noncomputable def comp {a b c : ℕ} (α : LargeExt X Y a) (β : LargeExt Y Z b) (h : a + b = c) :
    LargeExt X Z c where
  hom := α.hom.comp β.hom (by omega)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ}
    (α : LargeExt X Y a₁) (β : LargeExt Y Z a₂) (γ : LargeExt Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show _ = a by omega) =
      α.comp (β.comp γ h₂₃) (by omega) := by
  ext
  dsimp
  apply ShiftedHom.comp_assoc
  omega

@[simp]
lemma comp_add {a b c : ℕ} (α : LargeExt X Y a) (β₁ β₂ : LargeExt Y Z b) (h : a + b = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by aesop

@[simp]
lemma add_comp {a b c : ℕ} (α₁ α₂ : LargeExt X Y a) (β : LargeExt Y Z b) (h : a + b = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by aesop

@[simp]
lemma ofHom_id_comp {a : ℕ} (α : LargeExt X Y a) :
    (ofHom (𝟙 X)).comp α (zero_add a) = α := by aesop

@[simp]
lemma comp_ofHom_id {a : ℕ} (α : LargeExt X Y a) :
    α.comp (ofHom (𝟙 Y)) (add_zero a) = α := by aesop

lemma ofHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (add_zero _) := by
  ext
  dsimp
  rw [Functor.map_comp]
  symm
  apply ShiftedHom.mk₀_comp_mk₀

/-- The postcomposition with `β : LargeExt Y Z q` as an additive map. -/
@[simps! apply]
noncomputable def postcomp {Y Z : C} {q : ℕ} (β : LargeExt Y Z q)
    (X : C) (p : ℕ) (n : ℕ) (hpq : p + q = n) :
    LargeExt X Y p →+ LargeExt X Z n :=
  AddMonoidHom.mk' (fun α => α.comp β hpq) (by simp)

/-- The precomposition with `α : LargeExt X Y p` as an additive map. -/
@[simps! apply]
noncomputable def precomp {X Y : C} {p : ℕ} (α : LargeExt X Y p)
    (Z : C) (q : ℕ) (n : ℕ) (hpq : p + q = n) :
    LargeExt Y Z q →+ LargeExt X Z n :=
  AddMonoidHom.mk' (fun β => α.comp β hpq) (by simp)

/-- Auxiliary definition for `LargeExtFunctor`. -/
noncomputable def LargeExtFunctor.obj (n : ℕ) (X : C) : C ⥤ Ab where
  obj := fun Y => AddCommGroupCat.of (LargeExt X Y n)
  map := fun g => postcomp (ofHom g) _ _ _ (add_zero n)
  map_id _ := by ext; simp
  map_comp _ _ := by
    ext
    simp only [ofHom_comp]
    symm
    apply comp_assoc
    all_goals omega

variable (C)

/-- The `Ext`-groups in degree `n : ℕ`, as a bifunctor `Cᵒᵖ ⥤ C ⥤ Ab.{w}`. -/
noncomputable def LargeExtFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Ab.{w} where
  obj X := LargeExtFunctor.obj n X.unop
  map {X₁ X₂} f :=
    { app := fun Y => AddCommGroupCat.ofHom (precomp (ofHom f.unop) _ _ _ (zero_add n))
      naturality := by
        intros
        ext
        symm
        dsimp [LargeExtFunctor.obj]
        apply comp_assoc
        all_goals omega }
  map_id _ := by ext; simp [LargeExtFunctor.obj]
  map_comp _ _ := by
    ext
    dsimp [LargeExtFunctor.obj]
    simp only [ofHom_comp]
    apply comp_assoc
    all_goals omega

end LargeExt

end Abelian

open Abelian Pretriangulated

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

/-- The class in `LargeExt S.X₃ S.X₁ 1` that is attached to a short exact
short complex `S` in an abelian category. -/
@[simps]
noncomputable def largeExtClass : LargeExt S.X₃ S.X₁ 1 :=
  LargeExt.mk hS.singleδ

@[simp]
lemma comp_largeExtClass : (LargeExt.ofHom S.g).comp hS.largeExtClass (zero_add 1) = 0 := by
  have eq := comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished
  dsimp at eq
  ext
  dsimp [ShiftedHom.comp, ShiftedHom.mk₀]
  rw [assoc, ← NatTrans.naturality_assoc]
  dsimp
  rw [reassoc_of% eq, zero_comp]

@[simp]
lemma largeExtClass_comp : hS.largeExtClass.comp (LargeExt.ofHom S.f) (add_zero 1) = 0 := by
  have eq := comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished
  dsimp at eq
  ext
  dsimp [ShiftedHom.comp, ShiftedHom.mk₀]
  simp only [Functor.map_comp, assoc, reassoc_of% eq, zero_comp]

end ShortExact

end ShortComplex

namespace Abelian

namespace LargeExt

open ComposableArrows

section CovariantExactSequence

variable (A : C) {S : ShortComplex C} (hS : S.ShortExact)

/-- Given a short exact short complex `S` in an abelian category `C` and `A : C`,
this is the covariant (exact) sequence of `LargeExt` with six terms which starts by:
`LargeExact A S.X₁ n₀ ⟶ LargeExact A S.X₂ n₀ ⟶ LargeExact A S.X₃ n₀ → LargeExact A S.X₁ n₁ ⟶ ` -/
@[simp]
noncomputable def covariantSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGroupCat.{w} 5 :=
  ComposableArrows.mk₅
    (AddCommGroupCat.ofHom (postcomp (ofHom S.f) A n₀ n₀ (add_zero n₀)))
    (AddCommGroupCat.ofHom (postcomp (ofHom S.g) A n₀ n₀ (add_zero n₀)))
    (AddCommGroupCat.ofHom (postcomp hS.largeExtClass A n₀ n₁ h))
    (AddCommGroupCat.ofHom (postcomp (ofHom S.f) A n₁ n₁ (add_zero n₁)))
    (AddCommGroupCat.ofHom (postcomp (ofHom S.g) A n₁ n₁ (add_zero n₁)))

/-- The covariant (exact) sequence of `LargeExt` identifies to the homology sequence
of the homological functor `(preadditiveCoyoneda.obj (Opposite.op ((singleFunctor C 0).obj A)))`
applied to the distinguished triangle `hS.singleTriangle`. -/
noncomputable def covariantSequenceIso (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    covariantSequence A hS n₀ n₁ h ≅
      (preadditiveCoyoneda.obj
          (Opposite.op ((singleFunctor C 0).obj A))).homologySequenceComposableArrows₅
        hS.singleTriangle n₀ n₁ (by omega) :=
  isoMk₅
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₁ n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₂ n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₃ n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₁ n₁))
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₂ n₁))
    (AddEquiv.toAddCommGroupCatIso (addEquiv A S.X₃ n₁))
    (by ext; apply ShiftedHom.comp_mk₀) (by ext; apply ShiftedHom.comp_mk₀)
    (by ext; symm; apply Category.assoc)
    (by ext; apply ShiftedHom.comp_mk₀) (by ext; apply ShiftedHom.comp_mk₀)

lemma covariantSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (covariantSequence A hS n₀ n₁ h).Exact := by
  rw [exact_iff_of_iso (covariantSequenceIso A hS n₀ n₁ h)]
  apply Functor.homologySequenceComposableArrows₅_exact _ _ (hS.singleTriangle_distinguished)

variable {A}

/-- Given a short exact short complex `S` in an abelian category `C` and `A : C`,
this is the exactness of
`LargeExact A S.X₃ n₀ ⟶ LargeExact A S.X₁ n₁ ⟶ LargeExact A S.X₂ n₁`
when `n₀ + 1 = n₁`. -/
lemma covariant_sequence_exact₁
    {n₁ : ℕ} (x₁ : LargeExt A S.X₁ n₁) (hx₁ : x₁.comp (ofHom S.f) (add_zero n₁) = 0)
    (n₀ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ (x₃ : LargeExt A S.X₃ n₀), x₃.comp hS.largeExtClass h = x₁ :=
  (ShortComplex.ab_exact_iff _).1
    ((covariantSequence_exact A hS n₀ n₁ h).exact 2) x₁ hx₁

/-- Given a short exact short complex `S` in an abelian category `C` and `A : C`,
this is the exactness of
`LargeExact A S.X₁ n ⟶ LargeExact A S.X₂ n ⟶ LargeExact A S.X₃ n` -/
lemma covariant_sequence_exact₂
    {n : ℕ} (x₂ : LargeExt A S.X₂ n) (hx₂ : x₂.comp (ofHom S.g) (add_zero n) = 0) :
    ∃ (x₁ : LargeExt A S.X₁ n), x₁.comp (ofHom S.f) (add_zero n) = x₂ :=
  (ShortComplex.ab_exact_iff _).1
    ((covariantSequence_exact A hS n _ rfl).exact 0) x₂ hx₂

/-- Given a short exact short complex `S` in an abelian category `C` and `A : C`,
this is the exactness of
`LargeExact A S.X₂ n₀ ⟶ LargeExact A S.X₃ n₀ → LargeExact A S.X₁ n₁`
when `n₀ + 1 = n₁`. -/
lemma covariant_sequence_exact₃
    {n₀ : ℕ} (x₃ : LargeExt A S.X₃ n₀) {n₁ : ℕ} (h : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.largeExtClass h = 0) :
    ∃ (x₂ : LargeExt A S.X₂ n₀), x₂.comp (ofHom S.g) (add_zero n₀) = x₃ :=
  (ShortComplex.ab_exact_iff _).1
    ((covariantSequence_exact A hS n₀ n₁ h).exact 1) x₃ hx₃

end CovariantExactSequence

section ContravariantExactSequence

variable (B : C) {S : ShortComplex C} (hS : S.ShortExact)

/-- Given a short exact short complex `S` in an abelian category `C` and `B : C`,
this is the contravariant (exact) sequence of `LargeExt` with six terms which starts by:
`LargeExact S.X₃ B n₀ ⟶ LargeExact S.X₂ B n₀ ⟶ LargeExact S.X₁ B n₀ → LargeExact S.X₃ B n₁ ⟶ ` -/
@[simp]
noncomputable def contravariantSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGroupCat.{w} 5 :=
  ComposableArrows.mk₅
    (AddCommGroupCat.ofHom (precomp (ofHom S.g) B n₀ n₀ (zero_add n₀)))
    (AddCommGroupCat.ofHom (precomp (ofHom S.f) B n₀ n₀ (zero_add n₀)))
    (AddCommGroupCat.ofHom (precomp hS.largeExtClass B n₀ n₁ (by omega)))
    (AddCommGroupCat.ofHom (precomp (ofHom S.g) B n₁ n₁ (zero_add n₁)))
    (AddCommGroupCat.ofHom (precomp (ofHom S.f) B n₁ n₁ (zero_add n₁)))

open Pretriangulated.Opposite

/-- The contravariant (exact) sequence of `LargeExt` identifies to the homology sequence
of the homological functor `(preadditiveCoyoneda.obj (Opposite.op ((singleFunctor C 0).obj A)))`
applied to the distinguished triangle `hS.singleTriangle`. -/
noncomputable def contravariantSequenceIso (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    contravariantSequence B hS n₀ n₁ h ≅
      (preadditiveYoneda.obj ((singleFunctor C 0).obj B)).homologySequenceComposableArrows₅
        (((triangleOpEquivalence _).functor.obj
          (Opposite.op hS.singleTriangle))) n₀ n₁ (by omega) :=
  isoMk₅
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₃ B n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₂ B n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₁ B n₀))
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₃ B n₁))
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₂ B n₁))
    (AddEquiv.toAddCommGroupCatIso (addEquiv S.X₁ B n₁))
    (by ext x; apply ShiftedHom.mk₀_comp) (by ext x; apply ShiftedHom.mk₀_comp)
    (by
      ext x
      have eq := oppositeShiftHomEquiv'_compatibility hS.singleδ x.hom n₁ (by omega)
      nth_rw 2 [← assoc] at eq
      exact eq)
    (by ext x; apply ShiftedHom.mk₀_comp) (by ext x; apply ShiftedHom.mk₀_comp)

lemma contravariantSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (contravariantSequence B hS n₀ n₁ h).Exact := by
  rw [exact_iff_of_iso (contravariantSequenceIso B hS n₀ n₁ h)]
  apply Functor.homologySequenceComposableArrows₅_exact _ _
    (op_distinguished _ hS.singleTriangle_distinguished)

variable {B}

/-- Given a short exact short complex `S` in an abelian category `C` and `B : C`,
this is the exactness of
`LargeExact S.X₂ B n₀ ⟶ LargeExact S.X₁ B n₀ ⟶ LargeExact S.X₃ B n₁`
when `1 + n₀ = n₁`. -/
lemma contravariant_sequence_exact₁
    {n₀ : ℕ} (x₁ : LargeExt S.X₁ B n₀) (n₁ : ℕ) (h : 1 + n₀ = n₁)
    (hx₁ : hS.largeExtClass.comp x₁ h = 0) :
    ∃ (x₂ : LargeExt S.X₂ B n₀), (ofHom S.f).comp x₂ (zero_add n₀) = x₁ :=
  (ShortComplex.ab_exact_iff _).1
    ((contravariantSequence_exact B hS n₀ n₁ (by omega)).exact 1) x₁ hx₁

/-- Given a short exact short complex `S` in an abelian category `C` and `B : C`,
this is the exactness of
`LargeExact S.X₃ B n ⟶ LargeExact S.X₂ B n ⟶ LargeExact S.X₁ B n`. -/
lemma contravariant_sequence_exact₂
    {n : ℕ} (x₂ : LargeExt S.X₂ B n) (hx₂ : (ofHom S.f).comp x₂ (zero_add n) = 0) :
    ∃ (x₃ : LargeExt S.X₃ B n), (ofHom S.g).comp x₃ (zero_add n) = x₂ :=
  (ShortComplex.ab_exact_iff _).1
    ((contravariantSequence_exact B hS n _ rfl).exact 0) x₂ hx₂

/-- Given a short exact short complex `S` in an abelian category `C` and `B : C`,
this is the exactness of
`LargeExact S.X₁ B n₀ ⟶ LargeExact S.X₃ B n₁ ⟶ LargeExact S.X₂ B n₁`
when `1 + n₀ = n₁`. -/
lemma contravariant_sequence_exact₃
    {n₁ : ℕ} (x₃ : LargeExt S.X₃ B n₁) (hx₃ : (ofHom S.g).comp x₃ (zero_add n₁) = 0)
    (n₀ : ℕ) (h : 1 + n₀ = n₁) :
    ∃ (x₁ : LargeExt S.X₁ B n₀), hS.largeExtClass.comp x₁ h = x₃ :=
  (ShortComplex.ab_exact_iff _).1
    ((contravariantSequence_exact B hS n₀ n₁ (by omega)).exact 2) x₃ hx₃

end ContravariantExactSequence

end LargeExt

end Abelian

end CategoryTheory
