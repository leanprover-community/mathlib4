/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Long exact sequences of `Ext`-groups

In this file, we obtain the covariant long exact sequence of `Ext` when `n₀ + 1 = n₁`:
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `S` is a short exact short complex in an abelian category `C`, `n₀ + 1 = n₁` and `X : C`.
Similarly, if `Y : C`, there is a contravariant long exact sequence :
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ → Ext S.X₁ Y n₁`.

-/

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

open Opposite DerivedCategory Pretriangulated Pretriangulated.Opposite

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Abelian

namespace Ext

section CovariantSequence

lemma hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C]
    {X Y Z : C} {n : ℕ} (x : Ext X Y n) (f : Y ⟶ Z) :
    x.hom ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : ℤ)⟧' =
      (x.comp (mk₀ f) (add_zero n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

variable {X : C} {S : ShortComplex C} (hS : S.ShortExact)

lemma preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {X : C} {n₀ : ℕ} (x : Ext X S.X₃ n₀)
    {n₁ : ℕ} (h : n₀ + 1 = n₁) :
    (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequenceδ
      hS.singleTriangle n₀ n₁ (by cutsat) x.hom =
        (x.comp hS.extClass h).hom := by
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

variable (X)

include hS in
/-- Alternative formulation of `covariant_sequence_exact₂` -/
lemma covariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n)))
      (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ShortComplex.zero, mk₀_zero,
          comp_zero])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₂ _
    (hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext x; apply hom_comp_singleFunctor_map_shift (C := C)

section

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- Alternative formulation of `covariant_sequence_exact₃` -/
lemma covariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h)) (by
        ext x
        dsimp
        simp only [comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
          comp_zero])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₃ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by cutsat)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h

/-- Alternative formulation of `covariant_sequence_exact₁` -/
lemma covariant_sequence_exact₁' :
    (ShortComplex.mk
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
      (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁))) (by
        ext x
        dsimp
        simp only [comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp,
          comp_zero])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj X))).homologySequence_exact₁ _
    (hS.singleTriangle_distinguished) n₀ n₁ (by cutsat)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext x
    exact preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS x h
  · ext x; apply hom_comp_singleFunctor_map_shift (C := C)

open ComposableArrows

/-- Given a short exact short complex `S` in an abelian category `C` and an object `X : C`,
this is the long exact sequence
`Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁`
when `n₀ + 1 = n₁` -/
noncomputable def covariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp X h))
    (AddCommGrpCat.ofHom ((mk₀ S.f).postcomp X (add_zero n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero n₁)))

lemma covariantSequence_exact :
    (covariantSequence X hS n₀ n₁ h).Exact :=
  exact_of_δ₀ (covariant_sequence_exact₂' X hS n₀).exact_toComposableArrows
    (exact_of_δ₀ (covariant_sequence_exact₃' X hS n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (covariant_sequence_exact₁' X hS n₀ n₁ h).exact_toComposableArrows
        (covariant_sequence_exact₂' X hS n₁).exact_toComposableArrows))

end

lemma covariant_sequence_exact₁ {n₁ : ℕ} (x₁ : Ext X S.X₁ n₁)
    (hx₁ : x₁.comp (mk₀ S.f) (add_zero n₁) = 0) {n₀ : ℕ} (hn₀ : n₀ + 1 = n₁) :
    ∃ (x₃ : Ext X S.X₃ n₀), x₃.comp hS.extClass hn₀ = x₁ := by
  have := covariant_sequence_exact₁' X hS n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
lemma covariant_sequence_exact₂ {n : ℕ} (x₂ : Ext X S.X₂ n)
    (hx₂ : x₂.comp (mk₀ S.g) (add_zero n) = 0) :
    ∃ (x₁ : Ext X S.X₁ n), x₁.comp (mk₀ S.f) (add_zero n) = x₂ := by
  have := covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

lemma covariant_sequence_exact₃ {n₀ : ℕ} (x₃ : Ext X S.X₃ n₀) {n₁ : ℕ} (hn₁ : n₀ + 1 = n₁)
    (hx₃ : x₃.comp hS.extClass hn₁ = 0) :
    ∃ (x₂ : Ext X S.X₂ n₀), x₂.comp (mk₀ S.g) (add_zero n₀) = x₃ := by
  have := covariant_sequence_exact₃' X hS n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

end CovariantSequence

section ContravariantSequence

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

lemma singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C]
    {X Y Z : C} (f : X ⟶ Y) {n : ℕ} (x : Ext Y Z n) :
    (DerivedCategory.singleFunctor C 0).map f ≫ x.hom =
      ((mk₀ f).comp x (zero_add n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

lemma preadditiveYoneda_homologySequenceδ_singleTriangle_apply
    [HasDerivedCategory.{w'} C] {Y : C} {n₀ : ℕ} (x : Ext S.X₁ Y n₀)
    {n₁ : ℕ} (h : 1 + n₀ = n₁) :
    (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op hS.singleTriangle)) n₀ n₁ (by cutsat) x.hom =
      (hS.extClass.comp x h).hom := by
  rw [preadditiveYoneda_homologySequenceδ_apply,
    comp_hom, hS.extClass_hom, ShiftedHom.comp]
  rfl

include hS in
/-- Alternative formulation of `contravariant_sequence_exact₂` -/
lemma contravariant_sequence_exact₂' (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n)))
      (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n))) (by
        ext
        dsimp
        simp only [mk₀_comp_mk₀_assoc, ShortComplex.zero, mk₀_zero, zero_comp])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₂ _
    (op_distinguished _ hS.singleTriangle_distinguished) n
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  all_goals ext; apply singleFunctor_map_comp_hom (C := C)

section

variable (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁)

/-- Alternative formulation of `contravariant_sequence_exact₁` -/
lemma contravariant_sequence_exact₁' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (((mk₀ S.f).precomp Y (zero_add n₀))))
      (AddCommGrpCat.ofHom (hS.extClass.precomp Y h)) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.extClass_comp_assoc])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₃ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by cutsat)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; apply singleFunctor_map_comp_hom (C := C)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply

/-- Alternative formulation of `contravariant_sequence_exact₃` -/
lemma contravariant_sequence_exact₃' :
    (ShortComplex.mk (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
      (AddCommGrpCat.ofHom (((mk₀ S.g).precomp Y (zero_add n₁)))) (by
        ext
        dsimp
        simp only [ShortComplex.ShortExact.comp_extClass_assoc])).Exact := by
  letI := HasDerivedCategory.standard C
  have := (preadditiveYoneda.obj ((singleFunctor C 0).obj Y)).homologySequence_exact₁ _
    (op_distinguished _ hS.singleTriangle_distinguished) n₀ n₁ (by cutsat)
  rw [ShortComplex.ab_exact_iff_function_exact] at this ⊢
  apply Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := Ext.homAddEquiv)
    (e₂ := Ext.homAddEquiv) (e₃ := Ext.homAddEquiv) (H := this)
  · ext; dsimp; apply preadditiveYoneda_homologySequenceδ_singleTriangle_apply
  · ext; apply singleFunctor_map_comp_hom (C := C)

open ComposableArrows

/-- Given a short exact short complex `S` in an abelian category `C` and an object `Y : C`,
this is the long exact sequence
`Ext S.X₃ Y n₀ → Ext S.X₂ Y n₀ → Ext S.X₁ Y n₀ → Ext S.X₃ Y n₁ → Ext S.X₂ Y n₁ → Ext S.X₁ Y n₁`
when `1 + n₀ = n₁`. -/
noncomputable def contravariantSequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₀)))
    (AddCommGrpCat.ofHom (hS.extClass.precomp Y h))
    (AddCommGrpCat.ofHom ((mk₀ S.g).precomp Y (zero_add n₁)))
    (AddCommGrpCat.ofHom ((mk₀ S.f).precomp Y (zero_add n₁)))

lemma contravariantSequence_exact :
    (contravariantSequence hS Y n₀ n₁ h).Exact :=
  exact_of_δ₀ (contravariant_sequence_exact₂' hS Y n₀).exact_toComposableArrows
    (exact_of_δ₀ (contravariant_sequence_exact₁' hS Y n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (contravariant_sequence_exact₃' hS Y n₀ n₁ h).exact_toComposableArrows
        (contravariant_sequence_exact₂' hS Y n₁).exact_toComposableArrows))

end

lemma contravariant_sequence_exact₁ {n₀ : ℕ} (x₁ : Ext S.X₁ Y n₀) {n₁ : ℕ} (hn₁ : 1 + n₀ = n₁)
    (hx₁ : hS.extClass.comp x₁ hn₁ = 0) :
    ∃ (x₂ : Ext S.X₂ Y n₀), (mk₀ S.f).comp x₂ (zero_add n₀) = x₁ := by
  have := contravariant_sequence_exact₁' hS Y n₀ n₁ hn₁
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₁ hx₁

include hS in
lemma contravariant_sequence_exact₂ {n : ℕ} (x₂ : Ext S.X₂ Y n)
    (hx₂ : (mk₀ S.f).comp x₂ (zero_add n) = 0) :
    ∃ (x₁ : Ext S.X₃ Y n), (mk₀ S.g).comp x₁ (zero_add n) = x₂ := by
  have := contravariant_sequence_exact₂' hS Y n
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₂ hx₂

lemma contravariant_sequence_exact₃ {n₁ : ℕ} (x₃ : Ext S.X₃ Y n₁)
    (hx₃ : (mk₀ S.g).comp x₃ (zero_add n₁) = 0) {n₀ : ℕ} (hn₀ : 1 + n₀ = n₁) :
    ∃ (x₁ : Ext S.X₁ Y n₀), hS.extClass.comp x₁ hn₀ = x₃ := by
  have := contravariant_sequence_exact₃' hS Y n₀ n₁ hn₀
  rw [ShortComplex.ab_exact_iff] at this
  exact this x₃ hx₃

end ContravariantSequence

end Ext

end Abelian

end CategoryTheory
