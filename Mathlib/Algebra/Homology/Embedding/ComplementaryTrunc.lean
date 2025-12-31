/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Complementary truncations


-/

@[expose] public section

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

variable (K : HomologicalComplex C c) {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c}
  [e₁.IsTruncLE] [e₂.IsTruncGE] (ac : e₁.AreComplementary e₂)

include ac

lemma ιStupidTrunc_πStupidTrunc :
    K.ιStupidTrunc e₂ ≫ K.πStupidTrunc e₁ = 0 := by
  ext n
  have h₁ : (K.stupidTrunc e₂).IsStrictlySupportedOutside e₁ := by
    rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance
  have h₂ : (K.stupidTrunc e₁).IsStrictlySupportedOutside e₂ := by
    rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
  · apply IsZero.eq_of_src
    apply h₁.isZero
  · apply IsZero.eq_of_tgt
    apply h₂.isZero

@[simps]
noncomputable def shortComplexStupidTrunc : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (K.ιStupidTrunc e₂) (K.πStupidTrunc e₁) (K.ιStupidTrunc_πStupidTrunc ac)

noncomputable def shortComplexStupidTruncSplitting₁ (n : ι₁) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ (e₁.f n))).Splitting where
  r := 0
  s := (asIso ((K.πStupidTrunc e₁).f (e₁.f n))).inv
  f_r := by
    apply IsZero.eq_of_src
    dsimp
    apply IsStrictlySupportedOutside.isZero (e := e₁)
    rw [ac.isStrictlySupportedOutside₁_iff]
    infer_instance

noncomputable def shortComplexStupidTruncSplitting₂ (n : ι₂) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ (e₂.f n))).Splitting where
  r := (asIso ((K.ιStupidTrunc e₂).f (e₂.f n))).inv
  s := 0
  s_g := by
    apply IsZero.eq_of_src
    dsimp
    apply IsStrictlySupportedOutside.isZero (e := e₂)
    rw [ac.isStrictlySupportedOutside₂_iff]
    infer_instance

noncomputable def shortComplexStupidTruncSplitting (n : ι) :
    ((K.shortComplexStupidTrunc ac).map (eval C _ n)).Splitting := by
  apply ac.desc (K.shortComplexStupidTruncSplitting₁ ac)
    (K.shortComplexStupidTruncSplitting₂ ac) n


end

end HomologicalComplex

namespace ComplexShape.Embedding.AreComplementary

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

variable {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c} (ac : e₁.AreComplementary e₂)
  (K : HomologicalComplex C c)

include ac

lemma isZero_stupidTrunc_iff [e₁.IsRelIff] :
    IsZero (K.stupidTrunc e₁) ↔ K.IsStrictlySupported e₂ := by
  rw [K.isZero_stupidTrunc_iff, ac.isStrictlySupportedOutside₁_iff]

lemma isZero_stupidTrunc [e₁.IsRelIff] [K.IsStrictlySupported e₂] :
    IsZero (K.stupidTrunc e₁) := by
  rw [ac.isZero_stupidTrunc_iff]
  infer_instance

end ComplexShape.Embedding.AreComplementary
