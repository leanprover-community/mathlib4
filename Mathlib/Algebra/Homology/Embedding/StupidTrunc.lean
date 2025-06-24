/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.IsSupported
import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The stupid truncation of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we define
a functor `stupidTruncFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
which sends `K` to `K.stupidTrunc e` which is defined as `(K.restriction e).extend e`.

## TODO (@joelriou)
* define the inclusion `e.stupidTruncFunctor C ⟶ 𝟭 _` when `[e.IsTruncGE]`;
* define the projection `𝟭 _ ⟶ e.stupidTruncFunctor C` when `[e.IsTruncLE]`.

-/

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

/-- The stupid truncation of a complex `K : HomologicalComplex C c'` relatively to
an embedding `e : c.Embedding c'` of complex shapes. -/
noncomputable def stupidTrunc : HomologicalComplex C c' := ((K.restriction e).extend e)

instance : IsStrictlySupported (K.stupidTrunc e) e := by
  dsimp [stupidTrunc]
  infer_instance

/-- The isomorphism `(K.stupidTrunc e).X i' ≅ K.X i'` when `i` is in the image of `e.f`. -/
noncomputable def stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.stupidTrunc e).X i' ≅ K.X i' :=
  (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

lemma isZero_stupidTrunc_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.stupidTrunc e).X i') :=
  isZero_extend_X _ _ _ hi'

instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] :
    IsStrictlySupported (K.stupidTrunc e) e' where
  isZero i' hi' := by
    by_cases hi'' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso (K.stupidTruncXIso e hi)
    · apply isZero_stupidTrunc_X
      simpa using hi''

lemma isZero_stupidTrunc_iff :
    IsZero (K.stupidTrunc e) ↔ K.IsStrictlySupportedOutside e := by
  constructor
  · exact fun h ↦ ⟨fun i ↦
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i ↦ (h.isZero i).of_iso (K.stupidTruncXIso e rfl)⟩

variable {K L M}

/-- The morphism `K.stupidTrunc e ⟶ L.stupidTrunc e` induced by a morphism `K ⟶ L`. -/
noncomputable def stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e :=
  extendMap (restrictionMap φ e) e

variable (K) in
@[simp]
lemma stupidTruncMap_id : stupidTruncMap (𝟙 K) e = 𝟙 _ := by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]
lemma stupidTruncMap_comp :
    stupidTruncMap (φ ≫ φ') e = stupidTruncMap φ e ≫ stupidTruncMap φ' e := by
  simp [stupidTruncMap, stupidTrunc]

@[reassoc (attr := simp)]
lemma stupidTruncMap_stupidTruncXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (stupidTruncMap φ e).f i' ≫ (L.stupidTruncXIso e hi).hom =
      (K.stupidTruncXIso e hi).hom ≫ φ.f i' := by
  subst hi
  simp [stupidTruncMap, stupidTruncXIso, extendMap_f _ _ rfl]

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The stupid truncation functor `HomologicalComplex C c' ⥤ HomologicalComplex C c'`
given by an embedding `e : Embedding c c'` of complex shapes. -/
@[simps]
noncomputable def stupidTruncFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

end ComplexShape.Embedding
