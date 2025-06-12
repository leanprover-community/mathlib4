/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Basic
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Support of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we say
that `K : HomologicalComplex C c'` is supported (resp. strictly supported) on `e`
if `K` is exact in degree `i'` (resp. `K.X i'` is zero) whenever `i'` is
not of the form `e.f i`. This defines two typeclasses `K.IsSupported e`
and `K.IsStrictlySupported e`.

We also define predicates `K.IsSupportedOutside e` and `K.IsStrictlySupportedOutside e`
when the conditions above are satisfied for those `i'` that are of the form `e.f i`.
(These two predicates are not made typeclasses because in most practical applications,
they are equivalent to `K.IsSupported e'` or `K.IsStrictlySupported e'` for a
complementary embedding `e'`.)

-/

open CategoryTheory Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (e : c.Embedding c')

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K.X i'` is zero
whenever `i'` is not of the form `e.f i` for some `i`. -/
class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : ∀ i, e.f i ≠ i') : IsZero (K.X i')

lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'

include e' in
variable {K L} in
lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

@[simp]
lemma isStrictlySupported_op_iff :
    K.op.IsStrictlySupported e.op ↔ K.IsStrictlySupported e :=
  ⟨(fun _ ↦ ⟨fun i' hi' ↦ (K.op.isZero_X_of_isStrictlySupported e.op i' hi').unop⟩),
    (fun _ ↦ ⟨fun i' hi' ↦ (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩

instance [K.IsStrictlySupported e] :
    K.op.IsStrictlySupported e.op := by
  rw [isStrictlySupported_op_iff]
  infer_instance

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `i'`
whenever `i'` is not of the form `e.f i` for some `i`. -/
class IsSupported : Prop where
  exactAt (i' : ι') (hi' : ∀ i, e.f i ≠ i') : K.ExactAt i'

lemma exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    K.ExactAt i' :=
  IsSupported.exactAt i' hi'

include e' in
variable {K L} in
lemma isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' :=
    (K.exactAt_of_isSupported e i' hi').of_iso e'

instance [K.IsStrictlySupported e] : K.IsSupported e where
  exactAt i' hi' := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

@[simp]
lemma isSupported_op_iff :
    K.op.IsSupported e.op ↔ K.IsSupported e :=
  ⟨fun _ ↦ ⟨fun i' hi' ↦ (K.op.exactAt_of_isSupported e.op i' hi').unop⟩,
    fun _ ↦ ⟨fun i' hi' ↦ (K.exactAt_of_isSupported e i' hi').op⟩⟩

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupportedOutside e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K.X (e.f i)` is zero for all `i`. -/
structure IsStrictlySupportedOutside : Prop where
  isZero (i : ι) : IsZero (K.X (e.f i))

@[simp]
lemma isStrictlySupportedOutside_op_iff :
    K.op.IsStrictlySupportedOutside e.op ↔ K.IsStrictlySupportedOutside e :=
  ⟨fun h ↦ ⟨fun i ↦ (h.isZero i).unop⟩, fun h ↦ ⟨fun i ↦ (h.isZero i).op⟩⟩

/-- If `K : HomologicalComplex C c'`, then `K.IsSupportedOutside e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `e.f i` for all `i`. -/
structure IsSupportedOutside : Prop where
  exactAt (i : ι) : K.ExactAt (e.f i)

@[simp]
lemma isSupportedOutside_op_iff :
    K.op.IsSupportedOutside e.op ↔ K.IsSupportedOutside e :=
  ⟨fun h ↦ ⟨fun i ↦ (h.exactAt i).unop⟩, fun h ↦ ⟨fun i ↦ (h.exactAt i).op⟩⟩

variable {K e} in
lemma IsStrictlySupportedOutside.isSupportedOutside (h : K.IsStrictlySupportedOutside e) :
    K.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)

instance [HasZeroObject C] : (0 : HomologicalComplex C c').IsStrictlySupported e where
  isZero i _ := (eval _ _ i).map_isZero (Limits.isZero_zero _)

lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : ∃ i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)

instance [K.IsStrictlySupported e] : K.op.IsStrictlySupported e.op where
  isZero j hj' := (K.isZero_X_of_isStrictlySupported e j hj').op

end

section

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (K : HomologicalComplex C c') (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

instance map_isStrictlySupported [K.IsStrictlySupported e] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e where
  isZero i' hi' := by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id, (K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0, F.map_zero]

end

end HomologicalComplex
