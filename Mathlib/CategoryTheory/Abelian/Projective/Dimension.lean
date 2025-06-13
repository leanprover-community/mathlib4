/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Projective dimension

In an abelian category `C`, we shall say that `X : C` has projective dimension `< n`
if all `Ext X Y i` vanish when `n ≤ i`. This defines a type class
`HasProjectiveDimensionLT X n`. We also define a type class
`HasProjectiveDimensionLE X n` as an abbreviation for
`HasProjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasProjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasProjectiveDimensionLE`.)

-/

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object `X` in an abelian category has projective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasProjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasProjectiveDimensionLT.mk`, and the lemmas `hasProjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasProjectiveDimensionLT`.) -/
class HasProjectiveDimensionLT (X : C) (n : ℕ) : Prop where mk' ::
  subsingleton' (i : ℕ) (hi : n ≤ i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} X Y i)

/-- An object `X` in an abelian category has projective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i` -/
abbrev HasProjectiveDimensionLE (X : C) (n : ℕ) : Prop :=
  HasProjectiveDimensionLT X (n + 1)

namespace HasProjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : ℕ)

lemma subsingleton [hX : HasProjectiveDimensionLT X n] (i : ℕ) (hi : n ≤ i) (Y : C) :
    Subsingleton (Ext.{w} X Y i) := by
  letI := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
lemma mk (hX : ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0) :
    HasProjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ ↦ by simp only [hX i hi]⟩
    letI := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasProjectiveDimensionLT

lemma Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : ℕ} (e : Ext X Y i) (n : ℕ) [HasProjectiveDimensionLT X n]
    (hi : n ≤ i) : e = 0 :=
  (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : ℕ)

lemma hasProjectiveDimensionLT_iff [HasExt.{w} C] :
    HasProjectiveDimensionLT X n ↔
      ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext X Y i), e = 0 :=
  ⟨fun _ _ hi _ e ↦ e.eq_zero_of_hasProjectiveDimensionLT n hi,
    HasProjectiveDimensionLT.mk⟩

variable {X} in
lemma Limits.IsZero.hasProjectiveDimensionLT_zero (hX : IsZero X) :
    HasProjectiveDimensionLT X 0 := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp, hX.eq_of_src (𝟙 X) 0, Ext.mk₀_zero, Ext.zero_comp]

instance : HasProjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasProjectiveDimensionLT_zero

lemma isZero_of_hasProjectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : IsZero X := by
  letI := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)

lemma hasProjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X m := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by omega)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (n + k) :=
  hasProjectiveDimensionLT_of_ge X n (n + k) (by omega)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (k + n) :=
  hasProjectiveDimensionLT_of_ge X n (k + n) (by omega)

instance [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasProjectiveDimensionLT X (n + 1))

instance [Projective X] : HasProjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective

end

lemma Retract.hasProjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : ℕ)
    [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT X n := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp, ← h.retract, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero,
    ((Ext.mk₀ h.r).comp x (zero_add i)).eq_zero_of_hasProjectiveDimensionLT n hi,
    Ext.comp_zero]

lemma hasProjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : ℕ)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X' n :=
  e.symm.retract.hasProjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
include hS

-- In the following lemmas, the parameters `HasProjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

lemma hasProjectiveDimensionLT_X₂ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ n) :
    HasProjectiveDimensionLT S.X₂ n := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasProjectiveDimensionLT n hi, Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₃ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₂ : HasProjectiveDimensionLT S.X₂ (n + 1)) :
    HasProjectiveDimensionLT S.X₃ (n + 1) := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by omega), Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₁ (h₂ : HasProjectiveDimensionLT S.X₂ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ (n + 1)) :
    HasProjectiveDimensionLT S.X₁ n := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by omega))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by omega), Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1) :=
  ⟨fun _ ↦ hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ ↦ hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

instance (X Y : C) (n : ℕ) [HasProjectiveDimensionLT X n]
    [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasProjectiveDimensionLT_X₂ n
    (by assumption) (by assumption)

end CategoryTheory
