/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Data.ENat.Lattice

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

We also define the projective dimension in `WithBot ℕ∞` as `projectiveDimension`,
`projectiveDimension X = ⊥` iff `X` is zero and acts in common sense in the non-negative values.

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

lemma hasProjectiveDimensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ ↦ isZero_of_hasProjectiveDimensionLT_zero X, fun h ↦ h.hasProjectiveDimensionLT_zero⟩

lemma hasProjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X m := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by cutsat)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (n + k) :=
  hasProjectiveDimensionLT_of_ge X n (n + k) (by cutsat)

instance [HasProjectiveDimensionLT X n] (k : ℕ) :
    HasProjectiveDimensionLT X (k + n) :=
  hasProjectiveDimensionLT_of_ge X n (k + n) (by cutsat)

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

lemma projective_iff_subsingleton_ext_one [HasExt.{w} C] {X : C} :
    Projective X ↔ ∀ ⦃Y : C⦄, Subsingleton (Ext X Y 1) := by
  refine ⟨fun h ↦ HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h ↦ ⟨fun f g _ ↦ ?_⟩⟩
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.exact_kernel g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

lemma projective_iff_hasProjectiveDimensionLT_one (X : C) :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

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
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by cutsat), Ext.comp_zero]

lemma hasProjectiveDimensionLT_X₁ (h₂ : HasProjectiveDimensionLT S.X₂ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ (n + 1)) :
    HasProjectiveDimensionLT S.X₁ n := by
  letI := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by cutsat))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by cutsat), Ext.comp_zero]

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

section ProjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The projective dimension of an object in an abelian category. -/
noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

lemma Retract.projectiveDimension_le {X Y : C} (h : Retract X Y) :
    projectiveDimension X ≤ projectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn ↦ by
    simp only [Set.mem_setOf_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasProjectiveDimensionLT i)

lemma projectiveDimension_lt_iff {X : C} {n : ℕ} :
    projectiveDimension X < n ↔ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X ∈ _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_setOf_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ ↦ hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi ↦ hasProjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [WithBot.lt_add_one_iff]⟩

lemma projectiveDimension_le_iff (X : C) (n : ℕ) :
    projectiveDimension X ≤ n ↔ HasProjectiveDimensionLE X n := by
  simp [← projectiveDimension_lt_iff, ← WithBot.lt_add_one_iff]

lemma projectiveDimension_ge_iff (X : C) (n : ℕ) :
    n ≤ projectiveDimension X ↔ ¬ HasProjectiveDimensionLT X n := by
  rw [← not_iff_not, not_le, not_not, projectiveDimension_lt_iff]

lemma projectiveDimension_eq_bot_iff (X : C) :
    projectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero, ← projectiveDimension_lt_iff,
    Nat.cast_zero, ← WithBot.lt_coe_bot, bot_eq_zero', WithBot.coe_zero]

lemma projectiveDimension_ne_top_iff (X : C) :
    projectiveDimension X ≠ ⊤ ↔ ∃ n, HasProjectiveDimensionLE X n := by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← projectiveDimension_le_iff, hd, WithBot.coe_top, top_le_iff] at hn
      exact ENat.coe_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.coe_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← projectiveDimension_le_iff] using hd.le⟩

end CategoryTheory

end ProjectiveDimension
