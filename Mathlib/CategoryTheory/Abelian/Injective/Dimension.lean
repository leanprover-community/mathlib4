/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.ENat.Lattice

/-!
# Injective dimension

In an abelian category `C`, we shall say that `X : C` has Injective dimension `< n`
if all `Ext Y X i` vanish when `n ≤ i`. This defines a type class
`HasInjectiveDimensionLT X n`. We also define a type class
`HasInjectiveDimensionLE X n` as an abbreviation for
`HasInjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasInjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasInjectiveDimensionLE`.)

We also define the Injective dimension in `WithBot ℕ∞` as `injectiveDimension`,
`injectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object `X` in an abelian category has Injective dimension `< n` if
all `Ext X Y i` vanish when `n ≤ i`. See also `HasInjectiveDimensionLE`.
(Do not use the `subsingleton'` field directly. Use the constructor
`HasInjectiveDimensionLT.mk`, and the lemmas `hasInjectiveDimensionLT_iff` and
`Ext.eq_zero_of_hasInjectiveDimensionLT`.) -/
class HasInjectiveDimensionLT (X : C) (n : ℕ) : Prop where mk' ::
  subsingleton' (i : ℕ) (hi : n ≤ i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} Y X i)

/-- An object `X` in an abelian category has Injective dimension `≤ n` if
all `Ext X Y i` vanish when `n + 1 ≤ i` -/
abbrev HasInjectiveDimensionLE (X : C) (n : ℕ) : Prop :=
  HasInjectiveDimensionLT X (n + 1)

namespace HasInjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : ℕ)

lemma subsingleton [hX : HasInjectiveDimensionLT X n] (i : ℕ) (hi : n ≤ i) (Y : C) :
    Subsingleton (Ext.{w} Y X i) := by
  letI := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
lemma mk (hX : ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext Y X i), e = 0) :
    HasInjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext Y X i) := ⟨fun e₁ e₂ ↦ by simp only [hX i hi]⟩
    letI := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasInjectiveDimensionLT

lemma Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : ℕ} (e : Ext Y X i) (n : ℕ) [HasInjectiveDimensionLT X n]
    (hi : n ≤ i) : e = 0 :=
  (HasInjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : ℕ)

lemma hasInjectiveDimensionLT_iff [HasExt.{w} C] :
    HasInjectiveDimensionLT X n ↔
      ∀ (i : ℕ) (_ : n ≤ i) ⦃Y : C⦄, ∀ (e : Ext Y X i), e = 0 :=
  ⟨fun _ _ hi _ e ↦ e.eq_zero_of_hasInjectiveDimensionLT n hi,
    HasInjectiveDimensionLT.mk⟩

variable {X} in
lemma Limits.IsZero.hasInjectiveDimensionLT_zero (hX : IsZero X) :
    HasInjectiveDimensionLT X 0 := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.comp_mk₀_id, hX.eq_zero_of_tgt (𝟙 X), Ext.mk₀_zero, Ext.comp_zero]

instance : HasInjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasInjectiveDimensionLT_zero

lemma isZero_of_hasInjectiveDimensionLT_zero [HasInjectiveDimensionLT X 0] : IsZero X := by
  letI := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT _ 0 (by rfl)

lemma hasInjectiveDimensionLT_zero_iff_isZero : HasInjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ ↦ isZero_of_hasInjectiveDimensionLT_zero X, fun h ↦ h.hasInjectiveDimensionLT_zero⟩

lemma hasInjectiveDimensionLT_of_ge (m : ℕ) (h : n ≤ m)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X m := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasInjectiveDimensionLT n (by lia)

instance [HasInjectiveDimensionLT X n] (k : ℕ) :
    HasInjectiveDimensionLT X (n + k) :=
  hasInjectiveDimensionLT_of_ge X n (n + k) (by lia)

instance [HasInjectiveDimensionLT X n] (k : ℕ) :
    HasInjectiveDimensionLT X (k + n) :=
  hasInjectiveDimensionLT_of_ge X n (k + n) (by lia)

instance [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasInjectiveDimensionLT X (n + 1))

instance [Injective X] : HasInjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_injective

lemma injective_iff_subsingleton_ext_one [HasExt.{w} C] {X : C} :
    Injective X ↔ ∀ ⦃Y : C⦄, Subsingleton (Ext Y X 1) := by
  refine ⟨fun h ↦ HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h ↦ ⟨fun f g _ ↦ ?_⟩⟩
  obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ { exact := ShortComplex.exact_cokernel g } _
    (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

lemma injective_iff_hasInjectiveDimensionLT_one (X : C) :
    Injective X ↔ HasInjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ injective_iff_subsingleton_ext_one.2
    (HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

end

lemma Retract.hasInjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : ℕ)
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT X n := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.comp_mk₀_id, ← h.retract, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    (x.comp (Ext.mk₀ h.i) (add_zero i)).eq_zero_of_hasInjectiveDimensionLT n hi, Ext.zero_comp]

lemma hasInjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : ℕ)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X' n :=
  e.symm.retract.hasInjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
include hS

-- In the following lemmas, the parameters `HasInjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

lemma hasInjectiveDimensionLT_X₂ (h₁ : HasInjectiveDimensionLT S.X₁ n)
    (h₃ : HasInjectiveDimensionLT S.X₃ n) :
    HasInjectiveDimensionLT S.X₂ n := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x₂
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasInjectiveDimensionLT n hi, Ext.zero_comp]

lemma hasInjectiveDimensionLT_X₁ (h₁ : HasInjectiveDimensionLT S.X₃ n)
    (h₂ : HasInjectiveDimensionLT S.X₂ (n + 1)) :
    HasInjectiveDimensionLT S.X₁ (n + 1) := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₃
      (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) hi) rfl
    rw [x₁.eq_zero_of_hasInjectiveDimensionLT n (by lia), Ext.zero_comp]

lemma hasInjectiveDimensionLT_X₃ (h₂ : HasInjectiveDimensionLT S.X₂ n)
    (h₃ : HasInjectiveDimensionLT S.X₁ (n + 1)) :
    HasInjectiveDimensionLT S.X₃ n := by
  letI := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasInjectiveDimensionLT n (by lia), Ext.zero_comp]

lemma hasInjectiveDimensionLT_X₃_iff (n : ℕ) (h₂ : Injective S.X₂) :
    HasInjectiveDimensionLT S.X₃ (n + 1) ↔ HasInjectiveDimensionLT S.X₁ (n + 2) :=
  ⟨fun _ ↦ hS.hasInjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ ↦ hS.hasInjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

instance (X Y : C) (n : ℕ) [HasInjectiveDimensionLT X n]
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasInjectiveDimensionLT_X₂ n
    (by assumption) (by assumption)

lemma hasProjectiveDimensionLT_of_subsingleton [HasExt.{w} C] [EnoughProjectives C] (X : C) (n : ℕ)
    (hX : ∀ Y : C, Subsingleton (Ext Y X n)) : HasInjectiveDimensionLT X n := by
  match n with
  | 0 =>
    exact (IsZero.of_epi_eq_zero (𝟙 X) ((Ext.homEquiv₀.subsingleton_congr.mp (hX X)).eq_zero
      (𝟙 X))).hasInjectiveDimensionLT_zero
  | n + 1 =>
    refine HasInjectiveDimensionLT.mk (fun i hi {Y} e ↦ @ Subsingleton.eq_zero _ _ ?_ e)
    obtain ⟨k, rfl⟩ : ∃ k, i = n + 1 + k := Nat.exists_eq_add_of_le hi
    induction k generalizing Y with
    | zero => simpa using hX Y
    | succ k ih =>
      rcases EnoughProjectives.presentation Y with ⟨P, g⟩
      let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
      have S_exact : S.ShortExact := { exact := ShortComplex.exact_kernel g }
      have eq : 1 + (n + 1 + k) = n + 1 + (k + 1) := by abel
      have sub : Subsingleton (Ext P X (n + 1 + (k + 1))) := Ext.subsingleton_of_projective P X _
      have surj : Function.Surjective (S_exact.extClass.precomp X eq) :=
        fun x ↦ Ext.contravariant_sequence_exact₃ S_exact X x (sub.eq_zero _) eq
      exact @surj.subsingleton _ _ _ (ih (Nat.le_add_right _ k) 0)

end CategoryTheory

section InjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The injective dimension of an object in an abelian category. -/
noncomputable def injectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasInjectiveDimensionLT X i}

lemma injectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    injectiveDimension X = injectiveDimension Y := by
  simp only [injectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasInjectiveDimensionLT_of_iso e _,
    fun h ↦ hasInjectiveDimensionLT_of_iso e.symm _⟩

lemma Retract.injectiveDimension_le {X Y : C} (h : Retract X Y) :
    injectiveDimension X ≤ injectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn ↦ by
    simp only [Set.mem_setOf_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasInjectiveDimensionLT i)

set_option backward.isDefEq.respectTransparency false in
lemma injectiveDimension_lt_iff {X : C} {n : ℕ} :
    injectiveDimension X < n ↔ HasInjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : injectiveDimension X ∈ _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_setOf_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ ↦ hasInjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi ↦ hasInjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩

lemma injectiveDimension_le_iff (X : C) (n : ℕ) :
    injectiveDimension X ≤ n ↔ HasInjectiveDimensionLE X n := by
  simp [← injectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

lemma injectiveDimension_ge_iff (X : C) (n : ℕ) :
    n ≤ injectiveDimension X ↔ ¬ HasInjectiveDimensionLT X n := by
  contrapose!; exact injectiveDimension_lt_iff

lemma injectiveDimension_eq_bot_iff (X : C) :
    injectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasInjectiveDimensionLT_zero_iff_isZero, ← injectiveDimension_lt_iff,
    Nat.cast_zero, ← WithBot.lt_coe_bot, bot_eq_zero', WithBot.coe_zero]

lemma injectiveDimension_ne_top_iff (X : C) :
    injectiveDimension X ≠ ⊤ ↔ ∃ n, HasInjectiveDimensionLE X n := by
  generalize hd : injectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← injectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← injectiveDimension_le_iff, hd, WithBot.coe_top, top_le_iff] at hn
      exact ENat.coe_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.coe_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← injectiveDimension_le_iff] using hd.le⟩

end CategoryTheory

end InjectiveDimension
