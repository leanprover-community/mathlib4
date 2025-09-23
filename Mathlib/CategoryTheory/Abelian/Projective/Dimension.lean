/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Data.ENat.Lattice
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.Grp.Zero

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

We also defined the projective dimension as `WithBot ℕ∞` as `projectiveDimension`,
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

lemma hasProjectiveDimensionLT_one_iff (X : C) :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  refine ⟨fun h ↦ inferInstance, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  intro Z Y f g epi
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have S_exact : S.ShortExact := {
    exact := ShortComplex.exact_kernel g
    mono_f := equalizer.ι_mono
    epi_g := epi}
  have : IsZero (AddCommGrp.of (Ext X S.X₁ 1)) := by
    let _ := h 1 (le_refl 1) (Y := S.X₁)
    exact AddCommGrp.isZero_of_subsingleton _
  have exac := Ext.covariant_sequence_exact₃' X S_exact 0 1 (zero_add 1)
  have surj: Function.Surjective ((Ext.mk₀ S.g).postcomp X (add_zero 0)) :=
    (AddCommGrp.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
  rcases surj (Ext.mk₀ f) with ⟨f', hf'⟩
  use Ext.addEquiv₀ f'
  simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply] at hf'
  rw [← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
  exact (Ext.mk₀_bijective X Y).1 hf'

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

section ProjectiveDimension

open CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/-- The projective dimension of object of abelian category. -/
noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

lemma hasProjectiveDimensionLT_of_projectiveDimension_lt (X : C) (n : ℕ)
    (h : projectiveDimension X < n) : HasProjectiveDimensionLT X n := by
  have : projectiveDimension X ∈ _ := csInf_mem (by
    use ⊤
    simp)
  simp only [Set.mem_setOf_eq] at this
  exact this n h

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply hasProjectiveDimensionLT_of_projectiveDimension_lt X (n + 1)
    exact lt_of_le_of_lt h (Nat.cast_lt.mpr (lt_add_one n))
  · apply sInf_le
    simp only [Set.mem_setOf_eq, Nat.cast_lt]
    intro i hi
    exact hasProjectiveDimensionLT_of_ge X (n + 1) i hi

lemma projectiveDimension_ge_iff (X : C) (n : ℕ) : n ≤ projectiveDimension X  ↔
    ¬ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq] at h
    by_contra lt
    by_cases eq0 : n = 0
    · have := h ⊥ (fun i _ ↦ (hasProjectiveDimensionLT_of_ge X n i (by simp [eq0])))
      simp [eq0] at this
    · have : ∀ (i : ℕ), (n - 1 : ℕ) < (i : WithBot ℕ∞) → HasProjectiveDimensionLT X i := by
        intro i hi
        exact hasProjectiveDimensionLT_of_ge X n i (Nat.le_of_pred_lt (Nat.cast_lt.mp hi))
      have not := Nat.cast_le.mp (h (n - 1 : ℕ) this)
      omega
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro m hm
    by_contra nle
    exact h (hm _ (lt_of_not_ge nle))

lemma projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔
    Limits.IsZero X := by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply hasProjectiveDimensionLT_of_projectiveDimension_lt X 0
    simp [h, bot_lt_iff_ne_bot]
  · rw [eq_bot_iff]
    apply sInf_le
    intro i _
    apply hasProjectiveDimensionLT_of_ge X 0 i (Nat.zero_le i)

lemma projectiveDimension_eq_find (X : C) (h : ∃ n, HasProjectiveDimensionLE X n)
    (nzero : ¬ Limits.IsZero X) [DecidablePred (HasProjectiveDimensionLE X)] :
    projectiveDimension X = Nat.find h := by
  apply le_antisymm ((projectiveDimension_le_iff _ _).mpr (Nat.find_spec h))
  apply (projectiveDimension_ge_iff _ _).mpr
  by_cases eq0 : Nat.find h = 0
  · simp only [eq0]
    by_contra
    exact nzero (isZero_of_hasProjectiveDimensionLT_zero X)
  · rw [← Nat.succ_pred_eq_of_ne_zero eq0]
    exact (Nat.find_min h (Nat.sub_one_lt eq0))

lemma projectiveDimension_ne_top_iff (X : C) : projectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  simp only [projectiveDimension, ne_eq, sInf_eq_top, Set.mem_setOf_eq, not_forall]
  refine ⟨fun ⟨x, hx, ne⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · by_cases eqbot : x = ⊥
    · use 0
      have := hx 0 (by simp [eqbot, bot_lt_iff_ne_bot])
      exact instHasProjectiveDimensionLTSucc X 0
    · have : x.unbot eqbot ≠ ⊤ := by
        by_contra eq
        rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
        exact ne eq
      use (x.unbot eqbot).toNat
      have eq : x = (x.unbot eqbot).toNat := (WithBot.coe_unbot x eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)
      have : x < ((x.unbot eqbot).toNat + 1 : ℕ) := by
        nth_rw 1 [eq]
        exact Nat.cast_lt.mpr (lt_add_one _)
      exact hx ((x.unbot eqbot).toNat + 1 : ℕ) this
  · use n
    simpa using ⟨fun i hi ↦ hasProjectiveDimensionLT_of_ge X (n + 1) i hi,
      WithBot.coe_inj.not.mpr (ENat.coe_ne_top n)⟩

end ProjectiveDimension
