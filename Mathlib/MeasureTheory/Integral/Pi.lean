/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Integrals of functions defined on indexed product types

In this file we prove lemmas about integrals of functions defined on indexed product types
`f : (∀ i, α i) → E`. One of the goals of this file is to help with transfer of results about, e.g.,
functions on `ℝⁿ = Fin n → ℝ` for small values of `n` to results about functions on `ℝ` or `ℝ × ℝ`.

## Main results

- If `ι` is an empty type, then `∫ x, f x = f default`.
- If `ι` is a type with a unique element, then `∫ x, f x = ∫ y, f (const ι y)`.

For a type with a unique element, we also provide lemmas that are more useful for rewriting from an
integral over `α` to an integral over `ι → α`.

## TODO

- Add a section about `Fin 2 → α`.
- Add a section about `Fin.insertNth`.
- Relate integrals over `ι → α` and `ι' → α` given an equivalence `ι ≃ ι'`.
- Add a version of Fubini theorem: integrating over `ι → α` is the same as integrating over `s → α`,
  then over `sᶜ → α`, where `s : Set ι`. Can we reformulate it for two embeddings `ι₁ → ι` and
  `ι₂ → ι` with complement ranges?

## Keywords

integral, pi type
-/

open Function Set MeasureTheory.Measure

namespace MeasureTheory

variable {ι E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section IsEmpty

/-!
### Integral over `(i : ι) → α i` with empty `ι`

If `ι` is an empty type (e.g., `Fin 0`), then `(i : ι) → α i` is a singleton, and a
`MeasureTheory.Measure.pi`-measure on this singleton is the Dirac measure. Thus integral of a
function over a `pi`-measure is equal to the value of this function at the unique point.
-/

section Measure

variable [IsEmpty ι] {α : ι → Type _} [∀ i, MeasurableSpace (α i)]

theorem integral_pi_empty (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) :
    ∫ x, f x ∂(.pi μ) = f default := by
  rw [Measure.pi_of_empty, integral_dirac]; rfl

theorem set_integral_pi_empty (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) {s : Set (∀ i, α i)}
    (hs : default ∈ s) : ∫ x in s, f x ∂(Measure.pi μ) = f default := by
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty ⟨_, hs⟩
  rw [restrict_univ, integral_pi_empty]

theorem set_integral_pi_empty_pi (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) (I : Set ι)
    (s : ∀ i, Set (α i)) : ∫ x in I.pi s, f x ∂(Measure.pi μ) = f default :=
  set_integral_pi_empty f μ isEmptyElim

theorem set_integral_pi_empty_Icc [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (μ : ∀ i, Measure (α i)) (a b : (∀ i, α i)) :
    ∫ x in Icc a b, f x ∂(.pi μ) = f default :=
  set_integral_pi_empty f μ ⟨isEmptyElim, isEmptyElim⟩

end Measure

variable [IsEmpty ι] {α : ι → Type _} [∀ i, MeasureSpace (α i)]

theorem integral_pi_empty_volume (f : (∀ i, α i) → E) : ∫ x, f x = f default :=
  integral_pi_empty _ _

theorem set_integral_pi_empty_volume (f : (∀ i, α i) → E) {s : Set (∀ i, α i)} (hs : default ∈ s) :
    ∫ x in s, f x = f default :=
  set_integral_pi_empty f _ hs

theorem set_integral_pi_empty_pi_volume (f : (∀ i, α i) → E) (I : Set ι) (s : ∀ i, Set (α i)) :
    ∫ x in I.pi s, f x = f default :=
  set_integral_pi_empty_pi f _ I s

theorem set_integral_pi_empty_Icc_volume [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (a b : (∀ i, α i)) : ∫ x in Icc a b, f x = f default :=
  set_integral_pi_empty_Icc _ _ _ _

end IsEmpty

section Unique

/-!
### Integrals of functions on types with a unique element

If `ι` has a unique element (e.g., `ι = Fin 1` or `ι = PUnit`), then `ι → α` is equivalent to `α`,
thus integrating over `ι → α` is equivalent to integrating over `α`. We provide lemmas that allow
rewriting between these two kinds of integrals in both directions.
-/

section Measure

variable [Unique ι] {α : Type _} [MeasurableSpace α]

theorem integral_pi_unique (f : (ι → α) → E) (μ : Measure α) :
    ∫ x, f x ∂(.pi fun _ ↦ μ) = ∫ x, f (const ι x) ∂μ :=
  Eq.symm <| ((measurePreserving_funUnique _ _).symm _).integral_comp
    (MeasurableEquiv.measurableEmbedding _) _

theorem set_integral_pi_unique (f : (ι → α) → E) (μ : Measure α) (s : Set (ι → α)) :
    ∫ x in s, f x ∂(.pi fun _ ↦ μ) = ∫ x in const ι ⁻¹' s, f (const ι x) ∂μ :=
  Eq.symm <| ((measurePreserving_funUnique _ _).symm _).set_integral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) _ _

theorem set_integral_pi_unique_pi (f : (ι → α) → E) (μ : Measure α) (s : ι → Set α) :
    ∫ x in Set.pi univ s, f x ∂(.pi fun _ ↦ μ) = ∫ x in s default, f (const ι x) ∂μ := by
  simp only [set_integral_pi_unique, Set.preimage, Set.mem_univ_pi, Unique.forall_iff]
  rfl

theorem set_integral_pi_unique_Icc [Preorder α] (f : (ι → α) → E) (μ : Measure α) (a b : ι → α) :
    ∫ x in Icc a b, f x ∂(.pi fun _ ↦ μ) =
      ∫ x in Icc (a default) (b default), f (const ι x) ∂μ := by
  rw [← pi_univ_Icc, set_integral_pi_unique_pi]

theorem set_integral_pi_unique_Icc_eq_intervalIntegral (f : (ι → ℝ) → E) (μ : Measure ℝ)
    [NoAtoms μ] {a b : ι → ℝ} (h : a default ≤ b default) :
    ∫ x in Icc a b, f x ∂(.pi fun _ ↦ μ) = ∫ x in (a default)..(b default), f (const ι x) ∂μ := by
  rw [set_integral_pi_unique_Icc, intervalIntegral.integral_of_le h,
    restrict_congr_set Ioc_ae_eq_Icc.symm]

variable (ι)

theorem integral_eq_pi_unique (f : α → E) (μ : Measure α) :
    ∫ x, f x ∂μ = ∫ x : ι → α, f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| integral_pi_unique _ _

theorem set_integral_eq_pi_unique (f : α → E) (μ : Measure α) (s : Set α) :
    ∫ x in s, f x ∂μ = ∫ x : ι → α in eval default ⁻¹' s, f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| set_integral_pi_unique _ _ _

theorem set_integral_Icc_eq_pi_unique [Preorder α] (f : α → E) (μ : Measure α) (a b : α) :
    ∫ x in Icc a b, f x ∂μ = ∫ x in Icc (const ι a) (const ι b), f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| set_integral_pi_unique_Icc _ _ _ _

theorem intervalIntegral_eq_pi_unique (f : ℝ → E) (μ : Measure ℝ) [NoAtoms μ]
    {a b : ℝ} (h : a ≤ b) :
    ∫ x in a..b, f x ∂μ = ∫ x in Icc (const ι a) (const ι b), f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| set_integral_pi_unique_Icc_eq_intervalIntegral _ _ h

end Measure

variable [Unique ι] {α : Type _} [MeasureSpace α]

theorem integral_pi_unique_volume (f : (ι → α) → E) : ∫ x, f x = ∫ x, f (const ι x) :=
  integral_pi_unique _ _

theorem set_integral_pi_unique_volume (f : (ι → α) → E) (s : Set (ι → α)) :
    ∫ x in s, f x = ∫ x in const ι ⁻¹' s, f (const ι x) :=
  set_integral_pi_unique f _ s

theorem set_integral_pi_unique_pi_volume (f : (ι → α) → E) (s : ι → Set α) :
    ∫ x in Set.pi univ s, f x = ∫ x in s default, f (const ι x) :=
  set_integral_pi_unique_pi f _ s

theorem set_integral_pi_unique_Icc_volume [Preorder α] (f : (ι → α) → E) (a b : ι → α) :
    ∫ x in Icc a b, f x = ∫ x in Icc (a default) (b default), f (const ι x) :=
  set_integral_pi_unique_Icc _ _ _ _

theorem set_integral_pi_unique_Icc_volume_eq_intervalIntegral (f : (ι → ℝ) → E) {a b : ι → ℝ}
    (h : a default ≤ b default) :
    ∫ x in Icc a b, f x = ∫ x in (a default)..(b default), f (const ι x) :=
  set_integral_pi_unique_Icc_eq_intervalIntegral _ _ h

variable (ι)

theorem integral_volume_eq_pi_unique (f : α → E) : ∫ x, f x = ∫ x : ι → α, f (x default) :=
  integral_eq_pi_unique _ _ _

theorem set_integral_volume_eq_pi_unique (f : α → E) (s : Set α) :
    ∫ x in s, f x = ∫ x : ι → α in eval default ⁻¹' s, f (x default) :=
  set_integral_eq_pi_unique _ _ _ _

theorem set_integral_volume_Icc_eq_pi_unique [Preorder α] (f : α → E) (a b : α) :
    ∫ x in Icc a b, f x = ∫ x in Icc (const ι a) (const ι b), f (x default) :=
  Eq.symm <| set_integral_pi_unique_Icc _ _ _ _

theorem intervalIntegral_volume_eq_pi_unique (f : ℝ → E) {a b : ℝ} (h : a ≤ b) :
    ∫ x in a..b, f x = ∫ x in Icc (const ι a) (const ι b), f (x default) :=
  intervalIntegral_eq_pi_unique ι f _ h

end Unique

end MeasureTheory
