/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

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

- Relate integrals over `ι → α` and `ι' → α` given an equivalence `ι ≃ ι'`.
- Add a version of Fubini theorem: integrating over `ι → α` is the same as integrating over `s → α`,
  then over `sᶜ → α`, where `s : Set ι`. Can we reformulate it for two embeddings `ι₁ → ι` and
  `ι₂ → ι` with complement ranges?

## Keywords

integral, pi type
-/

open Function Set MeasureTheory.Measure

namespace MeasureTheory

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

section IsEmpty

/-!
### Integral over `(i : ι) → α i` with empty `ι`

If `ι` is an empty type (e.g., `Fin 0`), then `(i : ι) → α i` is a singleton, and a
`MeasureTheory.Measure.pi`-measure on this singleton is the Dirac measure. Thus integral of a
function over a `pi`-measure is equal to the value of this function at the unique point.
-/

section Measure

variable [CompleteSpace E] [IsEmpty ι] [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

theorem integral_pi_empty (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) :
    ∫ x, f x ∂(.pi μ) = f default := by
  rw [Measure.pi_of_empty, integral_dirac]; rfl

theorem setIntegral_pi_empty (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) {s : Set (∀ i, α i)}
    (hs : default ∈ s) : ∫ x in s, f x ∂(Measure.pi μ) = f default := by
  obtain rfl : s = univ := Subsingleton.eq_univ_of_nonempty ⟨_, hs⟩
  rw [restrict_univ, integral_pi_empty]

theorem setIntegral_pi_empty_pi (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i)) (I : Set ι)
    (s : ∀ i, Set (α i)) : ∫ x in I.pi s, f x ∂(Measure.pi μ) = f default :=
  setIntegral_pi_empty f μ isEmptyElim

theorem setIntegral_pi_empty_Icc [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (μ : ∀ i, Measure (α i)) (a b : (∀ i, α i)) :
    ∫ x in Icc a b, f x ∂(.pi μ) = f default :=
  setIntegral_pi_empty f μ ⟨isEmptyElim, isEmptyElim⟩

end Measure

variable [CompleteSpace E] [IsEmpty ι] [Fintype ι] {α : ι → Type*} [∀ i, MeasureSpace (α i)]

theorem integral_pi_empty_volume (f : (∀ i, α i) → E) : ∫ x, f x = f default :=
  integral_pi_empty _ _

theorem setIntegral_pi_empty_volume (f : (∀ i, α i) → E) {s : Set (∀ i, α i)} (hs : default ∈ s) :
    ∫ x in s, f x = f default :=
  setIntegral_pi_empty f _ hs

theorem setIntegral_pi_empty_pi_volume (f : (∀ i, α i) → E) (I : Set ι) (s : ∀ i, Set (α i)) :
    ∫ x in I.pi s, f x = f default :=
  setIntegral_pi_empty_pi f _ I s

theorem setIntegral_pi_empty_Icc_volume [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (a b : (∀ i, α i)) : ∫ x in Icc a b, f x = f default :=
  setIntegral_pi_empty_Icc _ _ _ _

end IsEmpty

section Unique

/-!
### Integrals of functions on types with a unique element

If `ι` has a unique element (e.g., `ι = Fin 1` or `ι = PUnit`), then `ι → α` is equivalent to `α`,
thus integrating over `ι → α` is equivalent to integrating over `α`. We provide lemmas that allow
rewriting between these two kinds of integrals in both directions.
-/

section Measure

variable [Unique ι] {α : Type*} {m : MeasurableSpace α}

theorem integral_pi_unique (f : (ι → α) → E) (μ : Measure α) :
    ∫ x, f x ∂(.pi fun _ ↦ μ) = ∫ x, f (const ι x) ∂μ :=
  .symm <| ((measurePreserving_funUnique _ _).symm _).integral_comp
    (MeasurableEquiv.measurableEmbedding _) _

theorem integrable_pi_unique {f : (ι → α) → F} {μ : Measure α} :
    Integrable f (.pi fun _ ↦ μ) ↔ Integrable (f <| const ι ·) μ :=
  .symm <| ((measurePreserving_funUnique _ _).symm _).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

theorem setIntegral_pi_unique (f : (ι → α) → E) (μ : Measure α) (s : Set (ι → α)) :
    ∫ x in s, f x ∂(.pi fun _ ↦ μ) = ∫ x in const ι ⁻¹' s, f (const ι x) ∂μ :=
  .symm <| ((measurePreserving_funUnique _ _).symm _).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) _ _

theorem integrableOn_pi_unique {f : (ι → α) → F} {μ : Measure α} {s : Set (ι → α)} :
    IntegrableOn f s (.pi fun _ ↦ μ) ↔ IntegrableOn (f <| const ι ·) (const ι ⁻¹' s) μ :=
  .symm <| ((measurePreserving_funUnique _ _).symm _).integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)

theorem setIntegral_pi_unique_pi (f : (ι → α) → E) (μ : Measure α) (s : ι → Set α) :
    ∫ x in Set.pi univ s, f x ∂(.pi fun _ ↦ μ) = ∫ x in s default, f (const ι x) ∂μ := by
  simp only [setIntegral_pi_unique, Set.preimage, Set.mem_univ_pi, Unique.forall_iff]
  rfl

theorem integrableOn_pi_unique_pi {f : (ι → α) → F} {μ : Measure α} {s : ι → Set α} :
    IntegrableOn f (univ.pi s) (.pi fun _ ↦ μ) ↔ IntegrableOn (f <| const ι ·) (s default) μ := by
  simp only [integrableOn_pi_unique, Set.preimage, Set.mem_univ_pi, Unique.forall_iff]
  rfl

theorem setIntegral_pi_unique_Icc [Preorder α] (f : (ι → α) → E) (μ : Measure α) (a b : ι → α) :
    ∫ x in Icc a b, f x ∂(.pi fun _ ↦ μ) =
      ∫ x in Icc (a default) (b default), f (const ι x) ∂μ := by
  rw [← pi_univ_Icc, setIntegral_pi_unique_pi]

theorem integrableOn_pi_unique_Icc [Preorder α] {f : (ι → α) → F} {μ : Measure α} {a b : ι → α} :
    IntegrableOn f (Icc a b) (.pi fun _ ↦ μ) ↔
      IntegrableOn (f <| const ι ·) (Icc (a default) (b default)) μ := by
  rw [← pi_univ_Icc, integrableOn_pi_unique_pi]

variable (ι)

theorem integral_eq_pi_unique (f : α → E) (μ : Measure α) :
    ∫ x, f x ∂μ = ∫ x : ι → α, f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| integral_pi_unique _ _

theorem setIntegral_eq_pi_unique (f : α → E) (μ : Measure α) (s : Set α) :
    ∫ x in s, f x ∂μ = ∫ x : ι → α in eval default ⁻¹' s, f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| setIntegral_pi_unique _ _ _

theorem setIntegral_Icc_eq_pi_unique [Preorder α] (f : α → E) (μ : Measure α) (a b : α) :
    ∫ x in Icc a b, f x ∂μ = ∫ x in Icc (const ι a) (const ι b), f (x default) ∂(.pi fun _ ↦ μ) :=
  Eq.symm <| setIntegral_pi_unique_Icc _ _ _ _

end Measure

variable [Unique ι] {α : Type*} [MeasureSpace α]

theorem integral_pi_unique_volume (f : (ι → α) → E) : ∫ x, f x = ∫ x, f (const ι x) :=
  integral_pi_unique _ _

theorem setIntegral_pi_unique_volume (f : (ι → α) → E) (s : Set (ι → α)) :
    ∫ x in s, f x = ∫ x in const ι ⁻¹' s, f (const ι x) :=
  setIntegral_pi_unique f _ s

theorem setIntegral_pi_unique_pi_volume (f : (ι → α) → E) (s : ι → Set α) :
    ∫ x in Set.pi univ s, f x = ∫ x in s default, f (const ι x) :=
  setIntegral_pi_unique_pi f _ s

theorem setIntegral_pi_unique_Icc_volume [Preorder α] (f : (ι → α) → E) (a b : ι → α) :
    ∫ x in Icc a b, f x = ∫ x in Icc (a default) (b default), f (const ι x) :=
  setIntegral_pi_unique_Icc _ _ _ _

variable (ι)

theorem integral_volume_eq_pi_unique (f : α → E) : ∫ x, f x = ∫ x : ι → α, f (x default) :=
  integral_eq_pi_unique _ _ _

theorem setIntegral_volume_eq_pi_unique (f : α → E) (s : Set α) :
    ∫ x in s, f x = ∫ x : ι → α in eval default ⁻¹' s, f (x default) :=
  setIntegral_eq_pi_unique _ _ _ _

theorem setIntegral_volume_Icc_eq_pi_unique [Preorder α] (f : α → E) (a b : α) :
    ∫ x in Icc a b, f x = ∫ x in Icc (const ι a) (const ι b), f (x default) :=
  Eq.symm <| setIntegral_pi_unique_Icc _ _ _ _

end Unique

section FinTwo

section Measure

variable {α : Type*} {m : MeasurableSpace α}

theorem integral_pi_fin_two (f : (Fin 2 → α) → E) (μ : Fin 2 → Measure α) [∀ i, SigmaFinite (μ i)] :
    ∫ x, f x ∂.pi μ = ∫ x : α × α, f ![x.1, x.2] ∂.prod (μ 0) (μ 1) :=
  Eq.symm <| ((measurePreserving_piFinTwo _).symm _).integral_comp
    (MeasurableEquiv.measurableEmbedding _) _

theorem integrable_pi_fin_two {f : (Fin 2 → α) → F} {μ : Fin 2 → Measure α}
    [∀ i, SigmaFinite (μ i)] :
    Integrable f (.pi μ) ↔ Integrable (fun x : α × α ↦ f ![x.1, x.2]) ((μ 0).prod (μ 1)) :=
  .symm <| ((measurePreserving_piFinTwo μ).symm _).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

theorem setIntegral_pi_fin_two (f : (Fin 2 → α) → E) (μ : Fin 2 → Measure α)
    [∀ i, SigmaFinite (μ i)] (s : Set (Fin 2 → α)) :
    ∫ x in s, f x ∂.pi μ =
      ∫ x : α × α in (fun x ↦ ![x.1, x.2]) ⁻¹' s, f ![x.1, x.2] ∂(μ 0).prod (μ 1) :=
  Eq.symm <| ((measurePreserving_piFinTwo _).symm _).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) _ _

theorem setIntegral_pi_fin_two_pi (f : (Fin 2 → α) → E) (μ : Fin 2 → Measure α)
    [∀ i, SigmaFinite (μ i)] (s : Fin 2 → Set α) :
    ∫ x in univ.pi s, f x ∂.pi μ = ∫ x : α × α in s 0 ×ˢ s 1, f ![x.1, x.2] ∂(μ 0).prod (μ 1) := by
  rw [setIntegral_pi_fin_two]
  congr with x
  simp [Fin.forall_fin_two]

theorem setIntegral_pi_fin_two_Icc [Preorder α] (f : (Fin 2 → α) → E) (μ : Fin 2 → Measure α)
    [∀ i, SigmaFinite (μ i)] (a b : Fin 2 → α) :
    ∫ x in Icc a b, f x ∂.pi μ =
      ∫ x in Icc (a 0, a 1) (b 0, b 1), f ![x.1, x.2] ∂(μ 0).prod (μ 1) := by
  rw [← pi_univ_Icc, setIntegral_pi_fin_two_pi, Icc_prod_Icc]

end Measure

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]

theorem integral_pi_fin_two_volume (f : (Fin 2 → α) → E) :
    ∫ x, f x = ∫ x : α × α, f ![x.1, x.2] :=
  integral_pi_fin_two ..

theorem setIntegral_pi_fin_two_volume (f : (Fin 2 → α) → E) (s : Set (Fin 2 → α)) :
    ∫ x in s, f x = ∫ x : α × α in (fun x ↦ ![x.1, x.2]) ⁻¹' s, f ![x.1, x.2] :=
  setIntegral_pi_fin_two ..

theorem setIntegral_pi_fin_two_pi_volume (f : (Fin 2 → α) → E) (s : Fin 2 → Set α) :
    ∫ x in univ.pi s, f x = ∫ x : α × α in s 0 ×ˢ s 1, f ![x.1, x.2] :=
  setIntegral_pi_fin_two_pi ..

theorem setIntegral_pi_fin_two_Icc_volume [Preorder α] (f : (Fin 2 → α) → E) (a b : Fin 2 → α) :
    ∫ x in Icc a b, f x = ∫ x in Icc (a 0, a 1) (b 0, b 1), f ![x.1, x.2] :=
  setIntegral_pi_fin_two_Icc ..

end FinTwo

section InsertNth

section Measure

variable {n : ℕ} {α : Fin (n + 1) → Type*} {m : ∀ i, MeasurableSpace (α i)}

theorem integral_pi_eq_integral_prod_pi_removeNth (f : (∀ i, α i) → E) (i : Fin (n + 1))
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :
    ∫ x, f x ∂.pi μ =
      ∫ x : α i × (∀ j, α (i.succAbove j)), f (i.insertNth x.1 x.2)
        ∂(μ i).prod (.pi (i.removeNth μ)) :=
  .symm <| ((measurePreserving_piFinSuccAbove _ _).symm _).integral_comp
    (MeasurableEquiv.measurableEmbedding _) _

theorem integrable_pi_iff_prod_pi_removeNth {f : (∀ i, α i) → F} {μ : ∀ i, Measure (α i)}
    [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1)) :
    Integrable f (.pi μ) ↔
      Integrable (fun x : α i × (∀ j, α (i.succAbove j)) ↦ f (i.insertNth x.1 x.2))
        ((μ i).prod (.pi (i.removeNth μ))) :=
  .symm <| ((measurePreserving_piFinSuccAbove _ _).symm _).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

theorem integral_pi_eq_integral_integral_pi_removeNth {f : (∀ i, α i) → E} {μ : ∀ i, Measure (α i)}
    [∀ i, SigmaFinite (μ i)] (hf : Integrable f (.pi μ)) (i : Fin (n + 1)) :
    ∫ x, f x ∂.pi μ = ∫ x, ∫ y, f (i.insertNth x y) ∂(.pi (i.removeNth μ)) ∂(μ i) := by
  rw [integrable_pi_iff_prod_pi_removeNth i] at hf
  rw [integral_pi_eq_integral_prod_pi_removeNth _ i]
  unfold Fin.removeNth at *
  rw [integral_prod _ hf]

theorem integral_pi_eq_integral_pi_removeNth_integral {f : (∀ i, α i) → E} {μ : ∀ i, Measure (α i)}
    [∀ i, SigmaFinite (μ i)] (hf : Integrable f (.pi μ)) (i : Fin (n + 1)) :
    ∫ x, f x ∂.pi μ = ∫ y, ∫ x, f (i.insertNth x y) ∂(μ i) ∂(.pi (i.removeNth μ)) := by
  rw [integrable_pi_iff_prod_pi_removeNth i] at hf
  rw [integral_pi_eq_integral_prod_pi_removeNth _ i]
  unfold Fin.removeNth at *
  rw [integral_prod_symm _ hf]

theorem setIntegral_pi_eq_setIntegral_preimage_prod_pi_insertNth (f : (∀ i, α i) → E)
    (i : Fin (n + 1)) (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (s : Set (∀ i, α i)) :
    ∫ x in s, f x ∂.pi μ =
      ∫ x : α i × (∀ j, α (i.succAbove j)) in (fun x ↦ i.insertNth x.1 x.2) ⁻¹' s,
        f (i.insertNth x.1 x.2) ∂(μ i).prod (.pi (i.removeNth μ)) :=
  .symm <| ((measurePreserving_piFinSuccAbove _ _).symm _).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) _ _

theorem setIntegral_pi_eq_setIntegral_prod_pi_removeNth (f : (∀ i, α i) → E) (i : Fin (n + 1))
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    ∫ x in univ.pi s, f x ∂.pi μ =
      ∫ x : α i × (∀ j, α (i.succAbove j)) in s i ×ˢ univ.pi (i.removeNth s),
        f (i.insertNth x.1 x.2) ∂(μ i).prod (.pi (i.removeNth μ)) := by
  convert setIntegral_pi_eq_setIntegral_preimage_prod_pi_insertNth f i μ _
  ext x
  simp [i.forall_iff_succAbove, Fin.removeNth]

theorem setIntegral_Icc_eq_setIntegral_prod_pi_removeNth [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (i : Fin (n + 1)) (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (a b : ∀ i, α i) :
    ∫ x in Icc a b, f x ∂.pi μ =
      ∫ x in Icc (a i) (b i) ×ˢ Icc (i.removeNth a) (i.removeNth b),
        f (i.insertNth x.1 x.2) ∂(μ i).prod (.pi (i.removeNth μ)) := by
  simp only [← pi_univ_Icc, setIntegral_fin_pi_eq_insertNth _ i, Icc_prod_Icc]
  rfl

end Measure

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasureSpace (α i)]
  [∀ i, SigmaFinite (volume : Measure (α i))]

theorem integral_fin_volume_eq_insertNth (f : (∀ i, α i) → E) (i : Fin (n + 1)) :
    ∫ x, f x =
      ∫ x : α i × (∀ j, α (i.succAbove j)), f (i.insertNth x.1 x.2) :=
  integral_fin_eq_insertNth ..

theorem setIntegral_fin_volume_eq_insertNth (f : (∀ i, α i) → E) (i : Fin (n + 1))
    (s : Set (∀ i, α i)) :
    ∫ x in s, f x =
      ∫ x : α i × (∀ j, α (i.succAbove j)) in (fun x ↦ i.insertNth x.1 x.2) ⁻¹' s,
        f (i.insertNth x.1 x.2) :=
  setIntegral_fin_eq_insertNth ..

theorem setIntegral_fin_pi_volume_eq_insertNth (f : (∀ i, α i) → E) (i : Fin (n + 1))
    (s : ∀ i, Set (α i)) :
    ∫ x in univ.pi s, f x =
      ∫ x : α i × (∀ j, α (i.succAbove j)) in s i ×ˢ univ.pi (i.removeNth s),
        f (i.insertNth x.1 x.2) :=
  setIntegral_fin_pi_eq_insertNth ..

theorem setIntegral_fin_Icc_volume_eq_insertNth [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (i : Fin (n + 1)) (a b : ∀ i, α i) :
    ∫ x in Icc a b, f x =
      ∫ x in Icc (a i) (b i) ×ˢ Icc (i.removeNth a) (i.removeNth b),
        f (i.insertNth x.1 x.2) :=
  setIntegral_fin_Icc_eq_insertNth ..

end InsertNth

section FinCons

section Measure

variable {n : ℕ} {α : Fin (n + 1) → Type*} {m : ∀ i, MeasurableSpace (α i)}

theorem integral_fin_eq_cons (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] :
    ∫ x, f x ∂.pi μ =
      ∫ x : α 0 × (∀ i : Fin n, α i.succ), f (Fin.cons x.1 x.2) ∂(μ 0).prod (.pi (Fin.tail μ)) := by
  simpa [Fin.insertNth_zero] using integral_fin_eq_insertNth f 0 μ

theorem setIntegral_fin_eq_cons (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (s : Set (∀ i, α i)) :
    ∫ x in s, f x ∂.pi μ =
      ∫ x : α 0 × (∀ i : Fin n, α i.succ) in (fun x ↦ Fin.cons x.1 x.2) ⁻¹' s,
        f (Fin.cons x.1 x.2) ∂(μ 0).prod (.pi (Fin.tail μ)) := by
  simpa [Fin.insertNth_zero] using setIntegral_fin_eq_insertNth f 0 μ s

theorem setIntegral_fin_pi_eq_cons (f : (∀ i, α i) → E) (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) :
    ∫ x in univ.pi s, f x ∂.pi μ =
      ∫ x : α 0 × (∀ i : Fin n, α i.succ) in s 0 ×ˢ univ.pi (Fin.tail s),
        f (Fin.cons x.1 x.2) ∂(μ 0).prod (.pi (Fin.tail μ)) := by
  simpa [Fin.insertNth_zero] using setIntegral_fin_pi_eq_insertNth f 0 μ s

theorem setIntegral_fin_Icc_eq_cons [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (a b : ∀ i, α i) :
    ∫ x in Icc a b, f x ∂.pi μ =
      ∫ x in Icc (a 0) (b 0) ×ˢ Icc (Fin.tail a) (Fin.tail b),
        f (Fin.cons x.1 x.2) ∂(μ 0).prod (.pi (Fin.tail μ)) := by
  simpa [Fin.insertNth_zero] using setIntegral_fin_Icc_eq_insertNth f 0 μ a b

end Measure

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasureSpace (α i)]
  [∀ i, SigmaFinite (volume : Measure (α i))]

theorem integral_fin_volume_eq_cons (f : (∀ i, α i) → E) :
    ∫ x, f x = ∫ x : α 0 × (∀ i : Fin n, α i.succ), f (Fin.cons x.1 x.2) :=
  integral_fin_eq_cons ..

theorem setIntegral_fin_volume_eq_cons (f : (∀ i, α i) → E) (s : Set (∀ i, α i)) :
    ∫ x in s, f x =
      ∫ x : α 0 × (∀ i : Fin n, α i.succ) in (fun x ↦ Fin.cons x.1 x.2) ⁻¹' s,
        f (Fin.cons x.1 x.2) :=
  setIntegral_fin_eq_cons ..

theorem setIntegral_fin_pi_volume_eq_cons (f : (∀ i, α i) → E) (s : ∀ i, Set (α i)) :
    ∫ x in univ.pi s, f x = ∫ x in s 0 ×ˢ univ.pi (Fin.tail s), f (Fin.cons x.1 x.2) :=
  setIntegral_fin_pi_eq_cons ..

theorem setIntegral_fin_Icc_volume_eq_cons [∀ i, Preorder (α i)] (f : (∀ i, α i) → E)
    (a b : ∀ i, α i) :
    ∫ x in Icc a b, f x =
      ∫ x in Icc (a 0) (b 0) ×ˢ Icc (Fin.tail a) (Fin.tail b), f (Fin.cons x.1 x.2) :=
  setIntegral_fin_Icc_eq_cons ..

end FinCons

end MeasureTheory

/-!
# Integration with respect to a finite product of measures

On a finite product of measure spaces, we show that a product of integrable functions each
depending on a single coordinate is integrable, in `MeasureTheory.integrable_fintype_prod`, and
that its integral is the product of the individual integrals,
in `MeasureTheory.integral_fintype_prod_eq_prod`.
-/

open Fintype MeasureTheory MeasureTheory.Measure

variable {𝕜 : Type*} [RCLike 𝕜]

namespace MeasureTheory

/-- On a finite product space in `n` variables, for a natural number `n`, a product of integrable
functions depending on each coordinate is integrable. -/
theorem Integrable.fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    {f : (i : Fin n) → E i → 𝕜} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun (x : (i : Fin n) → E i) ↦ ∏ i, f i (x i)) := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, volume_pi, isFiniteMeasure_iff,
      integrable_const_iff, one_ne_zero, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove (fun i => (volume : Measure (E i))) 0).symm)
      rw [volume_pi, ← this.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero]
      simp only [Fin.zero_succAbove, cast_eq, Function.comp_def, Fin.cons_zero, Fin.cons_succ]
      have : Integrable (fun (x : (j : Fin n) → E (Fin.succ j)) ↦ ∏ j, f (Fin.succ j) (x j)) :=
        n_ih (fun i ↦ hf _)
      exact Integrable.prod_mul (hf 0) this

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. Version with dependent target. -/
theorem Integrable.fintype_prod_dep {ι : Type*} [Fintype ι] {E : ι → Type*}
    {f : (i : ι) → E i → 𝕜} [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (hf : ∀ i, Integrable (f i)) :
    Integrable (fun (x : (i : ι) → E i) ↦ ∏ i, f i (x i)) := by
  let e := (equivFin ι).symm
  simp_rw [← (volume_measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i ↦ hf _)

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. -/
theorem Integrable.fintype_prod {ι : Type*} [Fintype ι] {E : Type*}
    {f : ι → E → 𝕜} [MeasureSpace E] [SigmaFinite (volume : Measure E)]
    (hf : ∀ i, Integrable (f i)) :
    Integrable (fun (x : ι → E) ↦ ∏ i, f i (x i)) :=
  Integrable.fintype_prod_dep hf

/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
theorem integral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  induction n with
  | zero =>
      simp only [volume_pi, Finset.univ_eq_empty, Finset.prod_empty, integral_const,
        pi_empty_univ, ENNReal.toReal_one, smul_eq_mul, mul_one, pow_zero, one_smul]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) := by
          rw [volume_pi, ← ((measurePreserving_piFinSuccAbove
            (fun i => (volume : Measure (E i))) 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, volume_eq_prod,
            volume_pi, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫ x, f 0 x) * ∏ i : Fin n, ∫ (x : E (Fin.succ i)), f (Fin.succ i) x := by
          rw [← n_ih, ← integral_prod_mul, volume_eq_prod]
        _ = ∏ i, ∫ x, f i x := by rw [Fin.prod_univ_succ]

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
theorem integral_fintype_prod_eq_prod (ι : Type*) [Fintype ι] {E : ι → Type*}
    (f : (i : ι) → E i → 𝕜) [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := by
  let e := (equivFin ι).symm
  rw [← (volume_measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

theorem integral_fintype_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] (f : E → 𝕜)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := by
  rw [integral_fintype_prod_eq_prod, Finset.prod_const, card]

end MeasureTheory
