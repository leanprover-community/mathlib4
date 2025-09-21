/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov, Eric Wieser
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives of functions taking values in product types

In this file we prove lemmas about derivatives of functions `f : 𝕜 → E × F` and of functions
`f : 𝕜 → (Π i, E i)`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative
-/

universe u v w

open Topology Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {s : Set 𝕜} {L : Filter 𝕜}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f₂ : 𝕜 → G} {f₂' : G}

nonrec theorem HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasDerivAtFilter f₂ f₂' x L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') x L :=
  hf₁.prodMk hf₂

@[deprecated (since := "2025-03-09")]
alias HasDerivAtFilter.prod := HasDerivAtFilter.prodMk

nonrec theorem HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  hf₁.prodMk hf₂

@[deprecated (since := "2025-03-09")]
alias HasDerivWithinAt.prod := HasDerivWithinAt.prodMk

nonrec theorem HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.prodMk hf₂

@[deprecated (since := "2025-03-09")]
alias HasDerivAt.prod := HasDerivAt.prodMk

nonrec theorem HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x)
    (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  hf₁.prodMk hf₂

@[deprecated (since := "2025-03-09")]
alias HasStrictDerivAt.prod := HasStrictDerivAt.prodMk

end CartesianProduct

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variable {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
  [∀ i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}

@[simp]
theorem hasStrictDerivAt_pi :
    HasStrictDerivAt φ φ' x ↔ ∀ i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  hasStrictFDerivAt_pi'

@[simp]
theorem hasDerivAtFilter_pi :
    HasDerivAtFilter φ φ' x L ↔ ∀ i, HasDerivAtFilter (fun x => φ x i) (φ' i) x L :=
  hasFDerivAtFilter_pi'

theorem hasDerivAt_pi : HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi

theorem hasDerivWithinAt_pi :
    HasDerivWithinAt φ φ' s x ↔ ∀ i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  hasDerivAtFilter_pi

theorem derivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hsx
  · simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hsx, Pi.zero_def]

theorem deriv_pi (h : ∀ i, DifferentiableAt 𝕜 (fun x => φ x i) x) :
    deriv φ x = fun i => deriv (fun x => φ x i) x :=
  (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv

end Pi


/-!
### Derivatives of tuples `f : 𝕜 → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ → Type*}
variable [∀ i, NormedAddCommGroup (F' i)] [∀ i, NormedSpace 𝕜 (F' i)]
variable {φ : 𝕜 → F' 0} {φs : 𝕜 → ∀ i, F' (Fin.succ i)}

theorem hasStrictDerivAt_finCons {φ' : Π i, F' i} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictDerivAt φ (φ' 0) x ∧ HasStrictDerivAt φs (fun i => φ' i.succ) x :=
  hasStrictFDerivAt_finCons

/-- A variant of `hasStrictDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasStrictDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasStrictDerivAt φ φ' x ∧ HasStrictDerivAt φs φs' x :=
  hasStrictDerivAt_finCons

theorem HasStrictDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasStrictDerivAt φ φ' x) (hs : HasStrictDerivAt φs φs' x) :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasStrictDerivAt_finCons'.mpr ⟨h, hs⟩

theorem hasDerivAtFilter_finCons {φ' : Π i, F' i} {l : Filter 𝕜} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' x l ↔
      HasDerivAtFilter φ (φ' 0) x l ∧ HasDerivAtFilter φs (fun i => φ' i.succ) x l :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasDerivAtFilter_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasDerivAtFilter_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter 𝕜} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x l ↔
      HasDerivAtFilter φ φ' x l ∧ HasDerivAtFilter φs φs' x l :=
  hasDerivAtFilter_finCons

theorem HasDerivAtFilter.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter 𝕜}
    (h : HasDerivAtFilter φ φ' x l) (hs : HasDerivAtFilter φs φs' x l) :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x l :=
  hasDerivAtFilter_finCons'.mpr ⟨h, hs⟩

theorem hasDerivAt_finCons {φ' : Π i, F' i} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasDerivAt φ (φ' 0) x ∧ HasDerivAt φs (fun i => φ' i.succ) x :=
  hasDerivAtFilter_finCons

/-- A variant of `hasDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasDerivAt φ φ' x ∧ HasDerivAt φs φs' x :=
  hasDerivAt_finCons

theorem HasDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivAt φ φ' x) (hs : HasDerivAt φs φs' x) :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasDerivAt_finCons'.mpr ⟨h, hs⟩

theorem hasDerivWithinAt_finCons {φ' : Π i, F' i} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasDerivWithinAt φ (φ' 0) s x ∧ HasDerivWithinAt φs (fun i => φ' i.succ) s x :=
  hasDerivAtFilter_finCons

/-- A variant of `hasDerivWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasDerivWithinAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x ↔
      HasDerivWithinAt φ φ' s x ∧ HasDerivWithinAt φs φs' s x :=
  hasDerivAtFilter_finCons

theorem HasDerivWithinAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivWithinAt φ φ' s x) (hs : HasDerivWithinAt φs φs' s x) :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x :=
  hasDerivWithinAt_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `derivWithin_pi` and `deriv_pi`

end PiFin
