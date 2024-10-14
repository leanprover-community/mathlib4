/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Additive operations on iterated derivatives
-/

variable {𝕜 R E F: Type}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]


section
/-! ### Constant scalar multiplication -/
variable [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

theorem HasFTaylorSeriesUpToOn.const_smul
    {n : ℕ∞} {A : E → F} {A' : E → FormalMultilinearSeries 𝕜 E F} {s : Set E}
    (hA : HasFTaylorSeriesUpToOn n A A' s) (c : R) :
    HasFTaylorSeriesUpToOn n (c • A) (c • A') s where
  zero_eq x hx := congr(c • $(hA.zero_eq x hx))
  fderivWithin m hm x hx := (hA.fderivWithin m hm x hx).const_smul c
  cont m hm := (hA.cont m hm).const_smul c

theorem HasFTaylorSeriesUpTo.const_smul
    [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
    {n : ℕ∞} {A : E → F} {A' : E → FormalMultilinearSeries 𝕜 E F}
    (hA : HasFTaylorSeriesUpTo n A A') (c : R) :
    HasFTaylorSeriesUpTo n (c • A) (c • A') where
  zero_eq x := congr(c • $(hA.zero_eq x))
  fderiv m hm x := (hA.fderiv m hm x).const_smul c
  cont m hm := (hA.cont m hm).const_smul c

end

/-! ### Zero -/

@[simp]
theorem HasFTaylorSeriesUpTo.zero {n : ℕ∞} :
    HasFTaylorSeriesUpTo (𝕜 := 𝕜) n (0 : E → F) 0 where
  zero_eq x := rfl
  fderiv _ _ x := hasFDerivAt_zero_of_eventually_const 0 (by simp)
  cont _ _ := continuous_const

@[simp]
theorem HasFTaylorSeriesUpToOn.zero {n : ℕ∞} (s) :
    HasFTaylorSeriesUpToOn (𝕜 := 𝕜) n (0 : E → F) 0 s :=
  HasFTaylorSeriesUpTo.zero.hasFTaylorSeriesUpToOn _

/-! ### Addition -/

theorem HasFTaylorSeriesUpToOn.add
    {n : ℕ∞} {A B : E → F} {A' B' : E → FormalMultilinearSeries 𝕜 E F} {s : Set E}
    (hA : HasFTaylorSeriesUpToOn n A A' s) (hB : HasFTaylorSeriesUpToOn n B B' s) :
    HasFTaylorSeriesUpToOn n (fun x => A x + B x) (A' + B') s where
  zero_eq x hx := congr($(hA.zero_eq x hx) + $(hB.zero_eq x hx))
  fderivWithin m hm x hx := (hA.fderivWithin m hm x hx).add (hB.fderivWithin m hm x hx)
  cont m hm := (hA.cont m hm).add (hB.cont m hm)

theorem HasFTaylorSeriesUpTo.add
    {n : ℕ∞} {A B : E → F} {A' B' : E → FormalMultilinearSeries 𝕜 E F}
    (hA : HasFTaylorSeriesUpTo n A A') (hB : HasFTaylorSeriesUpTo n B B') :
    HasFTaylorSeriesUpTo n (fun x => A x + B x) (A' + B') where
  zero_eq x := congr($(hA.zero_eq x) + $(hB.zero_eq x))
  fderiv m hm x := (hA.fderiv m hm x).add (hB.fderiv m hm x)
  cont m hm := (hA.cont m hm).add (hB.cont m hm)

/-! ### Subtraction -/

theorem HasFTaylorSeriesUpToOn.sub
    {n : ℕ∞} {A B : E → F} {A' B' : E → FormalMultilinearSeries 𝕜 E F} {s : Set E}
    (hA : HasFTaylorSeriesUpToOn n A A' s) (hB : HasFTaylorSeriesUpToOn n B B' s) :
    HasFTaylorSeriesUpToOn n (fun x => A x - B x) (A' - B') s where
  zero_eq x hx := congr($(hA.zero_eq x hx) - $(hB.zero_eq x hx))
  fderivWithin m hm x hx := (hA.fderivWithin m hm x hx).sub (hB.fderivWithin m hm x hx)
  cont m hm := (hA.cont m hm).sub (hB.cont m hm)

theorem HasFTaylorSeriesUpTo.sub
    {n : ℕ∞} {A B : E → F} {A' B' : E → FormalMultilinearSeries 𝕜 E F}
    (hA : HasFTaylorSeriesUpTo n A A') (hB : HasFTaylorSeriesUpTo n B B') :
    HasFTaylorSeriesUpTo n (fun x => A x - B x) (A' - B') where
  zero_eq x := congr($(hA.zero_eq x) - $(hB.zero_eq x))
  fderiv m hm x := (hA.fderiv m hm x).sub (hB.fderiv m hm x)
  cont m hm := (hA.cont m hm).sub (hB.cont m hm)

/-! ### Summation -/

theorem HasFTaylorSeriesUpToOn.sum
    {n : ℕ∞} {ι : Type*} {A : ι → E → F} {A' : ι → E → FormalMultilinearSeries 𝕜 E F} {s' : Set E}
    {s : Finset ι}
    (h : ∀ i ∈ s, HasFTaylorSeriesUpToOn n (A i) (A' i) s') :
    HasFTaylorSeriesUpToOn n (fun x => ∑ i ∈ s, A i x) (∑ i ∈ s, A' i) s' := by
  induction s using Finset.cons_induction with
  | empty => exact .zero _
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons]
    exact .add (h _ <| Finset.mem_cons_self _ _) (ih fun i hi => h _ <| Finset.mem_cons_of_mem hi)

theorem HasFTaylorSeriesUpTo.sum
    {n : ℕ∞} {ι : Type*} {A : ι → E → F} {A' : ι → E → FormalMultilinearSeries 𝕜 E F}
    {s : Finset ι}
    (h : ∀ i ∈ s, HasFTaylorSeriesUpTo n (A i) (A' i)) :
    HasFTaylorSeriesUpTo n (fun x => ∑ i ∈ s, A i x) (∑ i ∈ s, A' i) := by
  induction s using Finset.cons_induction with
  | empty => exact .zero
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons]
    exact .add (h _ <| Finset.mem_cons_self _ _) (ih fun i hi => h _ <| Finset.mem_cons_of_mem hi)
