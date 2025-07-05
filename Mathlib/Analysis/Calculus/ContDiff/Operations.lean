/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `(⊤ : ℕ∞) : WithTop ℕ∞` with `∞` and `⊤ : WithTop ℕ∞` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

open scoped NNReal Nat ContDiff

universe u uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {b : E × F → G} {m n : WithTop ℕ∞} {p : E → FormalMultilinearSeries 𝕜 E F}

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section Pi

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {p' : ∀ i, E → FormalMultilinearSeries 𝕜 E (F' i)}
  {Φ : E → ∀ i, F' i} {P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}

theorem hasFTaylorSeriesUpToOn_pi {n : WithTop ℕ∞} :
    HasFTaylorSeriesUpToOn n (fun x i => φ i x)
        (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : ∀ m : ℕ, (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)
  · ext1 i
    exact (h i).zero_eq x hx
  · intro m hm x hx
    exact (L m).hasFDerivAt.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
  · intro m hm
    exact (L m).continuous.comp_continuousOn <| continuousOn_pi.2 fun i => (h i).cont m hm

@[simp]
theorem hasFTaylorSeriesUpToOn_pi' {n : WithTop ℕ∞} :
    HasFTaylorSeriesUpToOn n Φ P' s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
          (P' x m)) s := by
  convert hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x ↦ Φ x i); ext; rfl

theorem contDiffWithinAt_pi :
    ContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h ↦ ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _, fun m ↦ ?_⟩
    set L : (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i :=
      ContinuousMultilinearMap.piₗᵢ _ _
    change AnalyticOn 𝕜 (fun x ↦ L (fun i ↦ p i x m)) (⋂ i, u i)
    apply (L.analyticOnNhd univ).comp_analyticOn ?_ (mapsTo_univ _ _)
    exact AnalyticOn.pi (fun i ↦ (h'p i m).mono (iInter_subset _ _))
  | (n : ℕ∞) =>
    intro m hm
    choose u hux p hp using fun i => h i m hm
    exact ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _⟩

theorem contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩

theorem contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  contDiffWithinAt_pi

theorem contDiff_pi : ContDiff 𝕜 n Φ ↔ ∀ i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [← contDiffOn_univ, contDiffOn_pi]

@[fun_prop]
theorem contDiff_pi' (hΦ : ∀ i, ContDiff 𝕜 n fun x => Φ x i) : ContDiff 𝕜 n Φ :=
  contDiff_pi.2 hΦ

@[fun_prop]
theorem contDiffOn_pi' (hΦ : ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s) : ContDiffOn 𝕜 n Φ s :=
  contDiffOn_pi.2 hΦ

@[fun_prop]
theorem contDiffAt_pi' (hΦ : ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x) : ContDiffAt 𝕜 n Φ x :=
  contDiffAt_pi.2 hΦ

theorem contDiff_update [DecidableEq ι] (k : WithTop ℕ∞) (x : ∀ i, F' i) (i : ι) :
    ContDiff 𝕜 k (update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

variable (F') in
theorem contDiff_single [DecidableEq ι] (k : WithTop ℕ∞) (i : ι) :
    ContDiff 𝕜 k (Pi.single i : F' i → ∀ i, F' i) :=
  contDiff_update k 0 i

variable (𝕜 E)

@[fun_prop]
theorem contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι → E => f i :=
  contDiff_pi.mp contDiff_id i

@[fun_prop]
theorem contDiffAt_apply (i : ι) (f : ι → E) : ContDiffAt 𝕜 n (fun f : ι → E => f i) f :=
  (contDiff_apply 𝕜 E i).contDiffAt

@[fun_prop]
theorem contDiffOn_apply (i : ι) (s : Set (ι → E)) : ContDiffOn 𝕜 n (fun f : ι → E => f i) s :=
  (contDiff_apply 𝕜 E i).contDiffOn

theorem contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι → ι' → E => f i j :=
  contDiff_pi.mp (contDiff_apply 𝕜 (ι' → E) i) j

end Pi

/-! ### Sum of two functions -/

section Add

theorem HasFTaylorSeriesUpToOn.add {n : WithTop ℕ∞} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
    (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g) (p + q) s := by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prodMk hg)

-- The sum is smooth.
@[fun_prop]
theorem contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  contDiff_add.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x + g x :=
  contDiff_add.comp (hf.prodMk hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx =>
  (hf x hx).add (hg x hx)

variable {i : ℕ}

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
See also `iteratedFDerivWithin_add_apply'`, which uses the spelling `(fun x ↦ f x + g x)`
instead of `f + g`. -/
theorem iteratedFDerivWithin_add_apply {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (f + g) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x := by
  have := (hf.eventually (by simp)).and (hg.eventually (by simp))
  obtain ⟨t, ht, hxt, h⟩ := mem_nhdsWithin.mp this
  have hft : ContDiffOn 𝕜 i f (s ∩ t) := fun a ha ↦ (h (by simp_all)).1.mono inter_subset_left
  have hgt : ContDiffOn 𝕜 i g (s ∩ t) := fun a ha ↦ (h (by simp_all)).2.mono inter_subset_left
  have hut : UniqueDiffOn 𝕜 (s ∩ t) := hu.inter ht
  have H : ↑(s ∩ t) =ᶠ[𝓝 x] s :=
    inter_eventuallyEq_left.mpr (eventually_of_mem (ht.mem_nhds hxt) (fun _ h _ ↦ h))
  rw [← iteratedFDerivWithin_congr_set H, ← iteratedFDerivWithin_congr_set H,
    ← iteratedFDerivWithin_congr_set H]
  exact .symm (((hft.ftaylorSeriesWithin hut).add
      (hgt.ftaylorSeriesWithin hut)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hut ⟨hx, hxt⟩)

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
This is the same as `iteratedFDerivWithin_add_apply`, but using the spelling `(fun x ↦ f x + g x)`
instead of `f + g`, which can be handy for some rewrites.
TODO: use one form consistently. -/
theorem iteratedFDerivWithin_add_apply' {f g : E → F} (hf : ContDiffWithinAt 𝕜 i f s x)
    (hg : ContDiffWithinAt 𝕜 i g s x) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (fun x => f x + g x) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x :=
  iteratedFDerivWithin_add_apply hf hg hu hx

theorem iteratedFDeriv_add_apply {i : ℕ} {f g : E → F}
    (hf : ContDiffAt 𝕜 i f x) (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (f + g) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

theorem iteratedFDeriv_add_apply' {i : ℕ} {f g : E → F} (hf : ContDiffAt 𝕜 i f x)
    (hg : ContDiffAt 𝕜 i g x) :
    iteratedFDeriv 𝕜 i (fun x => f x + g x) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x :=
  iteratedFDeriv_add_apply hf hg

end Add

/-! ### Negative -/

section Neg

-- The negative is smooth.
@[fun_prop]
theorem contDiff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.contDiff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
@[fun_prop]
theorem ContDiffWithinAt.neg {s : Set E} {f : E → F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
@[fun_prop]
theorem ContDiffAt.neg {f : E → F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => -f x) x := by rw [← contDiffWithinAt_univ] at *; exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
@[fun_prop]
theorem ContDiff.neg {f : E → F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  contDiff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.neg {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => -f x) s := fun x hx => (hf x hx).neg

variable {i : ℕ}

-- TODO: define `Neg` instance on `ContinuousLinearEquiv`,
-- prove it from `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`
theorem iteratedFDerivWithin_neg_apply {f : E → F} (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (-f) s x = -iteratedFDerivWithin 𝕜 i f s x := by
  induction' i with i hi generalizing x
  · ext; simp
  · ext h
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        rfl
      _ = fderivWithin 𝕜 (-iteratedFDerivWithin 𝕜 i f s) s x (h 0) (Fin.tail h) := by
        rw [fderivWithin_congr' (@hi) hx]; rfl
      _ = -(fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i f s) s) x (h 0) (Fin.tail h) := by
        rw [fderivWithin_neg (hu x hx)]; rfl
      _ = -(iteratedFDerivWithin 𝕜 (i + 1) f s) x h := rfl

theorem iteratedFDeriv_neg_apply {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)

end Neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x - g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-! ### Sum of finitely many functions -/

@[fun_prop]
theorem ContDiffWithinAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E} {x : E}
    (h : ∀ i ∈ s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
    ContDiffWithinAt 𝕜 n (fun x => ∑ i ∈ s, f i x) t x := by
  classical
    induction' s using Finset.induction_on with i s is IH
    · simp [contDiffWithinAt_const]
    · simp only [is, Finset.sum_insert, not_false_iff]
      exact (h _ (Finset.mem_insert_self i s)).add
        (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))

@[fun_prop]
theorem ContDiffAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {x : E}
    (h : ∀ i ∈ s, ContDiffAt 𝕜 n (fun x => f i x) x) :
    ContDiffAt 𝕜 n (fun x => ∑ i ∈ s, f i x) x := by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

@[fun_prop]
theorem ContDiffOn.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn 𝕜 n (fun x => f i x) t) :
    ContDiffOn 𝕜 n (fun x => ∑ i ∈ s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

@[fun_prop]
theorem ContDiff.sum {ι : Type*} {f : ι → E → F} {s : Finset ι}
    (h : ∀ i ∈ s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i ∈ s, f i x := by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h

theorem iteratedFDerivWithin_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : ∀ j ∈ u, ContDiffWithinAt 𝕜 i (f j) s x) :
    iteratedFDerivWithin 𝕜 i (∑ j ∈ u, f j ·) s x =
      ∑ j ∈ u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  induction u using Finset.cons_induction with
  | empty => ext; simp [hs, hx]
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [iteratedFDerivWithin_add_apply' h.1 (ContDiffWithinAt.sum h.2) hs hx, IH h.2]

theorem iteratedFDeriv_sum {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ}
    (h : ∀ j ∈ u, ContDiff 𝕜 i (f j)) :
    iteratedFDeriv 𝕜 i (∑ j ∈ u, f j ·) = ∑ j ∈ u, iteratedFDeriv 𝕜 i (f j) :=
  funext fun x ↦ by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (mem_univ x) (h · · |>.contDiffWithinAt)

/-! ### Product of two functions -/

section MulProd

variable {𝔸 𝔸' ι 𝕜' : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [NormedCommRing 𝔸']
  [NormedAlgebra 𝕜 𝔸'] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

-- The product is smooth.
@[fun_prop]
theorem contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2 :=
  (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
@[fun_prop]
theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  contDiff_mul.comp_contDiffWithinAt (hf.prodMk hg)

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
nonrec theorem ContDiffAt.mul {f g : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x :=
  hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.mul {f g : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.mul {f g : E → 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x * g x :=
  contDiff_mul.comp (hf.prodMk hg)

@[fun_prop]
theorem contDiffWithinAt_prod' {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i ∈ t, f i) s x :=
  Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

@[fun_prop]
theorem contDiffWithinAt_prod {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) :
    ContDiffWithinAt 𝕜 n (fun y => ∏ i ∈ t, f i y) s x := by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

@[fun_prop]
theorem contDiffAt_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (∏ i ∈ t, f i) x :=
  contDiffWithinAt_prod' h

@[fun_prop]
theorem contDiffAt_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (fun y => ∏ i ∈ t, f i y) x :=
  contDiffWithinAt_prod h

@[fun_prop]
theorem contDiffOn_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (∏ i ∈ t, f i) s := fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

@[fun_prop]
theorem contDiffOn_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (fun y => ∏ i ∈ t, f i y) s := fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

@[fun_prop]
theorem contDiff_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n (∏ i ∈ t, f i) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

@[fun_prop]
theorem contDiff_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n fun y => ∏ i ∈ t, f i y :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

@[fun_prop]
theorem ContDiff.pow {f : E → 𝔸} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by simpa using contDiff_const
  | m + 1 => by simpa [pow_succ] using (hf.pow m).mul hf

@[fun_prop]
theorem ContDiffWithinAt.pow {f : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (contDiff_id.pow m).comp_contDiffWithinAt hf

@[fun_prop]
nonrec theorem ContDiffAt.pow {f : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : ℕ) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

@[fun_prop]
theorem ContDiffOn.pow {f : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) :
    ContDiffOn 𝕜 n (fun y => f y ^ m) s := fun y hy => (hf y hy).pow m

@[fun_prop]
theorem ContDiffWithinAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

@[fun_prop]
nonrec theorem ContDiffAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

@[fun_prop]
theorem ContDiffOn.div_const {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
    ContDiffOn 𝕜 n (fun x => f x / c) s := fun x hx => (hf x hx).div_const c

@[fun_prop]
theorem ContDiff.div_const {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const


end MulProd

/-! ### Scalar multiplication -/

section SMul

-- The scalar multiplication is smooth.
@[fun_prop]
theorem contDiff_smul : ContDiff 𝕜 n fun p : 𝕜 × F => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
@[fun_prop]
theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x • g x) s x :=
  contDiff_smul.contDiffWithinAt.comp x (hf.prodMk hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
@[fun_prop]
theorem ContDiffAt.smul {f : E → 𝕜} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x • g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.smul {f : E → 𝕜} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x • g x :=
  contDiff_smul.comp (hf.prodMk hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x • g x) s := fun x hx =>
  (hf x hx).smul (hg x hx)

end SMul

/-! ### Constant scalar multiplication

TODO: generalize results in this section.

1. It should be possible to assume `[Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]`.
2. If `c` is a unit (or `R` is a group), then one can drop `ContDiff*` assumptions in some
  lemmas.
-/

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
variable [ContinuousConstSMul R F]

-- The scalar multiplication with a constant is smooth.
@[fun_prop]
theorem contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : F => c • p :=
  (c • ContinuousLinearMap.id 𝕜 F).contDiff

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
@[fun_prop]
theorem ContDiffWithinAt.const_smul {s : Set E} {f : E → F} {x : E} (c : R)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x :=
  (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
@[fun_prop]
theorem ContDiffAt.const_smul {f : E → F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun y => c • f y) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
@[fun_prop]
theorem ContDiff.const_smul {f : E → F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun y => c • f y :=
  (contDiff_const_smul c).comp hf

/-- The scalar multiplication of a constant and a `C^n` on a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.const_smul {s : Set E} {f : E → F} (c : R) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun y => c • f y) s := fun x hx => (hf x hx).const_smul c

variable {i : ℕ} {a : R}

theorem iteratedFDerivWithin_const_smul_apply (hf : ContDiffWithinAt 𝕜 i f s x)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (a • f) s x = a • iteratedFDerivWithin 𝕜 i f s x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl

theorem iteratedFDeriv_const_smul_apply (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDeriv_comp_left hf le_rfl

theorem iteratedFDeriv_const_smul_apply' (hf : ContDiffAt 𝕜 i f x) :
    iteratedFDeriv 𝕜 i (fun x ↦ a • f x) x = a • iteratedFDeriv 𝕜 i f x :=
  iteratedFDeriv_const_smul_apply hf

end ConstSMul

/-! ### Cartesian product of two functions -/

section prodMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
theorem ContDiffWithinAt.prodMap' {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {p : E × E'}
    (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n g t p.2) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p :=
  (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))

@[deprecated (since := "2025-03-09")]
alias ContDiffWithinAt.prod_map' := ContDiffWithinAt.prodMap'

@[fun_prop]
theorem ContDiffWithinAt.prodMap {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prodMap' hf hg

@[deprecated (since := "2025-03-09")]
alias ContDiffWithinAt.prod_map := ContDiffWithinAt.prodMap

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
@[fun_prop]
theorem ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prodMk
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

@[deprecated (since := "2025-03-09")]
alias ContDiffOn.prod_map := ContDiffOn.prodMap

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
theorem ContDiffAt.prodMap {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  simpa only [univ_prod_univ] using hf.prodMap hg

@[deprecated (since := "2025-03-09")]
alias ContDiffAt.prod_map := ContDiffAt.prodMap

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
@[fun_prop]
theorem ContDiffAt.prodMap' {f : E → F} {g : E' → F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p :=
  hf.prodMap hg

@[deprecated (since := "2025-03-09")]
alias ContDiffAt.prod_map' := ContDiffAt.prodMap'

/-- The product map of two `C^n` functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.prodMap {f : E → F} {g : E' → F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prodMap (hg y)

@[deprecated (since := "2025-03-09")]
alias ContDiff.prod_map := ContDiff.prodMap

@[fun_prop]
theorem contDiff_prodMk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  contDiff_id.prodMk contDiff_const

@[deprecated (since := "2025-03-09")]
alias contDiff_prod_mk_left := contDiff_prodMk_left

@[fun_prop]
theorem contDiff_prodMk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  contDiff_const.prodMk contDiff_id

@[deprecated (since := "2025-03-09")]
alias contDiff_prod_mk_right := contDiff_prodMk_right

end prodMap

/-!
### Inversion in a complete normed algebra (or more generally with summable geometric series)
-/

section AlgebraInverse

variable (𝕜)
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element, as it is analytic. -/
@[fun_prop]
theorem contDiffAt_ringInverse [HasSummableGeomSeries R] (x : Rˣ) :
    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

@[deprecated (since := "2025-04-22")] alias contDiffAt_ring_inverse := contDiffAt_ringInverse

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

@[fun_prop]
theorem contDiffAt_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [Ring.inverse_eq_inv'] using contDiffAt_ringInverse 𝕜 (Units.mk0 x hx)

@[fun_prop]
theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') {0}ᶜ := fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt

variable {𝕜}

@[fun_prop]
theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => (f x)⁻¹) s x :=
  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

@[fun_prop]
theorem ContDiffOn.inv {f : E → 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn 𝕜 n (fun x => (f x)⁻¹) s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

@[fun_prop]
nonrec theorem ContDiffAt.inv {f : E → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
    ContDiffAt 𝕜 n (fun x => (f x)⁻¹) x :=
  hf.inv hx

@[fun_prop]
theorem ContDiff.inv {f : E → 𝕜'} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
    ContDiff 𝕜 n fun x => (f x)⁻¹ := by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

-- TODO: generalize to `f g : E → 𝕜'`
@[fun_prop]
theorem ContDiffWithinAt.div {f g : E → 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

@[fun_prop]
theorem ContDiffOn.div {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

@[fun_prop]
theorem ContDiffOn.fun_div {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn 𝕜 n (fun x => f x / g x) s :=
  ContDiffOn.div hf hg h₀

@[fun_prop]
nonrec theorem ContDiffAt.div {f g : E → 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x ≠ 0) : ContDiffAt 𝕜 n (fun x => f x / g x) x :=
  hf.div hg hx

@[fun_prop]
theorem ContDiff.div {f g : E → 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : ∀ x, g x ≠ 0) : ContDiff 𝕜 n fun x => f x / g x := by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section MapInverse

open ContinuousLinearMap

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
@[fun_prop]
theorem contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) :
    ContDiffAt 𝕜 n inverse (e : E →L[𝕜] F) := by
  nontriviality E
  -- first, we use the lemma `inverse_eq_ringInverse` to rewrite in terms of `Ring.inverse` in the
  -- ring `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → F →L[𝕜] E := fun f => f.comp (e.symm : F →L[𝕜] E)
  let O₂ : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have : ContinuousLinearMap.inverse = O₁ ∘ Ring.inverse ∘ O₂ := funext (inverse_eq_ringInverse e)
  rw [this]
  -- `O₁` and `O₂` are `ContDiff`,
  -- so we reduce to proving that `Ring.inverse` is `ContDiff`
  have h₁ : ContDiff 𝕜 n O₁ := contDiff_id.clm_comp contDiff_const
  have h₂ : ContDiff 𝕜 n O₂ := contDiff_const.clm_comp contDiff_id
  refine h₁.contDiffAt.comp _ (ContDiffAt.comp _ ?_ h₂.contDiffAt)
  convert contDiffAt_ringInverse 𝕜 (1 : (E →L[𝕜] E)ˣ)
  simp [O₂, one_def]

/-- At an invertible map `e : M →L[R] M₂` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] {e : E →L[𝕜] F}
    (he : e.IsInvertible) : ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

end MapInverse

section FunctionInverse

open ContinuousLinearMap

/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.contDiffAt_symm [CompleteSpace E] (f : PartialHomeomorph E F)
    {f₀' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
    (hf₀' : HasFDerivAt f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a := by
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : ℕ∞) =>
    -- We prove this by induction on `n`
    induction' n using ENat.nat_induction with n IH Itop
    · apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuousOn_invFun⟩
    · obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hf
      apply contDiffAt_succ_iff_hasFDerivAt.2
      -- For showing `n.succ` times continuous differentiability (the main inductive step), it
      -- suffices to produce the derivative and show that it is `n` times continuously
      -- differentiable
      have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
      -- This follows by a bootstrapping formula expressing the derivative as a
      -- function of `f` itself
      refine ⟨inverse ∘ f' ∘ f.symm, ?_, ?_⟩
      · -- We first check that the derivative of `f` is that formula
        have h_nhds : { y : E | ∃ e : E ≃L[𝕜] F, ↑e = f' y } ∈ 𝓝 (f.symm a) := by
          have hf₀' := f₀'.nhds
          rw [← eq_f₀'] at hf₀'
          exact hf'.continuousAt.preimage_mem_nhds hf₀'
        obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (Filter.inter_mem hu h_nhds)
        use f.target ∩ f.symm ⁻¹' t
        refine ⟨IsOpen.mem_nhds ?_ ?_, ?_⟩
        · exact f.isOpen_inter_preimage_symm ht
        · exact mem_inter ha (mem_preimage.mpr htf)
        intro x hx
        obtain ⟨hxu, e, he⟩ := htu hx.2
        have h_deriv : HasFDerivAt f (e : E →L[𝕜] F) (f.symm x) := by
          rw [he]
          exact hff' (f.symm x) hxu
        convert f.hasFDerivAt_symm hx.1 h_deriv
        simp [← he]
      · -- Then we check that the formula, being a composition of `ContDiff` pieces, is
        -- itself `ContDiff`
        have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
          rw [eq_f₀']
          exact contDiffAt_map_inverse _
        have h_deriv₂ : ContDiffAt 𝕜 n f.symm a := by
          refine IH (hf.of_le ?_)
          norm_cast
          exact Nat.le_succ n
        exact (h_deriv₁.comp _ hf').comp _ h_deriv₂
    · refine contDiffAt_infty.mpr ?_
      intro n
      exact Itop n (contDiffAt_infty.mp hf n)

/-- If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.contDiff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E → E ≃L[𝕜] F}
    (hf₀' : ∀ a, HasFDerivAt f (f₀' a : E →L[𝕜] F) a) (hf : ContDiff 𝕜 n (f : E → F)) :
    ContDiff 𝕜 n (f.symm : F → E) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt

/-- Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜] (f : PartialHomeomorph 𝕜 𝕜)
    {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target) (hf₀' : HasDerivAt f f₀' (f.symm a))
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

/-- Let `f` be an `n` times continuously differentiable homeomorphism of a nontrivially normed
field.  Suppose that the derivative of `f` is never equal to zero. Then `f.symm` is `n` times
continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.contDiff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 → 𝕜}
    (h₀ : ∀ x, f' x ≠ 0) (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff 𝕜 n (f : 𝕜 → 𝕜)) :
    ContDiff 𝕜 n (f.symm : 𝕜 → 𝕜) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt

namespace PartialHomeomorph

variable (𝕜)

/-- Restrict a partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number or `ω`, but not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be open. -/
@[simps! apply symm_apply source target]
def restrContDiff (f : PartialHomeomorph E F) (n : WithTop ℕ∞) (hn : n ≠ ∞) :
    PartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx ↦ by
    simp [hx, and_comm]
  H.restr <| isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ ↦
    inter_mem (f.open_source.mem_nhds hxs) <| (hxf.eventually hn).and <|
    f.continuousAt hxs (hxf'.eventually hn)

lemma contDiffOn_restrContDiff_source (f : PartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ ∞) :
    ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n hn).source := fun _x hx ↦ hx.2.1.contDiffWithinAt

lemma contDiffOn_restrContDiff_target (f : PartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ ∞) :
    ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n hn).target := fun _x hx ↦ hx.2.1.contDiffWithinAt

end PartialHomeomorph

end FunctionInverse

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable (𝕜)
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
variable {p' : E → FormalMultilinearSeries 𝕜' E F}

theorem HasFTaylorSeriesUpToOn.restrictScalars {n : WithTop ℕ∞}
    (h : HasFTaylorSeriesUpToOn n f p' s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) :
    ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : ℕ∞) =>
    intro m hm
    rcases h m hm with ⟨u, u_mem, p', hp'⟩
    exact ⟨u, u_mem, _, hp'.restrictScalars _⟩

theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrict_scalars _

theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
  contDiffWithinAt_univ.1 <| h.contDiffWithinAt.restrict_scalars _

theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

end RestrictScalars
