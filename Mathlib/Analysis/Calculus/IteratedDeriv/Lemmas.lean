/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}
  -- For maximum generality, results about `smul` involve a second type besides `𝕜`,
  -- with varying hypotheses.
  -- * `R`: general type.
  {R : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- * `𝕝`: division semiring. (Addition in `𝕝` is not used, so the results would work with a
  -- `GroupWithZero` if we had a `DistribSMulWithZero` typeclass.)
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]
  -- * `𝔸`: normed `𝕜`-algebra.
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Module 𝔸 F] [IsBoundedSMul 𝔸 F]
    [IsScalarTower 𝕜 𝔸 F]
  -- * `𝕜'`: normed `𝕜`-division algebra.
  {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [ContinuousSMul 𝕜' F]

section one_dimensional


open scoped Topology

section

theorem Filter.EventuallyEq.iteratedDerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)

theorem Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (hfg : f =ᶠ[𝓝[insert x s] x] g) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))

theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s :=
  fun _ hx ↦ hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in
theorem iteratedDerivWithin_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx,
    ContinuousMultilinearMap.add_apply]

include h hx in
theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z ↦ f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using iteratedDerivWithin_add hx h hf hg

theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _

theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in
theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply (a := c) hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

include h hx in
theorem iteratedDerivWithin_fun_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun w ↦ c • f w) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
theorem iteratedDerivWithin_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), ← Pi.smul_def,
      derivWithin_const_smul_field]

include h hx in
theorem iteratedDerivWithin_const_mul (c : 𝔸) {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul hx h c hf

/-- A variant of `iteratedDerivWithin_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
theorem iteratedDerivWithin_fun_const_smul_field (c : 𝕝) (f : 𝕜 → F) :
    iteratedDerivWithin n (fun z => c • f z) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul_field c f

@[simp]
theorem iteratedDerivWithin_const_mul_field (c : 𝕜') (f : 𝕜 → 𝕜') :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x :=
  iteratedDerivWithin_fun_const_smul_field c f

include h hx in
theorem iteratedDerivWithin_smul_const {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (v : F) :
    iteratedDerivWithin n (fun y ↦ f y • v) s x = iteratedDerivWithin n f s x • v := by
  simp [iteratedDerivWithin, iteratedFDerivWithin_smul_const_apply hf h hx]

include h hx in
@[simp]
theorem iteratedDerivWithin_mul_const {f : 𝕜 → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (d : 𝔸) :
    iteratedDerivWithin n (fun z ↦ f z * d) s x = iteratedDerivWithin n f s x * d :=
  iteratedDerivWithin_smul_const hx h hf d

/-- A variant of `iteratedDerivWithin_mul_const` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
theorem iteratedDerivWithin_mul_const_field (f : 𝕜 → 𝕜') (d : 𝕜') :
    iteratedDerivWithin n (fun z ↦ f z * d) s x = iteratedDerivWithin n f s x * d := by
  induction n generalizing f x with
  | zero => simp
  | succ n IH =>
    simp_rw [iteratedDerivWithin_succ, funext (@IH · f), derivWithin_mul_const_field]

variable (f) in
omit h hx in
@[simp]
theorem iteratedDerivWithin_neg :
    iteratedDerivWithin n (-f) s x = -iteratedDerivWithin n f s x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [iteratedDerivWithin_succ]
    rw [← derivWithin.neg]
    congr with y
    exact IH

variable (f) in
theorem iteratedDerivWithin_fun_neg :
    iteratedDerivWithin n (fun z => -f z) s x = -iteratedDerivWithin n f s x :=
  iteratedDerivWithin_neg f

include h hx

theorem iteratedDerivWithin_sub
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f - g) s x =
      iteratedDerivWithin n f s x - iteratedDerivWithin n g s x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Pi.neg_def, iteratedDerivWithin_add hx h hf hg.neg,
    iteratedDerivWithin_fun_neg]

theorem iteratedDerivWithin_comp_const_smul (hf : ContDiffOn 𝕜 n f s) (c : 𝕜)
    (hs : Set.MapsTo (c * ·) s s) :
    iteratedDerivWithin n (fun x => f (c * x)) s x = c ^ n • iteratedDerivWithin n f s (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x ∈ s := hs hx
    have h₀ : s.EqOn
        (iteratedDerivWithin n (fun x ↦ f (c * x)) s)
        (fun x => c ^ n • iteratedDerivWithin n f s (c * x)) :=
      fun x hx => ih hx hf.of_succ
    have h₁ : DifferentiableWithinAt 𝕜 (iteratedDerivWithin n f s) s (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
    have h₂ : DifferentiableWithinAt 𝕜 (fun x => iteratedDerivWithin n f s (c * x)) s x := by
      rw [← Function.comp_def]
      apply DifferentiableWithinAt.comp
      · exact hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) h _ hcx
      · exact differentiableWithinAt_id'.const_mul _
      · exact hs
    rw [iteratedDerivWithin_succ, derivWithin_congr h₀ (ih hx hf.of_succ),
      derivWithin_fun_const_smul (c ^ n) h₂, iteratedDerivWithin_succ,
      ← Function.comp_def,
      derivWithin.scomp x h₁ (differentiableWithinAt_id'.const_mul _) hs,
      derivWithin_const_mul _ differentiableWithinAt_id', derivWithin_id' _ _ (h _ hx),
      smul_smul, mul_one, pow_succ]

lemma iteratedDerivWithin_id :
    iteratedDerivWithin n id s x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | n) := n
  · simp
  · rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr (g := fun _ ↦ 1) _ hx]
    · simp [iteratedDerivWithin_const]
    · exact fun y hy ↦ derivWithin_id _ _ (h.uniqueDiffWithinAt hy)

lemma iteratedDerivWithin_fun_id :
    iteratedDerivWithin n (·) s x = if n = 0 then x else if n = 1 then 1 else 0 :=
  iteratedDerivWithin_id hx h

lemma iteratedDerivWithin_smul {f : 𝕜 → 𝔸} {g : 𝕜 → F}
    (hf : ContDiffWithinAt 𝕜 (↑n) f s x) (hg : ContDiffWithinAt 𝕜 (↑n) g s x) :
    iteratedDerivWithin n (f • g) s x = ∑ i ∈ .range (n + 1),
      n.choose i • iteratedDerivWithin i f s x • iteratedDerivWithin (n - i) g s x := by
  induction n generalizing f g with
  | zero => simp
  | succ n IH =>
    obtain ⟨U, hU, H⟩ := ((hf.eventually (by simp)).and (hg.eventually (by simp))).exists_mem
    rw [iteratedDerivWithin_succ', Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := f • derivWithin g s + derivWithin f s • g)]
    · rw [Finset.sum_range_succ', iteratedDerivWithin_add hx h, IH, Finset.sum_range_succ', IH]
      · simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
        nth_rw 3 [Finset.sum_range_succ]
        have : ∀ i ∈ Finset.range n, 1 ≤ n - i := by simp; lia
        simp +contextual [← iteratedDerivWithin_succ', ← n.sub_sub, Nat.sub_add_cancel, this]
        abel
      all_goals clear IH H U hU; fun_prop (disch := simp_all)
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [derivWithin_smul (hfy.differentiableWithinAt _) (hgy.differentiableWithinAt _)]
      all_goals simp

lemma iteratedDerivWithin_mul {f g : 𝕜 → 𝔸}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f * g) s x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDerivWithin i f s x * iteratedDerivWithin (n - i) g s x := by
  simp [← smul_eq_mul, iteratedDerivWithin_smul hx h hf hg]

theorem iteratedDerivWithin_pow (m : ℕ) (k : ℕ) :
    iteratedDerivWithin k (· ^ m) s x = m.descFactorial k * x ^ (m - k) := by
  induction m generalizing k with
  | zero => cases k <;> simp [iteratedDerivWithin_const]
  | succ i IH =>
    obtain (_ | k) := k
    · simp
    simp only [pow_succ]
    refine (iteratedDerivWithin_mul hx h (by fun_prop) (by fun_prop)).trans ?_
    have : ((i + 1).descFactorial (k + 1)) =
        (k + 1) * (i.descFactorial k) + (i.descFactorial (k + 1)) := by
      rw [Nat.succ_descFactorial_succ]
      cases le_or_gt k i <;> simp [Nat.descFactorial, ← add_mul, *]; lia
    obtain hik | hik := le_or_gt i k <;>
      simp +contextual [IH, iteratedDerivWithin_fun_id, h, hx, Finset.sum_range_succ,
        show ∀ x ∈ Finset.range k, k + 1 - x ≠ 0 by simp; lia, -Nat.descFactorial_succ,
        show ∀ x ∈ Finset.range k, k + 1 - x ≠ 1 by simp; lia, this,
        Nat.descFactorial_eq_zero_iff_lt.mpr, hik,
        show k < i → i - k = (i - (k + 1) + 1) by lia]; ring

end

lemma iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_add (Set.mem_univ _) uniqueDiffOn_univ hf hg

-- TODO: `@[to_fun]` generates the wrong name. Same for the various lemmas below.
lemma iteratedDeriv_fun_add (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun z ↦ f z + g z) x = iteratedDeriv n f x + iteratedDeriv n g x :=
  iteratedDeriv_add hf hg

theorem iteratedDeriv_const_add (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c + f z) x = iteratedDeriv n f x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_add hn c

theorem iteratedDeriv_const_sub (hn : 0 < n) (c : F) :
    iteratedDeriv n (fun z => c - f z) x = iteratedDeriv n (-f) x := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_const_sub hn c

@[simp]
lemma iteratedDeriv_fun_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

@[simp]
lemma iteratedDeriv_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (-f) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

lemma iteratedDeriv_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_sub (Set.mem_univ _) uniqueDiffOn_univ hf hg

lemma iteratedDeriv_fun_sub (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun z ↦ f z - g z) x = iteratedDeriv n f x - iteratedDeriv n g x :=
  iteratedDeriv_sub hf hg

theorem iteratedDeriv_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiffAt 𝕜 n f x) (c : R) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

theorem iteratedDeriv_fun_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiffAt 𝕜 n f x) (c : R) :
    iteratedDeriv n (c • f ·) x = c • iteratedDeriv n f x :=
  iteratedDeriv_const_smul h c

/-- A variant of `iteratedDeriv_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
theorem iteratedDeriv_const_smul_field {n : ℕ} (c : 𝕝) (f : 𝕜 → F) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul_field (s := Set.univ) c f

/-- A variant of `iteratedDeriv_fun_const_smul` without differentiability assumption when
the scalar multiplication is by division ring elements. -/
@[simp]
theorem iteratedDeriv_fun_const_smul_field {n : ℕ} (c : 𝕝) (f : 𝕜 → F) :
    iteratedDeriv n (c • f ·) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_fun_const_smul_field (s := Set.univ) c f

theorem iteratedDeriv_smul_const {f : 𝕜 → 𝔸} (hf : ContDiffAt 𝕜 n f x) (v : F) :
    iteratedDeriv n (fun y ↦ f y • v) x = iteratedDeriv n f x • v := by
  simp [iteratedDeriv, iteratedFDeriv_smul_const_apply hf]

theorem iteratedDeriv_const_mul {n : ℕ} {f : 𝕜 → 𝔸} (c : 𝔸) (hf : ContDiffAt 𝕜 n f x) :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ c hf

/-- A variant of `iteratedDeriv_const_mul` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
theorem iteratedDeriv_const_mul_field {n : ℕ} (c : 𝕜') (f : 𝕜 → 𝕜') :
    iteratedDeriv n (c * f ·) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul_field (s := .univ) c f

/-- A variant of `iteratedDeriv_mul_const` without differentiability assumption when
the multiplication is in a division ring. -/
@[simp]
theorem iteratedDeriv_mul_const_field {n : ℕ} (f : 𝕜 → 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · * c) x = iteratedDeriv n f x * c := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_mul_const_field (s := .univ) f c

@[simp]
theorem iteratedDeriv_div_const {n : ℕ} (f : 𝕜 → 𝕜') (c : 𝕜') :
    iteratedDeriv n (f · / c) x = iteratedDeriv n f x / c := by
  simp [div_eq_mul_inv]

theorem iteratedDeriv_comp_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n • iteratedDeriv n f (c * x) := by
  funext x
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_comp_const_smul (Set.mem_univ x) uniqueDiffOn_univ (contDiffOn_univ.mpr h)
      c (Set.mapsTo_univ _ _)

theorem iteratedDeriv_comp_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiff 𝕜 n f) (c : 𝕜) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => c ^ n * iteratedDeriv n f (c * x) := by
  simpa only [smul_eq_mul] using iteratedDeriv_comp_const_smul h c

lemma iteratedDeriv_comp_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (-a) := by
  induction n generalizing a with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_smul]
  | succ n ih =>
    have ih' : iteratedDeriv n (fun x ↦ f (-x)) = fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (-x) :=
      funext ih
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih', pow_succ', neg_mul, one_mul,
      deriv_comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv_fun_const_smul_field,
      neg_smul]

lemma iteratedDeriv_id {n : ℕ} {x : 𝕜} :
    iteratedDeriv n id x = if n = 0 then x else if n = 1 then 1 else 0 := by
  obtain (_ | _ | n) := n <;>
    simp [iteratedDeriv_succ', iteratedDeriv_const]

lemma iteratedDeriv_fun_id {n : ℕ} {x : 𝕜} :
    iteratedDeriv n (fun a ↦ a) x = if n = 0 then x else if n = 1 then 1 else 0 :=
  iteratedDeriv_id

lemma iteratedDeriv_fun_id_zero :
    iteratedDeriv n (fun a ↦ a) (0 : 𝕜) = if n = 1 then 1 else 0 := by
  simp +contextual [iteratedDeriv_fun_id]

lemma iteratedDeriv_mul {f g : 𝕜 → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f * g) x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDeriv i f x * iteratedDeriv (n - i) g x := by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]
theorem iteratedDeriv_pow (m : ℕ) (k : ℕ) :
    iteratedDeriv k (· ^ m) x = m.descFactorial k * x ^ (m - k) := by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k

lemma iteratedDeriv_fun_mul {f g : 𝕜 → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun x ↦ f x * g x) x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDeriv i f x * iteratedDeriv (n - i) g x :=
  iteratedDeriv_mul hf hg

lemma iteratedDeriv_fun_pow_zero {n m : ℕ} :
    iteratedDeriv n (· ^ m) (0 : 𝕜) = if n = m then m.factorial else 0 := by
  obtain h | h | h := lt_trichotomy n m <;>
    simp_all [Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt.mpr, ne_of_lt, ne_of_gt]

lemma Filter.EventuallyEq.iteratedDeriv_eq (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} (hfg : f =ᶠ[𝓝 x] g) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  simp only [← iteratedDerivWithin_univ, iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [(hfg.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq hfg.eq_of_nhds n]

lemma Set.EqOn.iteratedDeriv_of_isOpen (hfg : Set.EqOn f g s) (hs : IsOpen s) (n : ℕ) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) s := by
  refine fun x hx ↦ Filter.EventuallyEq.iteratedDeriv_eq n ?_
  filter_upwards [IsOpen.mem_nhds hs hx] with a ha
  exact hfg ha

end one_dimensional

/-!
### Invariance of iterated derivatives under translation
-/

section shift_invariance

variable (n : ℕ) (f : 𝕜 → F) (s : 𝕜)

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedDeriv_comp_const_add :
    iteratedDeriv n (fun z ↦ f (s + z)) = fun t ↦ iteratedDeriv n f (s + t) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_const_add _ s

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedDeriv_comp_add_const :
    iteratedDeriv n (fun z ↦ f (z + s)) = fun t ↦ iteratedDeriv n f (t + s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n IH =>
    simpa only [iteratedDeriv_succ, IH] using funext <| deriv_comp_add_const _ s

lemma iteratedDeriv_comp_sub_const :
    iteratedDeriv n (fun z ↦ f (z - s)) = fun t ↦ iteratedDeriv n f (t - s) := by
  simp [sub_eq_add_neg, iteratedDeriv_comp_add_const]

lemma iteratedDeriv_comp_const_sub :
    iteratedDeriv n (fun z ↦ f (s - z)) = fun t ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f (s - t) := by
  simpa [funext_iff, neg_add_eq_sub, iteratedDeriv_comp_add_const] using
    iteratedDeriv_comp_neg n (fun z => f (z + s))

end shift_invariance

section sums

/-!
### Iterated derivatives of sums
-/
open Finset
variable {ι : Type*} {n : ℕ} {x : 𝕜} {f : ι → 𝕜 → F} {I : Finset ι}

lemma iteratedDerivWithin_sum {s : Set 𝕜} (hx : x ∈ s) (hs : UniqueDiffOn 𝕜 s)
    (hf : ∀ i ∈ I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i ∈ I, f i) s x =
      ∑ i ∈ I, iteratedDerivWithin n (f i) s x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [forall_mem_insert] at hf
    simp only [sum_insert hi, sum_fn] at IH ⊢
    rw [iteratedDerivWithin_add hx hs hf.1 (.sum hf.2), IH hf.2]

lemma iteratedDerivWithin_fun_sum {s : Set 𝕜} (hx : x ∈ s) (hs : UniqueDiffOn 𝕜 s)
    (hf : ∀ i ∈ I, ContDiffWithinAt 𝕜 n (f i) s x) :
    iteratedDerivWithin n (∑ i ∈ I, f i ·) s x = ∑ i ∈ I, iteratedDerivWithin n (f i) s x :=
  by simpa [sum_fn] using iteratedDerivWithin_sum hx hs hf

lemma iteratedDeriv_sum (hf : ∀ i ∈ I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (∑ i ∈ I, f i) x = ∑ i ∈ I, iteratedDeriv n (f i) x := by
  simpa using iteratedDerivWithin_sum (Set.mem_univ x) uniqueDiffOn_univ hf

lemma iteratedDeriv_fun_sum (hf : ∀ i ∈ I, ContDiffAt 𝕜 n (f i) x) :
    iteratedDeriv n (fun z ↦ ∑ i ∈ I, f i z) x = ∑ i ∈ I, iteratedDeriv n (f i) x :=
  by simpa [sum_fn] using iteratedDeriv_sum hf

end sums
