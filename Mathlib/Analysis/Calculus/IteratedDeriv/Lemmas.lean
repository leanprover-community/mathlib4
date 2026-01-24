/-
Copyright (c) 2023 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Ruben Van de Velde
-/
module

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

section one_dimensional

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}
  {𝕜' : Type*} [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

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
  rw [iteratedFDerivWithin_const_smul_apply hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

include h hx in
theorem iteratedDerivWithin_const_mul (c : 𝕜) {f : 𝕜 → 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun z => c * f z) s x = c * iteratedDerivWithin n f s x := by
  simpa using iteratedDerivWithin_const_smul (F := 𝕜) hx h c hf

variable (f) in
omit h hx in
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

-- TODO: `𝕜'` could be generalized to normed algebras not necessarily fields.
lemma iteratedDerivWithin_smul {f : 𝕜 → 𝕜'} {g : 𝕜 → F}
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

lemma iteratedDerivWithin_mul {f g : 𝕜 → 𝕜'}
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

lemma iteratedDeriv_fun_neg (n : ℕ) (f : 𝕜 → F) (a : 𝕜) :
    iteratedDeriv n (fun x ↦ -(f x)) a = -(iteratedDeriv n f a) := by
  simpa only [← iteratedDerivWithin_univ] using iteratedDerivWithin_neg f

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

theorem iteratedDeriv_const_smul {n : ℕ} {f : 𝕜 → F} (h : ContDiffAt 𝕜 n f x) (c : 𝕜) :
    iteratedDeriv n (c • f) x = c • iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

theorem iteratedDeriv_const_mul {n : ℕ} {f : 𝕜 → 𝕜} (h : ContDiffAt 𝕜 n f x) (c : 𝕜) :
    iteratedDeriv n (fun z => c * f z) x = c * iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_const_mul (Set.mem_univ x) uniqueDiffOn_univ
      c (contDiffWithinAt_univ.mpr h)

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
      deriv_comp_neg (f := fun x ↦ (-1 : 𝕜) ^ n • iteratedDeriv n f x), deriv_fun_const_smul',
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

lemma iteratedDeriv_mul {f g : 𝕜 → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (f * g) x = ∑ i ∈ .range (n + 1),
      n.choose i * iteratedDeriv i f x * iteratedDeriv (n - i) g x := by
  simpa using iteratedDerivWithin_mul
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

@[simp]
theorem iteratedDeriv_pow (m : ℕ) (k : ℕ) :
    iteratedDeriv k (· ^ m) x = m.descFactorial k * x ^ (m - k) := by
  simpa using iteratedDerivWithin_pow (Set.mem_univ x) uniqueDiffOn_univ m k

lemma iteratedDeriv_fun_mul {f g : 𝕜 → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
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

variable {𝕜 F} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
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
