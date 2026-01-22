
import Mathlib.Analysis.Complex.Divisor
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.CartanBound
import Mathlib.Analysis.Complex.CartanInverseFactorBound
import Mathlib.Analysis.Complex.CartanMajorantBound
import Mathlib.Analysis.Complex.ExpPoly
import Mathlib.Analysis.Complex.ExpPoly.Growth
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Annulus


/-!
## The intrinsic Hadamard quotient (entire and zero-free)

We bundle the main "quotient step": if `f` is entire, nontrivial, and we have the summability
hypothesis for the divisor-indexed canonical product of genus `m`, then there is an entire function
`H` with no zeros such that

`f z = H z * z^(ord0) * divisorCanonicalProduct m f univ z`.

Internally we define `H` as the **normal form** (`toMeromorphicNFOn`) of the meromorphic quotient
`f / (z^ord0 * divisorCanonicalProduct ...)`; this takes care of the values at zeros without any
padding/`ZeroData` tricks.
-/

noncomputable section

namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

/- If `∏' fac = F`, and each inverse factor satisfies `‖(fac a)⁻¹‖ ≤ exp (b a)`, and all finite sums
`∑_{a∈s} b a` are bounded by `B`, then `‖F⁻¹‖ ≤ exp B`. -/
lemma hasProd_norm_inv_le_exp_of_pointwise_le_exp
    {α : Type*} {L : SummationFilter α} [NeBot L.filter]
    (fac : α → ℂ) {F : ℂ} (hprod : HasProd fac F L)
    (b : α → ℝ) (B : ℝ)
    (hterm : ∀ a, ‖(fac a)⁻¹‖ ≤ Real.exp (b a))
    (hB : ∀ s : Finset α, (∑ a ∈ s, b a) ≤ B) :
    ‖F⁻¹‖ ≤ Real.exp B := by
  classical
  by_cases hF0 : F = 0
  · subst hF0
    -- `‖0⁻¹‖ = 0 ≤ exp B`
    simpa using (le_of_lt (Real.exp_pos B))
  · have hprod_inv : HasProd (fun a : α => (fac a)⁻¹) (F⁻¹) L :=
      HasProd.inv₀ (hf := hprod) (ha := by simp [hF0])
    have hbound_fin : ∀ s : Finset α, ‖∏ a ∈ s, (fac a)⁻¹‖ ≤ Real.exp B := by
      intro s
      have hnorm_le : ‖∏ a ∈ s, (fac a)⁻¹‖ ≤ ∏ a ∈ s, ‖(fac a)⁻¹‖ :=
        Finset.norm_prod_le (s := s) (f := fun a : α => (fac a)⁻¹)
      have hprod_le :
          (∏ a ∈ s, ‖(fac a)⁻¹‖) ≤ Real.exp (∑ a ∈ s, b a) := by
        refine Finset.prod_le_exp_sum (s := s) (a := fun a => ‖(fac a)⁻¹‖) (b := b) ?_ ?_
        · intro a ha
          exact norm_nonneg _
        · intro a ha
          exact hterm a
      have hexp_le : Real.exp (∑ a ∈ s, b a) ≤ Real.exp B :=
        Real.exp_le_exp.2 (hB s)
      exact hnorm_le.trans (hprod_le.trans hexp_le)
    have hlim :
        Tendsto (fun s : Finset α => ∏ a ∈ s, (fac a)⁻¹) L.filter (𝓝 (F⁻¹)) := by
      simpa [HasProd] using hprod_inv
    have hlim_norm :
        Tendsto (fun s : Finset α => ‖∏ a ∈ s, (fac a)⁻¹‖) L.filter (𝓝 ‖F⁻¹‖) :=
      (continuous_norm.tendsto _).comp hlim
    have h_event_le : ∀ᶠ s in L.filter, ‖∏ a ∈ s, (fac a)⁻¹‖ ≤ Real.exp B :=
      Filter.Eventually.of_forall hbound_fin
    by_contra hcontra
    have hgt : Real.exp B < ‖F⁻¹‖ := lt_of_not_ge hcontra
    have hnhds : Set.Ioi (Real.exp B) ∈ 𝓝 ‖F⁻¹‖ := Ioi_mem_nhds hgt
    have h_event_gt :
        ∀ᶠ s in L.filter, ‖∏ a ∈ s, (fac a)⁻¹‖ ∈ Set.Ioi (Real.exp B) :=
      hlim_norm.eventually hnhds
    have hfalse : ∀ᶠ s in L.filter, False :=
      (h_event_gt.and h_event_le).mono (fun _ hs => (not_lt_of_ge hs.2 hs.1).elim)
    have hbot : (L.filter : Filter (Finset α)) = ⊥ :=
      (Filter.eventually_false_iff_eq_bot).1 hfalse
    exact (NeBot.ne (f := (L.filter : Filter (Finset α))) (by infer_instance)) hbot

/-- The “denominator” in the Hadamard quotient construction: the product of the origin factor
`z ^ (analyticOrderNatAt f 0)` and the canonical product built from the divisor of `f` (of genus `m`)
on `univ`. -/
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

theorem differentiable_hadamardDenom (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (hadamardDenom m f) := by
  classical
  have hcprod : Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    intro z
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  simpa [hadamardDenom] using (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod

theorem hadamardDenom_ne_zero_at {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : f z ≠ 0) :
    hadamardDenom m f z ≠ 0 := by
  classical
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hf) hnot
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    have : DifferentiableWithinAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) w :=
      hdiffOn w (by simp)
    exact this.differentiableAt (by simp)
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [hadamardDenom, hord0, divisorCanonicalProduct_zero]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
      have hcprod_cast :
          (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
        have : (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne

lemma analyticOrderNatAt_divisorCanonicalProduct_zero
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 := by
  classical
  have hcprod_entire :
      Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    intro w
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    exact (hdiffOn w (by simp)).differentiableAt (by simp)
  have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
      ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
  have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : divisorCanonicalProduct m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [divisorCanonicalProduct_zero]
  have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have : (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) = 0 := by
    simp [hcast, this]
  exact_mod_cast this

theorem analyticOrderNatAt_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (hadamardDenom m f) z = analyticOrderNatAt f z := by
  classical
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      exact hcprod_entire.analyticAt 0
    have hcprod0 : analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
      analyticOrderNatAt_divisorCanonicalProduct_zero (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ)) (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 = analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero
          (hf := (by
            intro w
            have hdiffOn :
                DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
              differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
            exact (hdiffOn w (by simp)).differentiableAt (by simp)))
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
      simpa [hadamardDenom] using
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA) (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = analyticOrderNatAt f z :=
      analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      exact hcprod_entire.analyticAt z
    have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (by
          intro w
          have hdiffOn :
              DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
            differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
          exact (hdiffOn w (by simp)).differentiableAt (by simp)))
        ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      simpa [hadamardDenom] using
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA) (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]

theorem divisor_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  classical
  ext z
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (hadamardDenom m f) z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := hadamardDenom m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := f) hf_entire z)
  simp [hden, hfz, analyticOrderNatAt_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum) z]

theorem divisor_hadamardQuotient_eq_zero
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ) = 0 := by
  classical
  have hf_mero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hden_mero : MeromorphicOn (hadamardDenom m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (hden_entire.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : hadamardDenom m f z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hf_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt f z1 ≠ ⊤ := by
      have hfAt : MeromorphicAt f z1 := hf_mero z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hfAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hden_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (hadamardDenom m f) z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt (hadamardDenom m f) z1 ≠ ⊤ := by
      have hdenAt : MeromorphicAt (hadamardDenom m f) z1 := hden_mero z1 (by simp)
      have hcont : ContinuousAt (hadamardDenom m f) z1 := (hden_entire.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, hadamardDenom m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hden1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, hadamardDenom m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hdenAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hden_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hinv_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have hinv_mero : MeromorphicOn (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) :=
      hden_mero.inv
    have hz1_ne_top : meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ ⊤ := by
      have hinvAt : MeromorphicAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hinv_mero z1 (by simp)
      have hcont_denom : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hcont_denom.inv₀ hden1
      have hinv1 : (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero hden1
      have hne_nhds : ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hinvAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hinv_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hdiv_denom : MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    divisor_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor (fun z : ℂ => f z * (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (hadamardDenom m f z)⁻¹) hf_mero (hden_mero.inv)
            hf_order_ne_top hinv_order_ne_top)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) - MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [hdiv_denom]

theorem exists_entire_nonzero_hadamardQuotient
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧
      (∀ z, H z ≠ 0) ∧
      ∀ z : ℂ,
        f z =
          H z * z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  classical
  let denom : ℂ → ℂ := hadamardDenom m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have hden_entire : Differentiable ℂ denom :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hq_mero : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have hden_m : MeromorphicAt denom z := (hden_entire.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using (hf_m.mul hden_m.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hdivH : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      divisor_hadamardQuotient_eq_zero (m := m) (f := f) (hf := hf) (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using (MeromorphicOn.divisor_of_toMeromorphicNFOn (f := q) (U := (Set.univ : Set ℂ)) hq_mero)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have : (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤ MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [hdivH]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [hdivH])
  have hH_entire : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : denom z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hqA1 : AnalyticAt ℂ q z1 := by
    have hdenA1 : AnalyticAt ℂ denom z1 := hden_entire.analyticAt z1
    exact (hf.analyticAt z1).div hdenA1 hden1
  have hqNF1 : MeromorphicNFAt q z1 := hqA1.meromorphicNFAt
  have htoEq : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 hqNF1
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) hq_mero hx)
    simpa [H, htoEq] using this
  have hH1_ne : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 hden1
    simpa [hH1] using this
  have hH_not_top : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact analyticOrderAt_ne_top_of_exists_ne_zero (hf := hH_entire) ⟨z1, hH1_ne⟩
  have hH_orderNat_zero : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have hzdiv :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := H) hH_entire z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [hdivH]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [hzdiv] using this
    exact_mod_cast this
  have hH_ne : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (hH_not_top z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (hH_orderNat_zero z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have hdenA : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => hden_entire.analyticAt z
  have hprodA : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul hdenA)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have hden_ne : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (hden_entire.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hden1
    have hH_eq_q : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) hq_mero hx)
      simpa [H, htoEq] using hloc
    filter_upwards [hden_ne, hH_eq_q] with z hzden hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [hzden]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have hglob : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := hprodA) hlocal
  refine ⟨H, hH_entire, hH_ne, ?_⟩
  intro z
  have hglobz : f z = H z * denom z := congrArg (fun g => g z) hglob
  simpa [denom, hadamardDenom, mul_assoc, mul_left_comm, mul_comm] using hglobz


/-!
## Intrinsic Lindelöf summability: growth ⇒ summability of divisor-indexed exponents

This section is the first global ingredient needed to remove the final `sorry` in
`hadamard_factorization_of_growth`.

We derive the summability hypothesis required to form the intrinsic canonical product from the
growth bound on `log (1 + ‖f z‖)` by bounding the logarithmic counting function of the divisor.
-/

open scoped Real

lemma logCounting_divisor_univ_eq_circleAverage_sub_log_trailingCoeff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : R ≠ 0) :
    (Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R)
      = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := by
    intro z
    exact (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    (Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const (f := f)
      (h := hmero) (hR := hR))

lemma logCounting_divisor_univ_le_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR0 : 0 < R) :
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
      ≤ (Classical.choose hgrowth) * (1 + |R|) ^ ρ
        + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  classical
  set C : ℝ := Classical.choose hgrowth
  have hCpos : 0 < C := (Classical.choose_spec hgrowth).1
  have hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ :=
    (Classical.choose_spec hgrowth).2
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq := logCounting_divisor_univ_eq_circleAverage_sub_log_trailingCoeff (f := f) hf (R := R) hR
  have hf_sphere : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => Real.log ‖f z‖) 0 R :=
    circleIntegrable_log_norm_meromorphicOn hf_sphere
  have hbound_circle : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      Real.log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    have hz_norm : ‖z‖ = |R| := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hlog1 : Real.log ‖f z‖ ≤ Real.log (1 + ‖f z‖) := by
      by_cases h0 : f z = 0
      · simp [h0]
      · have hpos : 0 < ‖f z‖ := norm_pos_iff.2 h0
        have hle : ‖f z‖ ≤ 1 + ‖f z‖ := by linarith [norm_nonneg (f z)]
        exact Real.log_le_log hpos hle
    have hlog1' : Real.log ‖f z‖ ≤ C * (1 + ‖z‖) ^ ρ := le_trans hlog1 (hC z)
    simpa [hz_norm] using hlog1'
  have hCircleAvg_le :
      Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R) (f := fun z => Real.log ‖f z‖)
      hInt hbound_circle
  calc
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
        = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := hEq
    _ ≤ Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have : -Real.log ‖meromorphicTrailingCoeffAt f 0‖ ≤ |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (Real.log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

lemma countable_divisor_support_univ {f : ℂ → ℂ} :
    (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support.Countable := by
  classical
  set D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
    MeromorphicOn.divisor f (Set.univ : Set ℂ)
  have hclosed : IsClosed D.support := by
    simpa [D] using (D.closedSupport (hU := isClosed_univ))
  have hdisc : IsDiscrete D.support := by
    simpa [D] using (D.discreteSupport)
  have hL : IsLindelof (Set.univ : Set ℂ) := isLindelof_univ
  have hL' : IsLindelof D.support :=
    IsLindelof.of_isClosed_subset hL hclosed (by simp)
  simpa [D] using hL'.countable_of_isDiscrete hdisc

lemma logCounting_two_mul_lower_bound_sum_divisor_closedBall {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log 2) *
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
    MeromorphicOn.divisor f (Set.univ : Set ℂ)
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  have hr : r ≠ 0 := ne_of_gt hrpos
  have hDnonneg : 0 ≤ D := by
    have hAnal : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
      intro z hz
      simpa using (hf.analyticAt z)
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := (Set.univ : Set ℂ)) hAnal)
  let Dr : Function.locallyFinsuppWithin (Metric.closedBall (0 : ℂ) |r|) ℤ :=
    Function.locallyFinsuppWithin.toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : ℂ) |r|)
  let F : Finset ℂ := hDr_fin.toFinset
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hzS).2
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|))).1 hz_mem_SR
    have hz_in_ballR : z ∈ Metric.closedBall (0 : ℂ) |R| := by
      exact (Function.locallyFinsuppWithin.toClosedBall R D).supportWithinDomain hzR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have : ‖z‖ ≤ |R| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_in_ballR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hz_in_ballr : z ∈ Metric.closedBall (0 : ℂ) |r| := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm_le_r
    have hDrz : Dr z = D z := by
      simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
        (z := z) hz_in_ballr)
    have hDz_ne : D z ≠ 0 := by
      have hDz' : (Function.locallyFinsuppWithin.toClosedBall R D) z ≠ 0 := by
        simpa [Function.mem_support] using hzR
      have hz_in_ballR' : z ∈ Metric.closedBall (0 : ℂ) |R| := hz_in_ballR
      have hDz_eq : (Function.locallyFinsuppWithin.toClosedBall R D) z = D z := by
        simpa using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R) (f := D)
          (z := z) hz_in_ballR')
      simpa [hDz_eq] using hDz'
    have : z ∈ Dr.support := by
      simp [Function.mem_support, hDrz, hDz_ne]
    exact (Set.Finite.mem_toFinset hDr_fin).2 this
  have hlogCounting :
      Function.locallyFinsuppWithin.logCounting D r
        = (F.sum fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
    have hsupp :
        Function.support (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact (Set.Finite.mem_toFinset hDr_fin).2 this
    simp [Function.locallyFinsuppWithin.logCounting, D, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z : ℂ =>
        (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
        ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := (Set.Finite.mem_toFinset hDr_fin).1 hzF
      have hz_in : z ∈ Metric.closedBall (0 : ℂ) |r| := Dr.supportWithinDomain hz_sup
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z := by
          simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
            (z := z) hz_in)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ Real.log (r * ‖z‖⁻¹) := by
        by_cases hz0 : z = 0
        · subst hz0
          simp
        · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
          have hzle : ‖z‖ ≤ r := by
            have : ‖z‖ ≤ |r| := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_in
            simpa [abs_of_pos hrpos] using this
          have : 1 ≤ r * ‖z‖⁻¹ := by
            have : 1 ≤ r / ‖z‖ := (one_le_div hzpos).2 hzle
            simpa [div_eq_mul_inv] using this
          exact Real.log_nonneg this
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF hznot; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S,
        (Real.log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ 0 := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
          exact (Set.Finite.mem_toFinset
            (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
              (isCompact_closedBall (0 : ℂ) |R|))).1 hz_mem_SR
        have hz_in : z ∈ Metric.closedBall (0 : ℂ) |R| :=
          (Function.locallyFinsuppWithin.toClosedBall R D).supportWithinDomain hzRsup
        have : ‖z‖ ≤ |R| := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_in
        simpa [abs_of_pos hR0] using this
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hle2 : (2 : ℝ) ≤ r * ‖z‖⁻¹ := by
        have hRdiv : 1 ≤ R / ‖z‖ := (one_le_div hzpos).2 hz_norm_le_R
        have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
        simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hlog_le : Real.log 2 ≤ Real.log (r * ‖z‖⁻¹) :=
        Real.log_le_log (by positivity : (0 : ℝ) < 2) hle2
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ Metric.closedBall (0 : ℂ) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
          (z := z) hz_in_ballr)
      have : (Real.log 2) * (D z : ℝ) ≤ (Real.log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
          = S.sum (fun z : ℂ => (Real.log 2) * (D z : ℝ)) := by
              simp [Finset.mul_sum]
      _ ≤ S.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
            exact Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * Real.log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
      ≤ Function.locallyFinsuppWithin.logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [D, r, S, SR] using this

lemma sum_divisor_closedBall_le_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    ((((Function.locallyFinsuppWithin.finiteSupport
            (Function.locallyFinsuppWithin.toClosedBall R
              (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
            (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
        fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ ((Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) / (Real.log 2) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hlow :
      (Real.log 2) *
          ((((Function.locallyFinsuppWithin.finiteSupport
                  (Function.locallyFinsuppWithin.toClosedBall R
                    (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                  (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
            fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
        ≤ Function.locallyFinsuppWithin.logCounting
            (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) :=
    logCounting_two_mul_lower_bound_sum_divisor_closedBall (f := f) hf (R := R) hR
  have hupp :
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < (2 * R) := by nlinarith [hR0]
    simpa using (logCounting_divisor_univ_le_of_growth (f := f) (ρ := ρ) hf hgrowth (R := 2 * R) h2R0)
  have : (Real.log 2) *
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    le_trans hlow hupp
  have : ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ ((Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)
          / (Real.log 2) := by
    have hx :
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
            fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) * (Real.log 2)
          ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact (le_div_iff₀ hlog2pos).2 hx
  simpa using this

lemma sum_divisor_closedBall_mono {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    ((((Function.locallyFinsuppWithin.finiteSupport
            (Function.locallyFinsuppWithin.toClosedBall R₁
              (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
            (isCompact_closedBall (0 : ℂ) |R₁|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
        fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤
      ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R₂
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R₂|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
  classical
  have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR₁₂
  have habs₁ : |R₁| = R₁ := abs_of_nonneg hR₁
  have habs₂ : |R₂| = R₂ := abs_of_nonneg hR₂
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hAnal : AnalyticOnNhd ℂ f U := by
    intro z hz; simpa using (hf.analyticAt z)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := U) hAnal)
  let SR (R : ℝ) : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S (R : ℝ) : Finset ℂ := (SR R).filter fun z : ℂ => z ≠ 0
  have hsub : S R₁ ⊆ S R₂ := by
    intro z hz
    have hzSR₁ : z ∈ SR R₁ := (Finset.mem_filter.1 hz).1
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hz).2
    have hz_sup₁ :
        z ∈ (Function.locallyFinsuppWithin.toClosedBall R₁ D).support := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R₁ D)
          (isCompact_closedBall (0 : ℂ) |R₁|))).1 hzSR₁
    have hz_ball₁ : z ∈ Metric.closedBall (0 : ℂ) |R₁| :=
      (Function.locallyFinsuppWithin.toClosedBall R₁ D).supportWithinDomain hz_sup₁
    have hz_norm₁ : ‖z‖ ≤ R₁ := by
      have : ‖z‖ ≤ |R₁| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_ball₁
      simpa [habs₁] using this
    have hz_norm₂ : ‖z‖ ≤ R₂ := le_trans hz_norm₁ hR₁₂
    have hz_ball₂ : z ∈ Metric.closedBall (0 : ℂ) |R₂| := by
      have : ‖z‖ ≤ |R₂| := by simpa [habs₂] using hz_norm₂
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hEq₁ : (Function.locallyFinsuppWithin.toClosedBall R₁ D) z = D z := by
      simpa using
        (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R₁) (f := D)
          (z := z) hz_ball₁)
    have hEq₂ : (Function.locallyFinsuppWithin.toClosedBall R₂ D) z = D z := by
      simpa using
        (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R₂) (f := D)
          (z := z) hz_ball₂)
    have hDz_ne : D z ≠ 0 := by
      have : (Function.locallyFinsuppWithin.toClosedBall R₁ D) z ≠ 0 := by
        simpa [Function.mem_support] using hz_sup₁
      simpa [hEq₁] using this
    have hz_sup₂ : z ∈ (Function.locallyFinsuppWithin.toClosedBall R₂ D).support := by
      have : (Function.locallyFinsuppWithin.toClosedBall R₂ D) z ≠ 0 := by
        simpa [hEq₂] using hDz_ne
      simpa [Function.mem_support] using this
    have hzSR₂ : z ∈ SR R₂ := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R₂ D)
          (isCompact_closedBall (0 : ℂ) |R₂|))).2 hz_sup₂
    exact Finset.mem_filter.2 ⟨hzSR₂, hz0⟩
  have hterm_nonneg : ∀ z ∈ S R₂, 0 ≤ (MeromorphicOn.divisor f U z : ℝ) := by
    intro z hz
    have : 0 ≤ D z := hDnonneg z
    exact_mod_cast this
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz₂ _hznot => hterm_nonneg z hz₂)

lemma exists_r0_le_norm_divisorZeroIndex₀_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hAnal : AnalyticOnNhd ℂ f U := by
    intro z hz
    simpa using (hf.analyticAt z)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := U) hAnal)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀_val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀_val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact Ne.elim hA0 h
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ)) hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀_val p ∈ D.support := by
      simpa [D] using (divisorZeroIndex₀_val_mem_divisor_support (f := f) (U := U) p)
    have hnotBall : divisorZeroIndex₀_val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀_val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀_val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀_val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
      have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀_val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this

end Complex.Hadamard
