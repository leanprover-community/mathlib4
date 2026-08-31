/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.CPolynomialDef
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-! # Properties of continuously polynomial functions

We expand the API around continuously polynomial functions. Notably, we show that this class is
stable under the usual operations (addition, subtraction, negation).

We also prove that continuous multilinear maps are continuously polynomial, and so
are continuous linear maps into continuous multilinear maps. In particular, such maps are
analytic.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology Nat
open Set Filter ENNReal

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞} {n m : ℕ}
  {s : Set E}

theorem hasFiniteFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFiniteFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 ⊤ :=
  ⟨hasFPowerSeriesOnBall_const,
    fun _ hn ↦ constFormalMultilinearSeries_apply_of_nonzero (Nat.ne_zero_of_lt hn)⟩

theorem hasFiniteFPowerSeriesAt_const {c : F} {e : E} :
    HasFiniteFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e 1 :=
  ⟨⊤, hasFiniteFPowerSeriesOnBall_const⟩

theorem CPolynomialAt_const {v : F} : CPolynomialAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, 1, hasFiniteFPowerSeriesAt_const⟩

theorem CPolynomialOn_const {v : F} : CPolynomialOn 𝕜 (fun _ => v) s :=
  fun _ _ => CPolynomialAt_const

set_option backward.isDefEq.respectTransparency false in
theorem HasFiniteFPowerSeriesOnBall.add (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f + g) (pf + pg) x (max n m) r :=
  ⟨hf.1.add hg.1, fun N hN ↦ by
    rw [Pi.add_apply, hf.finite _ ((le_max_left n m).trans hN),
        hg.finite _ ((le_max_right n m).trans hN), zero_add]⟩

theorem HasFiniteFPowerSeriesAt.add (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

@[to_fun]
theorem CPolynomialAt.add (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f + g) x :=
  let ⟨_, _, hpf⟩ := hf
  let ⟨_, _, hqf⟩ := hg
  (hpf.add hqf).cpolynomialAt

set_option backward.isDefEq.respectTransparency false in
theorem HasFiniteFPowerSeriesOnBall.neg (hf : HasFiniteFPowerSeriesOnBall f pf x n r) :
    HasFiniteFPowerSeriesOnBall (-f) (-pf) x n r :=
  ⟨hf.1.neg, fun m hm ↦ by rw [Pi.neg_apply, hf.finite m hm, neg_zero]⟩

theorem HasFiniteFPowerSeriesAt.neg (hf : HasFiniteFPowerSeriesAt f pf x n) :
    HasFiniteFPowerSeriesAt (-f) (-pf) x n :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFiniteFPowerSeriesAt

@[to_fun]
theorem CPolynomialAt.neg (hf : CPolynomialAt 𝕜 f x) : CPolynomialAt 𝕜 (-f) x :=
  let ⟨_, _, hpf⟩ := hf
  hpf.neg.cpolynomialAt

theorem HasFiniteFPowerSeriesOnBall.sub (hf : HasFiniteFPowerSeriesOnBall f pf x n r)
    (hg : HasFiniteFPowerSeriesOnBall g pg x m r) :
    HasFiniteFPowerSeriesOnBall (f - g) (pf - pg) x (max n m) r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFiniteFPowerSeriesAt.sub (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f - g) (pf - pg) x (max n m) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]
theorem CPolynomialAt.sub (hf : CPolynomialAt 𝕜 f x) (hg : CPolynomialAt 𝕜 g x) :
    CPolynomialAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun]
theorem CPolynomialOn.add (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

@[to_fun]
theorem CPolynomialOn.sub (hf : CPolynomialOn 𝕜 f s) (hg : CPolynomialOn 𝕜 g s) :
    CPolynomialOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)

@[to_fun]
theorem CPolynomialAt.smul (hf : CPolynomialAt 𝕜 f x) (c : 𝕜) : CPolynomialAt 𝕜 (c • f) x :=
  ContinuousLinearMap.comp_cpolynomialAt ((ContinuousLinearMap.lsmul 𝕜 𝕜 c)) hf

@[to_fun]
theorem CPolynomialOn.smul (hf : CPolynomialOn 𝕜 f s) (c : 𝕜) : CPolynomialOn 𝕜 (c • f) s :=
  fun x hx ↦ (hf x hx).smul c

/-!
### Continuous multilinear maps

We show that continuous multilinear maps are continuously polynomial, and therefore analytic.
-/

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em F) {x : Π i, Em i} {s : Set (Π i, Em i)}

protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun _ hm ↦ dite_eq_right (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ ↦ by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeries, dite_eq_left rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dite_eq_right ne.symm]; rfl

lemma cpolynomialAt : CPolynomialAt 𝕜 f x :=
  f.hasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

lemma cpolynomialOn : CPolynomialOn 𝕜 f s := fun _ _ ↦ f.cpolynomialAt

lemma analyticOnNhd : AnalyticOnNhd 𝕜 f s := f.cpolynomialOn.analyticOnNhd

lemma analyticOn : AnalyticOn 𝕜 f s := f.analyticOnNhd.analyticOn

lemma analyticAt : AnalyticAt 𝕜 f x := f.cpolynomialAt.analyticAt

lemma analyticWithinAt : AnalyticWithinAt 𝕜 f s x := f.analyticAt.analyticWithinAt

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap

variable {ι : Type*} [Fintype ι] (f : E [⋀^ι]→L[𝕜] F) {x : Π (_ : ι), E} {s : Set (Π (_ : ι), E)}

lemma cpolynomialAt : CPolynomialAt 𝕜 f x :=
  ContinuousMultilinearMap.cpolynomialAt f.toContinuousMultilinearMap

lemma cpolynomialOn : CPolynomialOn 𝕜 f s := fun _ _ ↦ f.cpolynomialAt

lemma analyticOnNhd : AnalyticOnNhd 𝕜 f s := f.cpolynomialOn.analyticOnNhd

lemma analyticOn : AnalyticOn 𝕜 f s := f.analyticOnNhd.analyticOn

lemma analyticAt : AnalyticAt 𝕜 f x := f.cpolynomialAt.analyticAt

lemma analyticWithinAt : AnalyticWithinAt 𝕜 f s x := f.analyticAt.analyticWithinAt

/-- Precomposition on spaces of `n`-alternating maps, as a continuous linear map, is continuously
polynomial when multiplied by `(card ι)!`. -/
lemma cpolynomialAt_smul_compContinuousLinearMapCLM (f₀ : E →L[𝕜] F) :
    CPolynomialAt 𝕜 ((Fintype.card ι)! •
      compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ := by
  /- We decompose this map in three steps:
  * the canonical inclusion from alternating maps to multilinear maps (called `C` below)
  * precomposition on the space of multilinear maps (called `B`)
  * alternatization to go back from multilinear maps to alternating maps (called `A`)
  All these building blocks are continuously polynomial (as `A` and `C` can be seen as composition
  with linear maps, and `B` is a multilinear map), so their composition also is.
  The factor `(Fintype.card ι)!` comes out of the alternatization in this argument.
  Note that the naive argument to eliminate it fails, as follows.
  We would like to think that the map is polynomial of degree `card ι`, i.e., it should be
  written as `P (f, ..., f)` where `P` is multilinear. The natural candidate for `P` is
  `P (f₁, ..., fₙ) m (v₁, ..., vₙ) = m (f₁ v₁, ..., fₙ vₙ)`, i.e., apply the `fᵢ`coordinatewise.
  This is the formula used for multilinear maps.
  However, even if `m` is alternating, the map `m (f₁ v₁, ..., fₙ vₙ)` is not! So, `P` does not
  take its values in the correct space of alternating maps, and the argument fails.
  -/
  classical
  let A : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E) G →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
    ContinuousMultilinearMap.alternatizationCLM
  let B : ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ (E →L[𝕜] F))
      ((ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ F) G)
        →L[𝕜] (ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ E) G)) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear _ _ _ _
  let C : F [⋀^ι]→L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun (i : ι) ↦ F) G :=
    toContinuousMultilinearMapCLM 𝕜
  have : ((Fintype.card ι)! • compContinuousLinearMapCLM :
        (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) =
      (ContinuousLinearMap.compL _ _ _ _ A) ∘
        ((ContinuousLinearMap.compL _ _ _ _).flip C) ∘ (fun f ↦ B (fun i ↦ f)) := by
    ext f m : 2
    simp only [Pi.smul_apply, _root_.smul_apply, compContinuousLinearMapCLM_apply,
      ← ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap]
    rfl
  rw [this]
  apply ContinuousLinearMap.comp_cpolynomialAt
  apply ContinuousLinearMap.comp_cpolynomialAt
  apply CPolynomialAt.comp (ContinuousMultilinearMap.cpolynomialAt _) ?_
  exact ContinuousLinearMap.cpolynomialAt
    (ContinuousLinearMap.pi fun _ : ι ↦ ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)) f₀

variable [CharZero 𝕜]

/-- Precomposition on spaces of `n`-alternating maps, as a continuous linear map, is continuously
polynomial. -/
lemma cpolynomialAt_compContinuousLinearMapCLM (f₀ : E →L[𝕜] F) :
    CPolynomialAt 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ := by
  /- When multiplied by `(Fintype.card ι)!`, we have already proved the result above.
  As the field has characteristic zero, we can divide by this scalar factor.

  The result could also be proved by assuming instead that the field is complete and the spaces
  are finite-dimensional: in this case, the space of alternating maps is complemented in the space
  of multilinear maps, therefore there is a continuous linear projection on it. One can then follow
  the proof in `cpolynomialAt_smul_compContinuousLinearMapCLM` using this projection instead
  of `alternatization`, which eliminates the factorial.

  This corresponds to the sentence in Bourbaki, Variétés différentielles et analytiques,
  Paragraph 7.8: "We assume that 𝕜 has characteristic zero or that the vector bundles have finite
  dimension".
  -/
  have : (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) =
      ((Fintype.card ι)! : 𝕜)⁻¹ • ((Fintype.card ι)! • compContinuousLinearMapCLM) := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀, one_smul]
    simp [Nat.factorial_ne_zero]
  rw [this]
  apply CPolynomialAt.smul
  exact cpolynomialAt_smul_compContinuousLinearMapCLM f₀

/-- Precomposition on spaces of `n`-alternating maps, as a continuous linear map, is cpolynomial. -/
lemma cpolynomialOn_compContinuousLinearMapCLM (s : Set (E →L[𝕜] F)) :
    CPolynomialOn 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) s :=
  fun f _ ↦ cpolynomialAt_compContinuousLinearMapCLM f

lemma analyticOnNhd_compContinuousLinearMapCLM (s : Set (E →L[𝕜] F)) :
    AnalyticOnNhd 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) s :=
  (cpolynomialOn_compContinuousLinearMapCLM s).analyticOnNhd

lemma analyticOn_compContinuousLinearMapCLM (s : Set (E →L[𝕜] F)) :
    AnalyticOn 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) s :=
  (cpolynomialOn_compContinuousLinearMapCLM s).analyticOn

lemma analyticAt_compContinuousLinearMapCLM (f₀ : E →L[𝕜] F) :
    AnalyticAt 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ :=
  (cpolynomialAt_compContinuousLinearMapCLM f₀).analyticAt

lemma analyticWithinAt_compContinuousLinearMapCLM (s : Set (E →L[𝕜] F)) (f₀ : E →L[𝕜] F) :
    AnalyticWithinAt 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) s f₀ :=
  (analyticAt_compContinuousLinearMapCLM f₀).analyticWithinAt

end ContinuousAlternatingMap

/-!
### Continuous linear maps into continuous multilinear maps

We show that a continuous linear map into continuous multilinear maps is continuously polynomial
(as a function of two variables, i.e., uncurried). Therefore, it is also analytic.
-/

namespace ContinuousLinearMap

variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [Fintype ι] (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 Em F)
  {s : Set (G × (Π i, Em i))} {x : G × (Π i, Em i)}

/-- Formal multilinear series associated to a linear map into multilinear maps. -/
noncomputable def toFormalMultilinearSeriesOfMultilinear :
    FormalMultilinearSeries 𝕜 (G × (Π i, Em i)) F :=
  fun n ↦ if h : Fintype.card (Option ι) = n then
    (f.continuousMultilinearMapOption).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

protected theorem hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear :
    HasFiniteFPowerSeriesOnBall (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2)
      f.toFormalMultilinearSeriesOfMultilinear 0 (Fintype.card (Option ι) + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
  · intro m hm
    apply dite_eq_right
    exact Nat.ne_of_lt hm
  · intro y _
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeriesOfMultilinear, dite_eq_left rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeriesOfMultilinear, dite_eq_right ne.symm]; rfl

lemma cpolynomialAt_uncurry_of_multilinear :
    CPolynomialAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.hasFiniteFPowerSeriesOnBall_uncurry_of_multilinear.cpolynomialAt_of_mem
    (by simp only [Metric.eball_top, Set.mem_univ])

lemma cpolynomialOn_uncurry_of_multilinear :
    CPolynomialOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  fun _ _ ↦ f.cpolynomialAt_uncurry_of_multilinear

lemma analyticOnNhd_uncurry_of_multilinear :
    AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.cpolynomialOn_uncurry_of_multilinear.analyticOnNhd

lemma analyticOn_uncurry_of_multilinear :
    AnalyticOn 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_multilinear.analyticOn

lemma analyticAt_uncurry_of_multilinear : AnalyticAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_multilinear.analyticAt

lemma analyticWithinAt_uncurry_of_multilinear :
    AnalyticWithinAt 𝕜 (fun (p : G × (Π i, Em i)) ↦ f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_multilinear.analyticWithinAt

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {Em Fm : ι → Type*}
  [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
  [∀ i, NormedAddCommGroup (Fm i)] [∀ i, NormedSpace 𝕜 (Fm i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 Em (G →L[𝕜] F))
  {s : Set ((Π i, Em i) × G)} {x : (Π i, Em i) × G}

lemma cpolynomialAt_uncurry_of_linear :
    CPolynomialAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) x := by
  have : CPolynomialAt 𝕜 (ContinuousLinearEquiv.prodComm 𝕜 (Π i, Em i) G).toContinuousLinearMap x :=
    ContinuousLinearMap.cpolynomialAt _ _
  exact f.flipLinear.cpolynomialAt_uncurry_of_multilinear.comp this

lemma cpolyomialOn_uncurry_of_linear :
    CPolynomialOn 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  fun _ _ ↦ f.cpolynomialAt_uncurry_of_linear

lemma analyticOnNhd_uncurry_of_linear :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  f.cpolyomialOn_uncurry_of_linear.analyticOnNhd

lemma analyticOn_uncurry_of_linear :
    AnalyticOn 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s :=
  f.analyticOnNhd_uncurry_of_linear.analyticOn

lemma analyticAt_uncurry_of_linear : AnalyticAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) x :=
  f.cpolynomialAt_uncurry_of_linear.analyticAt

lemma analyticWithinAt_uncurry_of_linear :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Em i) × G) ↦ f p.1 p.2) s x :=
  f.analyticAt_uncurry_of_linear.analyticWithinAt

variable {t : Set ((Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))}
  {q : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G)}

lemma cpolynomialAt_uncurry_compContinuousLinearMap :
    CPolynomialAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) q :=
  cpolynomialAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

lemma cpolynomialOn_uncurry_compContinuousLinearMap :
    CPolynomialOn 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  cpolyomialOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

lemma analyticOnNhd_uncurry_compContinuousLinearMap :
    AnalyticOnNhd 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  analyticOnNhd_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

lemma analyticOn_uncurry_compContinuousLinearMap :
    AnalyticOn 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t :=
  analyticOn_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

lemma analyticAt_uncurry_compContinuousLinearMap :
    AnalyticAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) q :=
  analyticAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

lemma analyticWithinAt_uncurry_compContinuousLinearMap :
    AnalyticWithinAt 𝕜 (fun (p : (Π i, Fm i →L[𝕜] Em i) × (ContinuousMultilinearMap 𝕜 Em G))
      ↦ p.2.compContinuousLinearMap p.1) t q :=
  analyticWithinAt_uncurry_of_linear
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜 Fm Em G)

end ContinuousMultilinearMap
