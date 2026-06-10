/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Continuity of the continuous functional calculus in each variable

The continuous functional calculus is a map which takes a pair `a : A` (`A` is a C⋆-algebra) and
a function `f : C(spectrum R a, R)` where `a` satisfies some predicate `p`, depending on `R` and
returns another element of the algebra `A`. This is the map `cfcHom`. The class
`ContinuousFunctionalCalculus` declares that `cfcHom` is a continuous map from `C(spectrum R a, R)`
to `A`. However, users generally interact with the continuous functional calculus through `cfc`,
which operates on bare functions `f : R → R` instead and takes a junk value when `f` is not
continuous on the spectrum of `a`.  In this file we provide some lemma concerning the continuity
of `cfc`, subject to natural hypotheses.

However, the continuous functional calculus is *also* continuous in the variable `a`, but there
are some conditions that must be satisfied. In particular, given a function `f : R → R` the map
`a ↦ cfc f a` is continuous so long as `a` varies over a collection of elements satisfying the
predicate `p` and their spectra are collectively contained in a compact set on which `f` is
continuous. Moreover, it is required that the continuous functional calculus be the isometric
variant.

Under the assumption of `IsometricContinuousFunctionalCalculus`, we show that the continuous
functional calculus is Lipschitz with constant 1 in the variable `f : R →ᵤ[{spectrum R a}] R`
on the set of functions which are continuous on the spectrum of `a`. Combining this with the
continuity of the continuous functional calculus in the variable `a`, we obtain a joint continuity
result for `cfc` in both variables.

Finally, all of this is developed for both the unital and non-unital functional calculi.
The continuity results in the function variable are valid for all scalar rings, but the continuity
results in the variable `a` come in two flavors: those for `RCLike 𝕜` and those for `ℝ≥0`.

## Main results


+ `tendsto_cfc_fun`: If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and
  all these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
  to `cfc f a`.
+ `Filter.Tendsto.cfc`: If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to
  `a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
  `𝕜` and has spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to
  `cfc f a₀`.
+ `lipschitzOnWith_cfc_fun`: The function `f ↦ cfc f a` is Lipschitz with constant with constant 1
  with respect to supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are
  continuous on the spectrum.
+ `continuousOn_cfc`: For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the
  set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is
  contained in `s`.
+ `continuousOn_cfc_setProd`: Let `s : Set 𝕜` be a compact set and consider pairs
  `(f, a) : (𝕜 → 𝕜) × A` where `f` is continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies
  the predicate `p a` for the continuous functional calculus. Then `cfc` is jointly continuous in
  both variables (i.e., continuous in its uncurried form) on this set of pairs when the function
  space is equipped with the topology of uniform convergence on `s`.
+ Versions of all of the above for non-unital algebras, and versions over `ℝ≥0` as well.

-/

public section

open scoped UniformConvergence NNReal
open Filter Topology

section Unital

section Left

section Generic

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`. -/
theorem tendsto_cfc_fun {l : Filter X} {F : X → R → R} {f : R → R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : ∀ᶠ x in l, ContinuousOn (F x) (spectrum R a)) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
  open scoped ContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (spectrum R a)}
    rw [← tendsto_comap'_iff (i := ((↑) : s → X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply, cfc_apply (hf := x.2)]
    rw [cfc_apply ..]
    apply cfcHom_continuous _ |>.tendsto _ |>.comp
    rw [hf.tendsto_restrict_iff_tendstoUniformlyOn Subtype.property]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfc_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀`. -/
theorem continuousAt_cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : ∀ᶠ x in 𝓝 x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ :=
  tendsto_cfc_fun h_tendsto hf

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum of `a`,
and eventually each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀` within `s`. -/
theorem continuousWithinAt_cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (spectrum R a))
    (hf : ∀ᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousWithinAt (fun x ↦ cfc (f x) a) s x₀ :=
  tendsto_cfc_fun h_tendsto hf

open UniformOnFun in
/-- If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a`
is continuous on `s` also. -/
theorem ContinuousOn.cfc_fun [TopologicalSpace X] {f : X → R → R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x ↦ ofFun {spectrum R a} (f x)) s)
    (hf : ∀ x ∈ s, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx ↦ continuousWithinAt_cfc_fun (h_cont x hx) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hf x hx

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a` is continuous. -/
theorem Continuous.cfc_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfc_fun (fun x _ ↦ hf x)

end Generic

section Isometric

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are continuous on
the spectrum. -/
lemma lipschitzOnWith_cfc_fun (a : A) :
    LipschitzOnWith 1 (fun f ↦ cfc (toFun {spectrum R a} f) a)
      {f | ContinuousOn (toFun {spectrum R a} f) (spectrum R a)} := by
  by_cases ha : p a
  · intro f hf g hg
    simp only
    rw [cfc_apply .., cfc_apply .., isometry_cfcHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [edist_continuousRestrict_of_singleton hf hg]
  · simpa [cfc_apply_of_not_predicate a ha] using LipschitzWith.const' 0 |>.lipschitzOnWith

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfc f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a set `s` containing
the spectrum. -/
lemma lipschitzOnWith_cfc_fun_of_subset (a : A) {s : Set R} (hs : spectrum R a ⊆ s) :
    LipschitzOnWith 1 (fun f ↦ cfc (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s)} := by
  have h₁ := lipschitzOnWith_cfc_fun R a
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {spectrum R a}) (𝔗 := {s}) (β := R) (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s)})
  simpa using! h₁.comp h₃ (fun f hf ↦ hf.mono hs)

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

/-- `cfcHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
theorem continuous_cfcHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜))
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcHomSuperset (ha' x) (ha x) f) := by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.commutes] using! continuous_const
  | id =>
    simp only [cfcHomSuperset_id]
    fun_prop
  | star_id =>
    simp only [map_star, cfcHomSuperset_id]
    fun_prop
  | add f g hf hg => simpa using! hf.add hg
  | mul f g hf hg => simpa using! hf.mul hg
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcHom (ha' x)))]
    rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/-- For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the set of `a : A`
satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is contained in `s`. -/
theorem continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a | p a ∧ spectrum 𝕜 a ⊆ s} :=
  continuousOn_iff_continuous_restrict.mpr <| by
    convert!
      continuous_cfcHomSuperset_left hs ⟨_, hf.restrict⟩ ((↑) : {a | p a ∧ spectrum 𝕜 a ⊆ s} → A)
        continuous_subtype_val (fun x ↦ x.2.2) with
      x
    rw [cfcHomSuperset_apply, Set.restrict_apply, cfc_apply _ _ x.2.1 (hf.mono x.2.2)]
    congr!

open UniformOnFun in
/-- Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where `f` is
continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies the predicate `p a` for the continuous
functional calculus.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
theorem continuousOn_cfc_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{s}] 𝕜) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | p a ∧ spectrum 𝕜 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfc A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
private lemma uniformContinuous_ofFun_toFun_compact {𝕜 : Type*} [UniformSpace 𝕜] {s k : Set 𝕜}
    (hk : IsCompact k) (hks : k ⊆ s) :
    Continuous (fun f : 𝕜 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] 𝕜 ↦
      ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} f)) := by
  apply UniformContinuous.continuous
  refine uniformContinuous_ofFun_toFun 𝕜 _ _ fun _ _ ↦ ?_
  exact ⟨{k}, by simp_all⟩

open UniformOnFun in
theorem continuousOn_cfc_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] 𝕜) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s} ×ˢ
        {a | p a ∧ s ∈ 𝓝ˢ (spectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (spectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfc_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_compact hk hks |>.prodMap continuous_id).continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to `a₀ : A` along a
filter `l` (such that eventually `a x` satisfies the predicate `p` associated to `𝕜` and has
spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to `cfc f a₀`. -/
protected theorem Filter.Tendsto.cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in l, p (a x))
    (ha₀ : spectrum 𝕜 a₀ ⊆ s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc f (a x)) l (𝓝 (cfc f a₀)) := by
  apply continuousOn_cfc A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`, and
eventually `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum contained in `s`,
then `fun x ↦ cfc f (a x)` is continuous at `x₀`. -/
protected theorem ContinuousAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀` within
a set `t : Set X`, and eventually `a x` satisfies the predicate `p` associated to `𝕜` and has
spectrum contained in `s`, then `fun x ↦ cfc f (a x)` is continuous at `x₀` within `t`. -/
protected theorem ContinuousWithinAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x ↦ cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the predicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f (a x)` is
continuous on `t`. -/
protected theorem ContinuousOn.cfc [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, p (a x))
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfc (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and has spectrum contained in `s` for all
`x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`. -/
theorem ContinuousOn.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, spectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x ∈ t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  refine ContinuousOn.cfc _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfc` since it requires `f` to be continuous on a *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not required to be compact,
nor does it require an indexed family of compact sets. This is proven using `ContinuousOn.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets. -/
theorem ContinuousOn.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, spectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), spectrum 𝕜 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      spectrum.isCompact (𝕜 := 𝕜) (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_spectrum 𝕜 A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x`, then
`fun x ↦ cfc f (a x)` is continuous. -/
protected theorem Continuous.cfc [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfc` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous on the spectrum of `a`. -/
theorem Continuous.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `a : X → A` is continuous and `a x` satisfies the
predicate `p` associated to `𝕜` and `s` is a common neighborhood of the spectra of `a x` for
all `x`, then `fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc` since it requires `f` to be continuous on a *neighborhood* of
the spectra, but in practice it is often easier to apply because `s` is not required to be compact,
nor does it require an indexed family of compact sets. This is proven using `Continuous.cfc` and
`upperHemicontinuous_spectrum` to produce the necessary family of compact sets. -/
theorem Continuous.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, spectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/-- A version of `continuousOn_cfc` over `ℝ≥0` instead of `RCLike 𝕜`. -/
theorem continuousOn_cfc_nnreal {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a : A | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s} := by
  have : {a : A | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s}.EqOn (cfc f) (cfc (fun x : ℝ ↦ f x.toNNReal)) :=
    fun a ha ↦ cfc_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
  refine continuousOn_cfc A (hs.image NNReal.continuous_coe) _ hf |>.mono fun a ha ↦ ?_
  simp only [Set.mem_setOf_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  rw [← SpectrumRestricts] at ha
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/-- Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A` where `f` is
continuous on `s` and `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfc` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
theorem continuousOn_cfc_nnreal_setProd {s : Set ℝ≥0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{s}] ℝ≥0) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | 0 ≤ a ∧ spectrum ℝ≥0 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfc_nnreal A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
theorem continuousOn_cfc_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set ℝ≥0} :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] ℝ≥0) × A ↦ cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s} ×ˢ
        {a | 0 ≤ a ∧ s ∈ 𝓝ˢ (spectrum ℝ≥0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ≥0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (spectrum ℝ≥0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfc_nnreal_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_compact hk hks |>.prodMap continuous_id).continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` tends to `a₀ : A` along a
filter `l` (such that eventually `0 ≤ a x` and has spectrum contained in `s`, as does `a₀`), then
`fun x ↦ cfc f (a x)` tends to `cfc f a₀`. -/
theorem Filter.Tendsto.cfc_nnreal {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in l, 0 ≤ a x)
    (ha₀ : spectrum ℝ≥0 a₀ ⊆ s) (ha₀' : 0 ≤ a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc f (a x)) l (𝓝 (cfc f a₀)) := by
  apply continuousOn_cfc_nnreal A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`, and
eventually `0 ≤ a x` and has spectrum contained in `s`, then `fun x ↦ cfc f (a x)` is continuous
at `x₀`. -/
theorem ContinuousAt.cfc_nnreal [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous at `x₀`
within a set `t : Set X`, and eventually `0 ≤ a x` and has spectrum contained in `s`, then
`fun x ↦ cfc f (a x)` is continuous at `x₀` within `t`. -/
theorem ContinuousWithinAt.cfc_nnreal [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, spectrum ℝ≥0 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, 0 ≤ a x) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x ↦ cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x`, for each `x ∈ t`, then `fun x ↦ cfc f (a x)` is
continuous on `t`. -/
theorem ContinuousOn.cfc_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, spectrum ℝ≥0 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfc_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `a : X → A` is continuous on
`t : Set X`, and `0 ≤ a x` and has spectrum contained in `s` for all `x ∈ t`, then
`fun x ↦ cfc f (a x)` is continuous on `t`. -/
theorem ContinuousOn.cfc_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, spectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  refine ContinuousOn.cfc_nnreal _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous on `t : Set X`,
and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighborhood of the
spectra of `a x` for all `x ∈ t`, then `fun x ↦ cfc f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfc_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the spectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce the necessary family
of compact sets. -/
theorem ContinuousOn.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, spectrum ℝ≥0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x ↦ cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), spectrum ℝ≥0 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      spectrum.isCompact_nnreal (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_spectrum_nnreal A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc_nnreal (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuous on each `s x`,
then `fun x ↦ cfc f (a x)` is continuous. -/
theorem Continuous.cfc_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, spectrum ℝ≥0 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfc` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `a` varies over
nonnegative elements whose spectrum is contained in `s`, and the function `f` is
continuous on `s`. -/
theorem Continuous.cfc_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, spectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `a : X → A` is continuous and `a x` is nonnegative
for all `x` and `s` is a common neighborhood of the spectra of `a x` for all `x`, then
`fun x ↦ cfc f (a x)` is continuous.

This is weaker than `Continuous.cfc_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the spectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfc_nnreal` and `upperHemicontinuous_spectrum_nnreal` to produce the necessary family
of compact sets. -/
theorem Continuous.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, spectrum ℝ≥0 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end Unital

section NonUnital

section Left

section Generic

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum and map zero to itself, then
`fun x ↦ cfcₙ (F x) a` tends to `cfcₙ f a`. -/
theorem tendsto_cfcₙ_fun {l : Filter X} {F : X → R → R} {f : R → R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (quasispectrum R a))
    (hF : ∀ᶠ x in l, ContinuousOn (F x) (quasispectrum R a)) (hF0 : ∀ᶠ x in l, F x 0 = 0) :
    Tendsto (fun x ↦ cfcₙ (F x) a) l (𝓝 (cfcₙ f a)) := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  have hf0 : f 0 = 0 := Eq.symm <|
    tendsto_nhds_unique (tendsto_const_nhds.congr' <| .symm hF0) <|
    h_tendsto.tendsto_at (quasispectrum.zero_mem R a)
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (quasispectrum R a) ∧ F x 0 = 0}
    have hs : s ∈ l := hF.and hF0
    rw [← tendsto_comap'_iff (i := ((↑) : s → X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply, cfcₙ_apply (hf := x.2.1) (hf0 := x.2.2)]
    rw [cfcₙ_apply ..]
    apply cfcₙHom_continuous _ |>.tendsto _ |>.comp
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.isInducing.tendsto_nhds_iff]
    change Tendsto (fun x : s ↦ (⟨_, x.2.1.restrict⟩ : C(quasispectrum R a, R))) _
      (𝓝 ⟨_, hf.restrict⟩)
    rw [hf.tendsto_restrict_iff_tendstoUniformlyOn (fun x ↦ x.2.1)]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfcₙ_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a` and maps zero to itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀`. -/
theorem continuousAt_cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : ∀ᶠ x in 𝓝 x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ᶠ x in 𝓝 x₀, f x 0 = 0) :
    ContinuousAt (fun x ↦ cfcₙ (f x) a) x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝[s] x₀`) on the spectrum of `a`,
and eventually each `f x` is continuous on the spectrum of `a` and maps zero to itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀` within `s`. -/
theorem continuousWithinAt_cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (quasispectrum R a))
    (hf : ∀ᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ᶠ x in 𝓝[s] x₀, f x 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ (f x) a) s x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

open UniformOnFun in
/-- If `f : X → R → R` is continuous on `s : Set X` in the topology on
`X → R →ᵤ[{spectrum R a}] → R`, and for each `x ∈ s`, `f x` is continuous on the spectrum and
maps zero to itself, then `x ↦ cfcₙ (f x) a` is continuous on `s` also. -/
theorem ContinuousOn.cfcₙ_fun [TopologicalSpace X] {f : X → R → R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x ↦ ofFun {quasispectrum R a} (f x)) s)
    (hf : ∀ x ∈ s, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : ∀ x ∈ s, f x 0 = 0) :
    ContinuousOn (fun x ↦ cfcₙ (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx ↦ continuousWithinAt_cfcₙ_fun (h_cont x hx) ?_ ?_
  all_goals filter_upwards [self_mem_nhdsWithin] with x hx
  exacts [hf x hx, hf0 x hx]

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum and maps zero to itself, then
`x ↦ cfcₙ (f x) a` is continuous. -/
theorem Continuous.cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {quasispectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    Continuous fun x ↦ cfcₙ (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfcₙ_fun (fun x _ ↦ hf x) (fun x _ ↦ hf0 x)

end Generic

section Isometric

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [MetricSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalIsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped NonUnitalContinuousFunctionalCalculus in
/-- The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{quasispectrum R a}] R`) on those functions which are continuous on
the quasispectrum and map zero to itself. -/
lemma lipschitzOnWith_cfcₙ_fun (a : A) :
    LipschitzOnWith 1 (fun f ↦ cfcₙ (toFun {quasispectrum R a} f) a)
      {f | ContinuousOn (toFun {quasispectrum R a} f) (quasispectrum R a) ∧ f 0 = 0} := by
  by_cases ha : p a
  · rintro f ⟨hf, hf0⟩ g ⟨hg, hg0⟩
    simp only
    rw [cfcₙ_apply .., cfcₙ_apply .., isometry_cfcₙHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [← ContinuousMapZero.isometry_toContinuousMap.edist_eq,
      edist_continuousRestrict_of_singleton hf hg]
  · simpa [cfcₙ_apply_of_not_predicate a ha] using LipschitzWith.const' 0 |>.lipschitzOnWith

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/-- The function `f ↦ cfcₙ f a` is Lipschitz with constant 1 with respect to
supremum metric (on `R →ᵤ[{s}] R`) on those functions which are continuous on a set `s` containing
the quasispectrum and map zero to itself. -/
lemma lipschitzOnWith_cfcₙ_fun_of_subset (a : A) {s : Set R} (hs : quasispectrum R a ⊆ s) :
    LipschitzOnWith 1 (fun f ↦ cfcₙ (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0} := by
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {quasispectrum R a}) (𝔗 := {s}) (β := R)
    (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0})
  simpa using! lipschitzOnWith_cfcₙ_fun R a |>.comp h₃ (fun f ↦ .imp_left fun hf ↦ hf.mono hs)

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
/-- `cfcₙHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
theorem continuous_cfcₙHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) [hs0 : Fact (0 ∈ s)]
    (f : C(s, 𝕜)₀) {a : X → A} (ha_cont : Continuous a)
    (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙHomSuperset (ha' x) (ha x) f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa [map_zero] using! continuous_const
  | id => simpa only [cfcₙHomSuperset_id]
  | star_id => simp only [map_star, cfcₙHomSuperset_id]; fun_prop
  | add f g hf hg => simpa only [map_add] using! hf.add hg
  | mul f g hf hg => simpa only [map_mul] using! hf.mul hg
  | smul r f hf => simpa only [map_smul] using! hf.const_smul r
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcₙHomSuperset_apply]
    rw [isometry_cfcₙHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcₙHom (ha' x)))]
    rw [ContinuousMapZero.norm_def, ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/-- For `f : 𝕜 → 𝕜` continuous on a set `s` for which `f 0 = 0`, `cfcₙ f` is continuous on the
set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-quasispectrum is
contained in `s`. -/
theorem continuousOn_cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A → A) {a | p a ∧ quasispectrum 𝕜 a ⊆ s} := by
  by_cases hs0 : 0 ∈ s
  · rw [continuousOn_iff_continuous_restrict]
    convert!
      continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.restrict⟩, hf0⟩ (X :=
        {a : A | p a ∧ quasispectrum 𝕜 a ⊆ s}) continuous_subtype_val (fun x ↦ x.2.2) with
      x
    rw [cfcₙHomSuperset_apply, Set.restrict_apply, cfcₙ_apply _ _ (hf.mono x.2.2) hf0 x.2.1]
    congr!
  · convert! continuousOn_empty _
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun a ha ↦ hs0 <| ha.2 <| quasispectrum.zero_mem 𝕜 a

open UniformOnFun in
/-- Let `s : Set 𝕜` be a compact set and consider pairs `(f, a) : (𝕜 → 𝕜) × A` where `f` is
continuous on `s`, maps zero itself, and `quasispectrum 𝕜 a ⊆ s` and `a` satisfies the predicate
`p a` for the continuous functional calculus.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
theorem continuousOn_cfcₙ_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{s}] 𝕜) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | p a ∧ quasispectrum 𝕜 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfcₙ A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
theorem continuousOn_cfcₙ_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] 𝕜) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s ∧ f 0 = 0} ×ˢ
        {a | p a ∧ s ∈ 𝓝ˢ (quasispectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (quasispectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfcₙ_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_compact hk hks |>.prodMap continuous_id).continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` tends to
`a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
`𝕜` and has quasispectrum contained in `s`, as does `a₀`), then `fun x ↦ cfcₙ f (a x)` tends to
`cfcₙ f a₀`. -/
protected theorem Filter.Tendsto.cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in l, p (a x))
    (ha₀ : quasispectrum 𝕜 a₀ ⊆ s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
  apply continuousOn_cfcₙ A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
at `x₀`, and eventually `a x` satisfies the predicate `p` associated to `𝕜` and has quasispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀`. -/
protected theorem ContinuousAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
at `x₀` within a set `t : Set X`, and eventually `a x` satisfies the predicate `p` associated to `𝕜`
and has quasispectrum contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀`
within `t`. -/
protected theorem ContinuousWithinAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `a x` satisfies the predicate `p` for
all `x ∈ t`. Suppose further that `s : X → Set 𝕜` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : 𝕜 → 𝕜` is continuous on `s x` for each `x ∈ t`, and `f 0 = 0` then `fun x ↦ cfcₙ f (a x)`
is continuous on `t`. -/
protected theorem ContinuousOn.cfcₙ [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, p (a x))
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfcₙ (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is continuous
on `t : Set X`, and `a x` satisfies the predicate `p` associated to `𝕜` and has quasispectrum
contained in `s` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`. -/
theorem ContinuousOn.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x ∈ t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous on `t : Set X`,
and `a x` satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfcₙ` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the necessary family of
compact sets. -/
theorem ContinuousOn.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, quasispectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), quasispectrum 𝕜 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      quasispectrum.isCompact (𝕜 := 𝕜) (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_quasispectrum 𝕜 A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is continuous and `a x` satisfies the predicate `p` for all `x`.
Suppose further that `s : X → Set 𝕜` is a family of compact sets `s x₀` contains the spectrum of
`a x` for all sufficiently close `x`. If `f : 𝕜 → 𝕜` is continuous on each `s x` and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous. -/
protected theorem Continuous.cfcₙ [TopologicalSpace X] {s : X → Set 𝕜} (f : 𝕜 → 𝕜) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfcₙ` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose quasispectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous `s` and `f 0 = 0`. -/
theorem Continuous.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : 𝕜 → 𝕜` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous and `a x`
satisfies the predicate `p` associated to `𝕜` and `s` is a common neighborhood of the quasispectra
of `a x` for all `x`, then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ` since it requires `f` to be continuous on a *neighborhood* of
the quasispectra, but in practice it is often easier to apply because `s` is not required to be
compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfcₙ` and `upperHemicontinuous_quasispectrum` to produce the necessary family of
compact sets. -/
theorem Continuous.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 → 𝕜) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, quasispectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : ∀ x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/-- A version of `continuousOn_cfcₙ` over `ℝ≥0` instead of `RCLike 𝕜`. -/
theorem continuousOn_cfcₙ_nnreal {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A → A) {a : A | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s} := by
  have : {a : A | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s}.EqOn (cfcₙ f)
      (cfcₙ (fun x : ℝ ↦ f x.toNNReal)) :=
    fun a ha ↦ cfcₙ_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x ↦ f x.toNNReal : ℝ → ℝ) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
  refine continuousOn_cfcₙ A (hs.image NNReal.continuous_coe) _ hf |>.mono fun a ha ↦ ?_
  simp only [Set.mem_setOf_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/-- Let `s : Set ℝ≥0` be a compact set and consider pairs `(f, a) : (ℝ≥0 → ℝ≥0) × A` where `f` is
continuous on `s`, maps zero to itself, `spectrum ℝ≥0 a ⊆ s` and `0 ≤ a`.

Then `cfcₙ` is jointly continuous in both variables (i.e., continuous in its uncurried form) on this
set of pairs when the function space is equipped with the topology of uniform convergence on `s`. -/
theorem continuousOn_cfcₙ_nnreal_setProd {s : Set ℝ≥0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{s}] ℝ≥0) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | 0 ≤ a ∧ quasispectrum ℝ≥0 a ⊆ s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf ↦ continuousOn_cfcₙ_nnreal A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ ↦ lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
theorem continuousOn_cfcₙ_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set ℝ≥0} :
    ContinuousOn (fun fa : (ℝ≥0 →ᵤ[{t | IsCompact t ∧ t ⊆ s}] ℝ≥0) × A ↦ cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t ⊆ s} f) s ∧ f 0 = 0} ×ˢ
        {a | 0 ≤ a ∧ s ∈ 𝓝ˢ (quasispectrum ℝ≥0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ ↦ ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := ℝ≥0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k ∈ 𝓝ˢ (quasispectrum ℝ≥0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t ⊆ s} fa.1))) => rfl
  refine continuousOn_cfcₙ_nnreal_setProd hk |>.comp'
    (uniformContinuous_ofFun_toFun_compact hk hks |>.prodMap continuous_id).continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` tends to
`a₀ : A` along a filter `l` (such that eventually `0 ≤ a x` and has quasispectrum contained in `s`,
as does `a₀`), then `fun x ↦ cfcₙ f (a x)` tends to `cfcₙ f a₀`. -/
theorem Filter.Tendsto.cfcₙ_nnreal {s : Set ℝ≥0} (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    {a : X → A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : ∀ᶠ x in l, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in l, 0 ≤ a x)
    (ha₀ : quasispectrum ℝ≥0 a₀ ⊆ s) (ha₀' : 0 ≤ a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
  apply continuousOn_cfcₙ_nnreal A hs f |>.continuousWithinAt ⟨ha₀', ha₀⟩ |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous at `x₀`, and eventually `0 ≤ a x` and has quasispectrum contained in `s`, then
`fun x ↦ cfcₙ f (a x)` is continuous at `x₀`. -/
theorem ContinuousAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set ℝ≥0}
    (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : ∀ᶠ x in 𝓝 x₀, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ᶠ x in 𝓝 x₀, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous at `x₀` within a set `t : Set X`, and eventually `0 ≤ a x` and has quasispectrum
contained in `s`, then `fun x ↦ cfcₙ f (a x)` is continuous at `x₀` within `t`. -/
theorem ContinuousWithinAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set ℝ≥0}
    (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0) {a : X → A} {x₀ : X} {t : Set X} (hx₀ : x₀ ∈ t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : ∀ᶠ x in 𝓝[t] x₀, quasispectrum ℝ≥0 (a x) ⊆ s)
    (ha' : ∀ᶠ x in 𝓝[t] x₀, 0 ≤ a x) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x ↦ cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/-- Suppose `a : X → Set A` is continuous on `t : Set X` and `0 ≤ a x` for all `x ∈ t`.
Suppose further that `s : X → Set ℝ≥0` is a family of sets with `s x` compact when
`x ∈ t` such that `s x₀` contains the spectrum of `a x` for all sufficiently close `x ∈ t`.
If `f : ℝ≥0 → ℝ≥0` is continuous on `s x` for each `x ∈ t` and `f 0 = 0`, then
`fun x ↦ cfc f (a x)` is continuous on `t`. -/
theorem ContinuousOn.cfcₙ_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    {t : Set X} (hs : ∀ x ∈ t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : ∀ x₀ ∈ t, ∀ᶠ x in 𝓝[t] x₀, quasispectrum ℝ≥0 (a x) ⊆ s x₀) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ∀ x ∈ t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx ↦ (ha_cont x hx).cfcₙ_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on a compact set `s` and `f 0 = 0` and `a : X → A` is
continuous on `t : Set X`, and `0 ≤ a x` and has quasispectrum contained in `s` for all `x ∈ t`,
then `fun x ↦ cfcₙ f (a x)` is continuous on `t`. -/
theorem ContinuousOn.cfcₙ_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : ∀ x ∈ t, quasispectrum ℝ≥0 (a x) ⊆ s) (ha' : ∀ x ∈ t, 0 ≤ a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ_nnreal _ (fun _ _ ↦ hs) ha_cont (fun _ _ ↦ ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous on
`t : Set X`, and `a x` is nonnegative for all `x ∈ t` and `s` is a common neighborhood of the
quasispectra of `a x` for all `x ∈ t`, then `fun x ↦ cfcₙ f (a x)` is continuous on `t`.

This is weaker than `ContinuousOn.cfcₙ_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`ContinuousOn.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to produce the necessary
family of compact sets. -/
theorem ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} {t : Set X} (hs : s ∈ 𝓝ˢ (⋃ x ∈ t, quasispectrum ℝ≥0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : ∀ x ∈ t, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x ↦ cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : ∃ S, IsCompact S ∧ (∀ᶠ (x' : A) in 𝓝 (a x), quasispectrum ℝ≥0 x' ⊆ S) ∧ S ⊆ s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
      quasispectrum.isCompact_nnreal (a x) |>.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2)
    refine ⟨S, hS₂, ?_, hS₃⟩
    exact upperHemicontinuous_quasispectrum_nnreal A |>.upperHemicontinuousAt (a x) _ hS₁ |>.mono
      fun _ ↦ subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ_nnreal (s := fun x : X ↦ if hx : x ∈ t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
  · exact fun x₀ hx₀ ↦ ha_cont.continuousWithinAt hx₀ |>.eventually <| hS₂ ⟨x₀, hx₀⟩
  · exact fun x hx ↦ hf.mono <| hS₃ ⟨x, hx⟩

/-- Suppose `a : X → Set A` is a continuous family of nonnegative elements.
Suppose further that `s : X → Set ℝ≥0` is a family of compact sets such that `s x₀` contains the
spectrum of `a x` for all sufficiently close `x`. If `f : ℝ≥0 → ℝ≥0` is continuous on each `s x`
and `f 0 = 0`, then `fun x ↦ cfc f (a x)` is continuous. -/
theorem Continuous.cfcₙ_nnreal [TopologicalSpace X] {s : X → Set ℝ≥0} (f : ℝ≥0 → ℝ≥0) {a : X → A}
    (ha_cont : Continuous a) (hs : ∀ x, IsCompact (s x))
    (ha : ∀ x₀, ∀ᶠ x in 𝓝 x₀, quasispectrum ℝ≥0 (a x) ⊆ s x₀)
    (hf : ∀ x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal f (fun x _ ↦ hs x) (fun x _ ↦ by simpa using ha x) (fun x _ ↦ ha' x)

/-- `cfcₙ` is continuous in the variable `a : A` when `s : Set ℝ≥0` is compact and `a` varies over
nonnegative elements whose quasispectrum is contained in `s`, and the function `f` is
continuous on `s` and `f 0 = 0`. -/
theorem Continuous.cfcₙ_nnreal' [TopologicalSpace X] {s : Set ℝ≥0} (hs : IsCompact s)
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (ha_cont : Continuous a) (ha : ∀ x, quasispectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, 0 ≤ a x := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal' hs f (fun x _ ↦ ha x) (fun x _ ↦ ha' x)

/-- If `f : ℝ≥0 → ℝ≥0` is continuous on `s` and `f 0 = 0` and `a : X → A` is continuous and `a x` is
nonnegative for all `x` and `s` is a common neighborhood of the quasispectra of `a x` for all `x`,
then `fun x ↦ cfcₙ f (a x)` is continuous.

This is weaker than `Continuous.cfcₙ_nnreal` since it requires `f` to be continuous on a
*neighborhood* of the quasispectra, but in practice it is often easier to apply because `s` is not
required to be compact, nor does it require an indexed family of compact sets. This is proven using
`Continuous.cfcₙ_nnreal` and `upperHemicontinuous_quasispectrum_nnreal` to produce the necessary
family of compact sets. -/
theorem Continuous.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set ℝ≥0}
    (f : ℝ≥0 → ℝ≥0) {a : X → A} (hs : s ∈ 𝓝ˢ (⋃ x, quasispectrum ℝ≥0 (a x)))
    (ha_cont : Continuous a) (ha' : ∀ x, 0 ≤ a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end NonUnital
