/-
Copyright (c) 2025 Ruiz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The fundamental group of the circle

We prove that the fundamental group of the circle `AddCircle 1` (equivalently `ℝ / ℤ`)
is isomorphic to `ℤ`. The proof uses the covering space `ℝ → AddCircle 1` and the
homotopy lifting property.

## Main definitions

* `AddCircle.nLoop n` : the loop in `AddCircle 1` that winds `n` times around the circle,
  defined as `t ↦ n • t`.
* `AddCircle.zeroLoop` : the constant loop at `0` in `AddCircle 1`.

## Main results

* `AddCircle.surj_nLoop` : every loop at `0` in `AddCircle 1` is homotopic to some `nLoop n`
  (surjectivity of the winding number map).
* `AddCircle.inj_nLoop` : if `nLoop n` is homotopic to `zeroLoop`, then `n = 0`
  (injectivity of the winding number map).

## References

* [A. Hatcher, *Algebraic Topology*][hatcher02], Theorem 1.7 and Proposition 1.31.
-/

public section

open unitInterval

namespace AddCircle

/-- The unit circle, `ℝ / ℤ`. -/
abbrev uc := AddCircle (1 : ℝ)

/-- The covering map `ℝ → ℝ/ℤ`. -/
abbrev covMap : ℝ → uc := ((↑) : ℝ → uc)

theorem isCoveringMap_covMap : IsCoveringMap covMap :=
  AddCircle.isCoveringMap_coe 1

/-- The constant loop at `0 : uc`. -/
def zeroLoop : Path (0 : uc) 0 where
  toFun := 0
  source' := by simp
  target' := by simp
  continuous_toFun := continuous_zero

/-- The loop `ωₙ` in `uc` that winds `n` times, defined as `t ↦ n • t`.
  This is the representative loop in each homotopy class. -/
def nLoop (n : ℤ) : Path (0 : uc) 0 where
  toFun t := n • t
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one]
    rw [AddCircle.coe_period]
    exact zsmul_zero n
  continuous_toFun := (continuous_zsmul n).comp
    (continuous_quotient_mk'.comp continuous_subtype_val)

/-- Preimages of `0 : uc` under the covering map are exactly the integers. -/
lemma covMap_eq_zero_iff (k : ℝ) : covMap k = 0 → ∃ (n : ℤ), k = (n : ℝ) := by
  intro h1
  rw [covMap, AddCircle.coe_eq_zero_iff] at h1
  rcases h1 with ⟨n, hn⟩
  exact ⟨n, by simp at hn; linarith⟩

/-- The linear multiplication function `t ↦ n * t` on `I → ℝ`. -/
abbrev linearLift (n : ℤ) := fun (t : I) ↦ (n : ℝ) * t

theorem continuous_linearLift (n : ℤ) : Continuous (linearLift n) := by
  have heq : linearLift n = ((fun t : ℝ ↦ n • t) ∘ Subtype.val) := by
    ext x; simp [linearLift]
  rw [heq]
  continuity

/-- The lift of `nLoop n` to `ℝ` starting at `0` is the linear path `t ↦ n * t`. -/
private lemma liftPath_nLoop (n : ℤ) :
    (isCoveringMap_covMap.liftPath (nLoop n).toContinuousMap 0 (by simp [covMap]) : C(I, ℝ))
    = ⟨linearLift n, continuous_linearLift n⟩ := by
  symm
  rw [IsCoveringMap.eq_liftPath_iff']
  refine ⟨funext fun ⟨t, ht⟩ => ?_, by simp [linearLift]⟩
  simp only [Function.comp_apply, ContinuousMap.coe_mk, linearLift, covMap, nLoop]
  rw [show (↑n : ℝ) * t = n • t from by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul],
    AddCircle.coe_zsmul]

/-- The lift of `zeroLoop` to `ℝ` starting at `0` is the constant path at `0`. -/
private lemma liftPath_zeroLoop :
    (isCoveringMap_covMap.liftPath zeroLoop.toContinuousMap 0 (by simp [covMap]) : C(I, ℝ))
    = .const I 0 := by
  symm
  rw [IsCoveringMap.eq_liftPath_iff']
  constructor
  · ext ⟨t, ht⟩
    simp [Function.comp_apply, covMap, zeroLoop]
  · simp

/-- **Surjectivity of the winding number**: every loop at `0` in `uc` is homotopic to
  `nLoop n` for some integer `n`. -/
theorem surj_nLoop (ω : Path (0 : uc) 0) : ∃ (n : ℤ), (nLoop n).Homotopic ω := by
  -- Lift ω to ℝ starting at 0
  have ω_src : ω.toContinuousMap 0 = covMap 0 := by simp
  let ω_lift := isCoveringMap_covMap.liftPath ω.toContinuousMap 0 ω_src
  -- The endpoint of the lift projects to 0, so it must be an integer
  have ω_lift_end : covMap (ω_lift 1) = 0 := by
    have := congr_fun (isCoveringMap_covMap.liftPath_lifts ω.toContinuousMap 0 ω_src) 1
    simpa [Function.comp_apply] using this
  obtain ⟨n, hn⟩ := covMap_eq_zero_iff (ω_lift 1) ω_lift_end
  use n
  -- Build paths in ℝ from 0 to n: the linear lift and ω's lift
  have ω_lift_zero : ω_lift 0 = 0 :=
    isCoveringMap_covMap.liftPath_zero ω.toContinuousMap 0 ω_src
  let path_ω_lift : Path (0 : ℝ) n := ⟨ω_lift, ω_lift_zero, hn⟩
  let path_linear : Path (0 : ℝ) n :=
    ⟨⟨linearLift n, continuous_linearLift n⟩, by simp [linearLift], by simp [linearLift]⟩
  -- ℝ is simply connected, so the two lifts are homotopic rel endpoints
  obtain ⟨H_R⟩ := SimplyConnectedSpace.paths_homotopic path_linear path_ω_lift
  -- Project the homotopy down to uc via covMap
  have hx : ((n : ℝ) : uc) = 0 := by rw [← hn]; exact ω_lift_end
  have covMap_linear (s : I) : covMap (path_linear s) = (nLoop n) s := by
    dsimp only [path_linear, linearLift, nLoop, Path.coe_mk_mk]
    rw [show (↑n : ℝ) * ↑s = n • (↑s : ℝ) from by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]]; rfl
  have covMap_omega (s : I) : covMap (path_ω_lift s) = ω s := by
    have := congr_fun (isCoveringMap_covMap.liftPath_lifts ω.toContinuousMap 0 ω_src) s
    simpa [Function.comp_apply] using this
  exact ⟨{
    toFun := fun (t, s) => covMap (H_R (t, s))
    continuous_toFun := isCoveringMap_covMap.continuous.comp H_R.continuous_toFun
    map_zero_left := fun s => by simp [H_R.apply_zero, covMap_linear]
    map_one_left := fun s => by simp [H_R.apply_one, covMap_omega]
    prop' := fun t s hs => by
      rcases hs with rfl | (rfl : s = 1)
      · simp
      · simp }⟩

/-- **Injectivity of the winding number**: if `nLoop n` is homotopic to `zeroLoop`,
  then `n = 0`. -/
theorem inj_nLoop (n : ℤ) : (nLoop n).Homotopic zeroLoop → n = 0 := by
  intro ⟨H⟩
  -- The key tool: homotopic paths lift to paths with the same endpoint
  have key := isCoveringMap_covMap.liftPath_apply_one_eq_of_homotopicRel
    ⟨H⟩ (0 : ℝ) (by simp [covMap]) (by simp [covMap])
  -- Compute the lift endpoints using our lemmas
  rw [liftPath_nLoop, liftPath_zeroLoop] at key
  -- Now key says: linearLift n 1 = 0
  simp only [ContinuousMap.coe_mk, linearLift, ContinuousMap.const_apply,
    Set.Icc.coe_one, mul_one] at key
  exact_mod_cast key

/-- Integer values map to zero under the covering map. -/
private lemma covMap_intCast (m : ℤ) : covMap (m : ℝ) = 0 := by
  change ((m : ℝ) : AddCircle (1 : ℝ)) = 0
  rw [show (m : ℝ) = m • (1 : ℝ) from by simp]
  rw [AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]

/-- The lift of `nLoop n` starting at integer `m` is the affine path `t ↦ m + n * t`. -/
private lemma liftPath_nLoop_at (m n : ℤ) :
    (isCoveringMap_covMap.liftPath (nLoop n).toContinuousMap (m : ℝ)
      (by simp only [Path.coe_toContinuousMap, Path.source]
          exact (covMap_intCast m).symm) : C(I, ℝ))
    = ⟨fun t => (m : ℝ) + (n : ℝ) * t,
        continuous_const.add ((continuous_const).mul continuous_subtype_val)⟩ := by
  symm
  rw [IsCoveringMap.eq_liftPath_iff']
  refine ⟨funext fun ⟨t, ht⟩ => ?_, by norm_num⟩
  simp only [Function.comp_apply, ContinuousMap.coe_mk, covMap, nLoop]
  rw [show (↑m : ℝ) + (↑n : ℝ) * t = (↑n : ℝ) * t + (↑m : ℝ) from by ring]
  rw [show (↑n : ℝ) * t = n • t from by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]]
  rw [← AddCircle.coe_zsmul]
  exact QuotientAddGroup.eq.mpr (by
    have : -(n • t + (↑m : ℝ)) + (n • t) = -(↑m : ℝ) := by ring
    rw [this]; exact ⟨-m, by simp⟩)

/-- Winding numbers are additive: `(nLoop m).trans (nLoop n)` is homotopic to `nLoop (m + n)`. -/
theorem nLoop_add (m n : ℤ) :
    ((nLoop m).trans (nLoop n)).Homotopic (nLoop (m + n)) := by
  -- Strategy: build explicit paths in ℝ from 0 to m+n that project to each side,
  -- use simple connectedness of ℝ, then project the homotopy down.
  -- Path in ℝ projecting to (nLoop m).trans (nLoop n): concat of 0→m and m→m+n
  let p1 : Path (0 : ℝ) (↑m : ℝ) :=
    ⟨⟨linearLift m, continuous_linearLift m⟩,
     by simp [linearLift], by simp [linearLift]⟩
  let p2 : Path (↑m : ℝ) ((↑m : ℝ) + ↑n) :=
    ⟨⟨fun t => (↑m : ℝ) + (↑n : ℝ) * t,
      continuous_const.add (continuous_const.mul continuous_subtype_val)⟩,
     by norm_num, by simp⟩
  let path_concat := p1.trans p2
  -- Path in ℝ projecting to nLoop (m+n): linear 0→m+n
  let path_mn : Path (0 : ℝ) ((↑m : ℝ) + ↑n) :=
    ⟨⟨linearLift (m + n), continuous_linearLift (m + n)⟩,
     by simp [linearLift], by simp [linearLift]⟩
  -- path_mn projects to nLoop (m+n)
  have covMap_mn (s : I) : covMap (path_mn s) = (nLoop (m + n)) s := by
    dsimp only [path_mn, linearLift, nLoop, Path.coe_mk_mk]
    rw [show (↑(m + n) : ℝ) * ↑s = (m + n) • (↑s : ℝ) from
      by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]]; rfl
  -- Each piece projects correctly (abstract over I to avoid Set.projIcc coercion issues)
  have covMap_p1 : ∀ u : I, covMap (p1 u) = (nLoop m) u := fun u => by
    dsimp only [p1, Path.coe_mk_mk, linearLift, covMap, nLoop]
    rw [show (↑m : ℝ) * ↑u = m • (↑u : ℝ) from by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]]
    rfl
  have covMap_p2 : ∀ u : I, covMap (p2 u) = (nLoop n) u := fun u => by
    dsimp only [p2, Path.coe_mk_mk, covMap, nLoop]
    rw [show (↑m : ℝ) + (↑n : ℝ) * ↑u = (↑n : ℝ) * ↑u + (↑m : ℝ) from by ring]
    rw [show (↑n : ℝ) * ↑u = n • (↑u : ℝ) from by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]]
    rw [← AddCircle.coe_zsmul]
    exact QuotientAddGroup.eq.mpr (by
      have : -(n • (↑u : ℝ) + (↑m : ℝ)) + (n • ↑u) = -(↑m : ℝ) := by ring
      rw [this]; exact ⟨-m, by simp⟩)
  -- path_concat projects to (nLoop m).trans (nLoop n)
  have covMap_concat (s : I) :
      covMap (path_concat s) = ((nLoop m).trans (nLoop n)) s := by
    simp only [path_concat, Path.trans_apply]
    split_ifs <;> [exact covMap_p1 _; exact covMap_p2 _]
  -- ℝ simply connected → both lifts homotopic
  obtain ⟨H_R⟩ := SimplyConnectedSpace.paths_homotopic path_concat path_mn
  -- Project the homotopy down to uc via covMap
  have hx : covMap ((↑m : ℝ) + ↑n) = 0 := by
    rw [show (↑m : ℝ) + ↑n = ↑(m + n) from by push_cast; ring]
    exact covMap_intCast (m + n)
  exact ⟨{
    toFun := fun (t, s) => covMap (H_R (t, s))
    continuous_toFun := isCoveringMap_covMap.continuous.comp H_R.continuous_toFun
    map_zero_left := fun s => by simp [H_R.apply_zero, covMap_concat]
    map_one_left := fun s => by simp [H_R.apply_one, covMap_mn]
    prop' := fun t s hs => by
      rcases hs with rfl | (rfl : s = 1)
      · simp
      · simp [hx] }⟩


/-- `nLoop 0` is the constant loop at `0`. -/
private lemma nLoop_zero : nLoop 0 = Path.refl (0 : uc) := by
  ext t; simp [nLoop]

open CategoryTheory in
/-- The winding number homomorphism sending `n : ℤ` to the homotopy class `⟦nLoop n⟧`. -/
noncomputable def windingHom : Multiplicative ℤ →* FundamentalGroup uc 0 where
  toFun n := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (nLoop (Multiplicative.toAdd n)))
  map_one' := by simp only [toAdd_one, nLoop_zero]; rfl
  map_mul' a b := by
    simp only [toAdd_mul, show Multiplicative.toAdd a + Multiplicative.toAdd b =
      Multiplicative.toAdd b + Multiplicative.toAdd a from add_comm _ _]
    exact (Quotient.sound (nLoop_add _ _)).symm

open CategoryTheory in
/-- **The fundamental group of the circle is ℤ.** -/
noncomputable def fundamentalGroupCircle : Multiplicative ℤ ≃* FundamentalGroup uc 0 :=
  MulEquiv.ofBijective windingHom
    ⟨fun a b hab => by
      obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hab
      have key := isCoveringMap_covMap.liftPath_apply_one_eq_of_homotopicRel
        ⟨H⟩ (0 : ℝ) (by simp [covMap]) (by simp [covMap])
      rw [liftPath_nLoop, liftPath_nLoop] at key
      simp only [ContinuousMap.coe_mk, linearLift, Set.Icc.coe_one, mul_one] at key
      ext; exact_mod_cast key,
    fun q => Quotient.inductionOn q fun ω => by
      obtain ⟨n, hn⟩ := surj_nLoop ω
      exact ⟨Multiplicative.ofAdd n, Quotient.sound hn⟩⟩

end AddCircle
