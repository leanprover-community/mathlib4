/-
Copyright (c) 2025 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
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

## Main results

* `AddCircle.nLoop_surjective` : every loop at `0` in `AddCircle 1` is homotopic to some
  `nLoop n` (surjectivity of the winding number map).
* `AddCircle.nLoop_homotopic_iff` : `(nLoop m).Homotopic (nLoop n) ↔ m = n`.
* `AddCircle.windingNumberIso` :
  `FundamentalGroup (AddCircle 1) 0 ≃* Multiplicative ℤ`.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher02], Theorem 1.7 and Proposition 1.31.
-/

public section

open unitInterval

namespace AddCircle

/-- The loop `ωₙ` in `AddCircle 1` that winds `n` times, defined as `t ↦ n • t`.
  This is the representative loop in each homotopy class. -/
def nLoop (n : ℤ) : Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := n • t
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one]
    rw [AddCircle.coe_period]
    exact zsmul_zero n
  continuous_toFun := (continuous_zsmul n).comp
    (continuous_quotient_mk'.comp continuous_subtype_val)

/-- Preimages of `0 : AddCircle 1` under the covering map are exactly the integers. -/
lemma covMap_eq_zero_iff (k : ℝ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 →
    ∃ (n : ℤ), k = (n : ℝ) := by
  intro h1
  rw [AddCircle.coe_eq_zero_iff] at h1
  rcases h1 with ⟨n, hn⟩
  exact ⟨n, by simp at hn; linarith⟩

/-- Integer values map to zero under the covering map. -/
@[simp] lemma covMap_intCast (m : ℤ) : ((m : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  have : (m : ℝ) = m • (1 : ℝ) := by simp
  rw [this, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]

/-- The lift of `nLoop n` to `ℝ` starting at `0` is the linear path `t ↦ n * t`. -/
private lemma liftPath_nLoop (n : ℤ) :
    ((AddCircle.isCoveringMap_coe 1).liftPath (nLoop n).toContinuousMap 0
      (by simp) : C(I, ℝ))
    = ⟨fun t => (n : ℝ) * t, by fun_prop⟩ := by
  symm
  rw [IsCoveringMap.eq_liftPath_iff']
  refine ⟨funext fun ⟨t, ht⟩ => ?_, by simp⟩
  simp only [Function.comp_apply, ContinuousMap.coe_mk, nLoop]
  have : (↑n : ℝ) * t = n • t := by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
  rw [this, AddCircle.coe_zsmul]

/-- **Surjectivity of the winding number**: every loop at `0` in `AddCircle 1` is homotopic to
  `nLoop n` for some integer `n`. -/
theorem nLoop_surjective (ω : Path (0 : AddCircle (1 : ℝ)) 0) :
    ∃ (n : ℤ), (nLoop n).Homotopic ω := by
  -- Lift ω to ℝ starting at 0
  have ω_src : ω.toContinuousMap 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by simp
  let ω_lift := (AddCircle.isCoveringMap_coe 1).liftPath ω.toContinuousMap 0 ω_src
  -- The endpoint of the lift projects to 0, so it must be an integer
  have ω_lift_end : ((ω_lift 1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have := congr_fun ((AddCircle.isCoveringMap_coe 1).liftPath_lifts ω.toContinuousMap 0 ω_src) 1
    simpa [Function.comp_apply] using this
  obtain ⟨n, hn⟩ := covMap_eq_zero_iff (ω_lift 1) ω_lift_end
  use n
  -- Build paths in ℝ from 0 to n: the linear lift and ω's lift
  have ω_lift_zero : ω_lift 0 = 0 :=
    (AddCircle.isCoveringMap_coe 1).liftPath_zero ω.toContinuousMap 0 ω_src
  let path_ω_lift : Path (0 : ℝ) n := ⟨ω_lift, ω_lift_zero, hn⟩
  let path_linear : Path (0 : ℝ) n :=
    ⟨⟨fun t => (n : ℝ) * t, by fun_prop⟩, by simp, by simp⟩
  -- ℝ is simply connected, so the two lifts are homotopic rel endpoints
  obtain ⟨H_R⟩ := SimplyConnectedSpace.paths_homotopic path_linear path_ω_lift
  -- Project the homotopy down to AddCircle 1 via the covering map
  have hx : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := by rw [← hn]; exact ω_lift_end
  have covMap_linear (s : I) :
      ((path_linear s : ℝ) : AddCircle (1 : ℝ)) = (nLoop n) s := by
    dsimp only [path_linear, nLoop, Path.coe_mk_mk]
    have : (↑n : ℝ) * ↑s = n • (↑s : ℝ) := by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
    rw [this]; rfl
  have covMap_omega (s : I) :
      ((path_ω_lift s : ℝ) : AddCircle (1 : ℝ)) = ω s := by
    have := congr_fun ((AddCircle.isCoveringMap_coe 1).liftPath_lifts
      ω.toContinuousMap 0 ω_src) s
    simpa [Function.comp_apply] using this
  exact ⟨{
    toFun := fun (t, s) => ((H_R (t, s) : ℝ) : AddCircle (1 : ℝ))
    continuous_toFun := (AddCircle.isCoveringMap_coe 1).continuous.comp H_R.continuous_toFun
    map_zero_left s := by simp [H_R.apply_zero, covMap_linear]
    map_one_left s := by simp [H_R.apply_one, covMap_omega]
    prop' t s hs := by
      rcases hs with rfl | (rfl : s = 1)
      · simp
      · simp }⟩

/-- **Injectivity of the winding number**: `nLoop m` and `nLoop n` are homotopic iff `m = n`. -/
theorem nLoop_homotopic_iff (m n : ℤ) : (nLoop m).Homotopic (nLoop n) ↔ m = n := by
  constructor
  · intro ⟨H⟩
    have key := (AddCircle.isCoveringMap_coe 1).liftPath_apply_one_eq_of_homotopicRel
      ⟨H⟩ (0 : ℝ) (by simp) (by simp)
    rw [liftPath_nLoop, liftPath_nLoop] at key
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one] at key
    exact_mod_cast key
  · rintro rfl; exact ⟨.refl _⟩

/-- The lift of `nLoop n` starting at integer `m` is the affine path `t ↦ m + n * t`. -/
private lemma liftPath_nLoop_at (m n : ℤ) :
    ((AddCircle.isCoveringMap_coe 1).liftPath (nLoop n).toContinuousMap (m : ℝ)
      (by simp only [Path.coe_toContinuousMap, Path.source]
          exact (covMap_intCast m).symm) : C(I, ℝ))
    = ⟨fun t => (m : ℝ) + (n : ℝ) * t,
        continuous_const.add ((continuous_const).mul continuous_subtype_val)⟩ := by
  symm
  rw [IsCoveringMap.eq_liftPath_iff']
  refine ⟨funext fun ⟨t, ht⟩ => ?_, by norm_num⟩
  simp only [Function.comp_apply, ContinuousMap.coe_mk, nLoop]
  have h1 : (↑m : ℝ) + (↑n : ℝ) * t = (↑n : ℝ) * t + (↑m : ℝ) := by ring
  have h2 : (↑n : ℝ) * t = n • t := by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
  rw [h1, h2, ← AddCircle.coe_zsmul]
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
    ⟨⟨fun t => (m : ℝ) * t, by fun_prop⟩, by simp, by simp⟩
  let p2 : Path (↑m : ℝ) ((↑m : ℝ) + ↑n) :=
    ⟨⟨fun t => (↑m : ℝ) + (↑n : ℝ) * t,
      continuous_const.add (continuous_const.mul continuous_subtype_val)⟩,
     by norm_num, by simp⟩
  let path_concat := p1.trans p2
  -- Path in ℝ projecting to nLoop (m+n): linear 0→m+n
  let path_mn : Path (0 : ℝ) ((↑m : ℝ) + ↑n) :=
    ⟨⟨fun t => ((m + n : ℤ) : ℝ) * t, by fun_prop⟩, by simp, by simp⟩
  -- path_mn projects to nLoop (m+n)
  have covMap_mn (s : I) :
      ((path_mn s : ℝ) : AddCircle (1 : ℝ)) = (nLoop (m + n)) s := by
    dsimp only [path_mn, nLoop, Path.coe_mk_mk]
    have : (↑(m + n) : ℝ) * ↑s = (m + n) • (↑s : ℝ) := by
      rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
    rw [this]; rfl
  -- Each piece projects correctly (abstract over I to avoid Set.projIcc coercion issues)
  have covMap_p1 : ∀ u : I, ((p1 u : ℝ) : AddCircle (1 : ℝ)) = (nLoop m) u := fun u => by
    dsimp only [p1, Path.coe_mk_mk, nLoop]
    have : (↑m : ℝ) * ↑u = m • (↑u : ℝ) := by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
    rw [this]; rfl
  have covMap_p2 : ∀ u : I, ((p2 u : ℝ) : AddCircle (1 : ℝ)) = (nLoop n) u := fun u => by
    dsimp only [p2, Path.coe_mk_mk, nLoop]
    have h1 : (↑m : ℝ) + (↑n : ℝ) * ↑u = (↑n : ℝ) * ↑u + (↑m : ℝ) := by ring
    have h2 : (↑n : ℝ) * ↑u = n • (↑u : ℝ) := by rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
    rw [h1, h2, ← AddCircle.coe_zsmul]
    exact QuotientAddGroup.eq.mpr (by
      have : -(n • (↑u : ℝ) + (↑m : ℝ)) + (n • ↑u) = -(↑m : ℝ) := by ring
      rw [this]; exact ⟨-m, by simp⟩)
  -- path_concat projects to (nLoop m).trans (nLoop n)
  have covMap_concat (s : I) :
      ((path_concat s : ℝ) : AddCircle (1 : ℝ)) = ((nLoop m).trans (nLoop n)) s := by
    simp only [path_concat, Path.trans_apply]
    split_ifs <;> [exact covMap_p1 _; exact covMap_p2 _]
  -- ℝ simply connected → both lifts homotopic
  obtain ⟨H_R⟩ := SimplyConnectedSpace.paths_homotopic path_concat path_mn
  -- Project the homotopy down to AddCircle 1 via the covering map
  exact ⟨{
    toFun := fun (t, s) => ((H_R (t, s) : ℝ) : AddCircle (1 : ℝ))
    continuous_toFun := (AddCircle.isCoveringMap_coe 1).continuous.comp H_R.continuous_toFun
    map_zero_left s := by simp [H_R.apply_zero, covMap_concat]
    map_one_left s := by simp [H_R.apply_one, covMap_mn]
    prop' t s hs := by
      rcases hs with rfl | (rfl : s = 1)
      · simp
      · simp [covMap_intCast] }⟩

/-- `nLoop 0` is the constant loop at `0`. -/
private lemma nLoop_zero : nLoop 0 = Path.refl (0 : AddCircle (1 : ℝ)) := by
  ext t; simp [nLoop]

open CategoryTheory

private noncomputable def windingHom :
    Multiplicative ℤ →* FundamentalGroup (AddCircle (1 : ℝ)) 0 where
  toFun n := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (nLoop (Multiplicative.toAdd n)))
  map_one' := by simp only [toAdd_one, nLoop_zero]; rfl
  map_mul' a b := by
    simp only [toAdd_mul, show Multiplicative.toAdd a + Multiplicative.toAdd b =
      Multiplicative.toAdd b + Multiplicative.toAdd a from add_comm _ _]
    exact (Quotient.sound (nLoop_add _ _)).symm

/-- **The fundamental group of the circle is ℤ.** -/
noncomputable def windingNumberIso :
    Multiplicative ℤ ≃* FundamentalGroup (AddCircle (1 : ℝ)) 0 :=
  MulEquiv.ofBijective windingHom
    ⟨fun a b hab => by
        ext; exact (nLoop_homotopic_iff _ _).mp (Path.Homotopic.Quotient.exact hab),
      fun q => Quotient.inductionOn q fun ω => by
        obtain ⟨n, hn⟩ := nLoop_surjective ω
        exact ⟨Multiplicative.ofAdd n, Quotient.sound hn⟩⟩

end AddCircle
