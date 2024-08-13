/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Heights on Weierstrass curves
-/

open IsDedekindDomain NumberField

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K]

noncomputable def IsDedekindDomain.HeightOneSpectrum.realValuation (v : HeightOneSpectrum R)
    (x : K) : ℝ :=
  (v.valuation x).casesOn 0 (fun x => (Nat.card <| R ⧸ v.asIdeal : ℝ) ^ Multiplicative.toAdd x)

variable [NumberField K]

namespace NumberField

variable (K) in
def Place : Type v :=
  HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

noncomputable def Place.valuation (v : Place K) (x : K) : ℝ :=
  v.casesOn (fun v => v.realValuation x) (fun v => v x)

-- TODO: define the prime p below v and [Kᵥ : ℚₚ]
open Classical in
noncomputable def Place.localDegree (v : Place K) : ℕ :=
  v.casesOn (fun v => sorry) (fun v => if v.IsReal then 1 else 2)

end NumberField

namespace WeierstrassCurve.Affine.Point

variable {W : Affine K}

noncomputable def naiveHeight : W.Point → ℝ
  | zero => 1
  | @some _ _ _ x _ _ =>
    (∏ᶠ v : Place K, max 1 (v.valuation x) ^ v.localDegree) ^ (1 / FiniteDimensional.finrank ℚ K)

noncomputable def logarithmicHeight (P : W.Point) : ℝ :=
  P.naiveHeight.log

noncomputable def heightSeq (P : W.Point) : ℕ → ℝ :=
  fun n => ((2 ^ n) • P).logarithmicHeight / 4 ^ n

-- TODO: prove that the naive height is almost a quadratic form
lemma isCauchy_heightSeq (P : W.Point) : IsCauSeq abs P.heightSeq :=
  sorry

noncomputable def canonicalHeight (P : W.Point) : ℝ :=
  CauSeq.lim ⟨fun n => ((2 ^ n) • P).logarithmicHeight / 4 ^ n, P.isCauchy_heightSeq⟩

end WeierstrassCurve.Affine.Point
