/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Volumetric Packing Fraction of the 3D Hexagonal Close-Packed (HCP) Lattice

This file formalizes the unit-cell volume and exact volumetric sphere-packing fraction
`η_HCP = π / (3 * √2)` (the Gauss–Hales optimal close-packing density `≈ 0.74048`)
of a three-dimensional Hexagonal Close-Packed (HCP) crystal lattice, together with its
interstitial void fraction `1 - η_HCP` and rigorous numerical enclosures.

## Main definitions

* `HCPLattice.ballVolume`: volume `(4 / 3) * π * r³` of a 3D Euclidean ball.
* `HCPLattice.hcpUnitCellVolume`: volume of a two-layer (`ABAB`) primitive rhombic HCP unit cell.

## Main results

* `HCPLattice.hcpUnitCellVolume_eq`: exact volume formula `hcpUnitCellVolume a = √2 * a³`.
* `HCPLattice.hcp_packing_fraction`: exact volumetric packing density `π / (3 * √2)`.
* `HCPLattice.hcp_packing_fraction_bounds` & `HCPLattice.hcp_void_fraction_bounds`: rigorous
  analytical enclosures `0.74 < η_HCP < 0.75` and `0.25 < 1 - η_HCP < 0.26`.
-/

@[expose] public section

noncomputable section

namespace HCPLattice

/-- Volume `(4 / 3) * π * r³` of a three-dimensional Euclidean ball of radius `r`. -/
def ballVolume (r : ℝ) : ℝ :=
  (4 / 3) * Real.pi * r ^ 3

/-- Base area `(√3 / 2) * a²` of a primitive rhombic HCP basal cell with lattice constant `a`. -/
def hcpBasalArea (a : ℝ) : ℝ :=
  (Real.sqrt 3 / 2) * a ^ 2

/-- Ideal axial height `c = 2 * √(2 / 3) * a` of a two-layer (`ABAB`) HCP unit cell. -/
def hcpCellHeight (a : ℝ) : ℝ :=
  2 * Real.sqrt (2 / 3) * a

/-- Total volume `hcpBasalArea a * hcpCellHeight a` of the two-sphere HCP unit cell. -/
def hcpUnitCellVolume (a : ℝ) : ℝ :=
  hcpBasalArea a * hcpCellHeight a

/-- Exact volume formula `hcpUnitCellVolume a = √2 * a³` for the HCP unit cell. -/
theorem hcpUnitCellVolume_eq (a : ℝ) :
    hcpUnitCellVolume a = Real.sqrt 2 * a ^ 3 := by
  dsimp [hcpUnitCellVolume, hcpBasalArea, hcpCellHeight]
  have h_sqrt : Real.sqrt 3 * Real.sqrt (2 / 3) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  calc (Real.sqrt 3 / 2 * a ^ 2) * (2 * Real.sqrt (2 / 3) * a)
    _ = (Real.sqrt 3 * Real.sqrt (2 / 3)) * a ^ 3 := by ring
    _ = Real.sqrt 2 * a ^ 3 := by rw [h_sqrt]

/-- **Optimal HCP packing fraction (`η_HCP = π / (3√2)`):** for touching spheres of radius
`r > 0` (`a = 2 * r`), the ratio of the volume of the two spheres in the HCP unit cell to the
total cell volume equals `π / (3 * √2)` independently of `r`. -/
theorem hcp_packing_fraction {r : ℝ} (hr : r ≠ 0) :
    (2 * ballVolume r) / hcpUnitCellVolume (2 * r) = Real.pi / (3 * Real.sqrt 2) := by
  rw [hcpUnitCellVolume_eq]
  dsimp [ballVolume]
  have h_num : 2 * ((4 / 3) * Real.pi * r ^ 3) = (8 * Real.pi * r ^ 3) / 3 := by ring
  have h_den : Real.sqrt 2 * (2 * r) ^ 3 = (8 * Real.sqrt 2) * r ^ 3 := by ring
  rw [h_num, h_den]
  have h_sq2_ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- **Numerical enclosure of the HCP packing density (`0.74 < η_HCP < 0.75`):**
rigorous analytical verification that the close-packed volumetric fraction lies strictly
between `74%` and `75%`. -/
theorem hcp_packing_fraction_bounds :
    (74 / 100 : ℝ) < Real.pi / (3 * Real.sqrt 2) ∧
    Real.pi / (3 * Real.sqrt 2) < (75 / 100 : ℝ) := by
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_hi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hsq2_pos : 0 < Real.sqrt 2 := by positivity
  have hsq2_lo : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq2_hi : Real.sqrt 2 < (1.4143 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-- **Interstitial void fraction bounds (`0.25 < 1 - η_HCP < 0.26`):**
the tetrahedral and octahedral interstices of an HCP crystal occupy strictly between
`25%` and `26%` of total Euclidean volume. -/
theorem hcp_void_fraction_bounds :
    (25 / 100 : ℝ) < 1 - Real.pi / (3 * Real.sqrt 2) ∧
    1 - Real.pi / (3 * Real.sqrt 2) < (26 / 100 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hcp_packing_fraction_bounds
  exact ⟨by linarith, by linarith⟩

end HCPLattice
