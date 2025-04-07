/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/

import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The Amice Transform of p-adic measure


## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

open Finset IsUltrametricDist NNReal Filter PowerSeries

open scoped fwdDiff ZeroAtInfty Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

noncomputable def Amice_iso :
 (C(ℤ_[p],ℤ_[p]) →L[ℤ_[p]] ℤ_[p]) ≃ₗᵢ[ℤ_[p]]
   C(ℕ ,ℤ_[p])where
