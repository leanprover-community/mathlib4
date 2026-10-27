/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.EReal.Operations

open ENNReal

namespace EReal

proof_wanted recENNReal_neg_coe_ennreal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) {x : ℝ≥0∞} (hx : 0 < x) :
    recENNReal coe neg_coe (-x) = neg_coe x hx

end EReal
