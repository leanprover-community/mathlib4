/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Rat.Cast.Defs

deprecated_module (since := "2025-12-18")

@[expose] public section

@[deprecated (since := "2025-12-18")] alias algebraMap.coe_inv := map_inv₀

@[deprecated (since := "2025-12-18")] alias algebraMap.coe_div := map_div₀

@[deprecated (since := "2025-12-18")] alias algebraMap.coe_zpow := map_zpow₀

@[deprecated (since := "2025-12-18")] alias algebraMap.coe_ratCast := map_ratCast
