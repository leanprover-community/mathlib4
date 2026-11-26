/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

variable {R : Type*} [Ring R]

-- Need left-right symmetry of Jacobson radical
proof_wanted IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ

proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
