import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

universe u

-- A left Artinian ring is right Noetherian if and only if it is right Artinian.
example {R : Type u} [Ring R] [IsArtinianRing R] :
    IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ := by
  let : IsSemiprimaryRing Rᵐᵒᵖ := IsSemiprimaryRing.mulOpposite
  exact IsSemiprimaryRing.isNoetherian_iff_isArtinian
