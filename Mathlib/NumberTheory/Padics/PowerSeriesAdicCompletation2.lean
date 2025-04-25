import Mathlib.NumberTheory.Padics.PowerSeriesAdicCompletation

set_option maxHeartbeats 1000000000000000000000000000000000000000000
set_option synthInstance.maxHeartbeats 1000000000000000000000000000000

open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot


open scoped fwdDiff ZeroAtInfty Topology
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries

namespace PadicInt
variable {p : ℕ} [hp : Fact p.Prime]

#check (p:ℤ_[p]⸨X⸩)
#check ((algebraMap ℤ_[p] ℤ_[p]⸨X⸩) ((p:ℤ_[p])))



noncomputable def Amice_Trans_PowerSeries:ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]]
AdicCompletion (Ideal.span {(p:ℤ_[p]⸨X⸩)}) ℤ_[p]⸨X⸩  where
    toFun r := ⟨algebraMap _ (∀ _, _) r, fun _ ↦ rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y
    commutes' r :=by
      ext n
      simp
      rfl


end PadicInt
