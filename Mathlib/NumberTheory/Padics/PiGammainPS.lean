/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/



import Mathlib.NumberTheory.Padics.PSAC3
import Mathlib.NumberTheory.Padics.PsiandVar

open Finset IsUltrametricDist NNReal Filter  CauSeq  zero_atBot KaehlerDifferential
open scoped fwdDiff ZeroAtInfty Topology  LaurentSeries PowerSeries
variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt
noncomputable def action_PS (a:ℤ_[p]):ℤ_[p]⟦X⟧ →+* ℤ_[p]⟦X⟧ :=sorry
noncomputable def ϕ_PS :ℤ_[p]⟦X⟧ →+* ℤ_[p]⟦X⟧ :=sorry
noncomputable def ψ_PS :ℤ_[p]⟦X⟧ →+* ℤ_[p]⟦X⟧ :=sorry
lemma equiv_1(a:ℤ_[p]) (f:(C(ℤ_[p],ℤ_[p])→L[ℤ_[p]] ℤ_[p])): action_PS  a ( Amice_iso_2 f)=
Amice_iso_2 (action a f) :=by sorry
lemma equiv_2 (f:(C(ℤ_[p],ℤ_[p])→L[ℤ_[p]] ℤ_[p])): ϕ_PS ( Amice_iso_2 f)=
Amice_iso_2 (ϕ f) :=by sorry
lemma equiv_3 (f:(C(ℤ_[p],ℤ_[p])→L[ℤ_[p]] ℤ_[p])): ψ_PS ( Amice_iso_2 f)=
Amice_iso_2 (ψ f) :=by sorry

#check PowerSeries.trunc

end PadicInt
