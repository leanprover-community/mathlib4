/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Co-finitely generated submodules

This files defines the notion of a co-finitely generated submodule. A submodule `S` of a module
`M` is co-finitely generated (or CoFG for short) if the quotient of `M` by `S` is finitely
generated (i.e. FG).

## Main declarations

- `Submodule.CoFG` expresses that a submodule is co-finitely generated.

-/

@[expose] public section

namespace Submodule

section Ring

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A submodule `S` of a module `M` is co-finitely generated (CoFG) if the quotient
  space `M ⧸ S` is finitely generated. -/
abbrev CoFG (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

/-- A submodule of a noetherian module is CoFG. -/
@[simp] theorem CoFG.of_isNoetherian [IsNoetherian R M] {S : Submodule R M} : S.CoFG :=
  Module.Finite.quotient R S

/-- A submodule of a finitely generated module is CoFG. -/
alias CoFG.of_finite := CoFG.of_isNoetherian

/-- The top submodule is CoFG. -/
@[simp] theorem CoFG.top : (⊤ : Submodule R M).CoFG := inferInstance

/-- If the bottom submodule is CoFG, then the module is finite. -/
theorem _root_.Module.Finite.of_cofg_bot (h : (⊥ : Submodule R M).CoFG) : Module.Finite R M
    := Module.Finite.equiv (quotEquivOfEqBot ⊥ rfl)

/-- A complement of a CoFG submodule is FG. -/
theorem CoFG.isCompl_fg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG) : T.FG
  := Module.Finite.iff_fg.mp <| Module.Finite.equiv <| quotientEquivOfIsCompl S T hST

/-- A complement of an FG submodule is CoFG. -/
theorem FG.isCompl_cofg {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG := by
  haveI := Module.Finite.iff_fg.mpr hS
  exact Module.Finite.equiv (quotientEquivOfIsCompl T S hST.symm).symm

/-- The sup of a CoFG submodule with another submodule is CoFG. -/
theorem CoFG.sup_left {S : Submodule R M} (hS : S.CoFG) (T : Submodule R M) : (S ⊔ T).CoFG
  := Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

alias CoFG.sup := CoFG.sup_left

/-- The sup of a CoFG submodule with another submodule is CoFG. -/
theorem CoFG.sup_right (S : Submodule R M) {T : Submodule R M} (hT : S.CoFG) : (S ⊔ T).CoFG
  := Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

/-- A submodule that contains a CoFG submodule is CoFG. -/
theorem CoFG.of_cofg_le {S T : Submodule R M} (hT : S ≤ T) (hS : S.CoFG) : T.CoFG := by
  rw [← sup_eq_right.mpr hT]
  exact hS.sup T

/-- If a family of submodules contains a CoFG submodule then the supremum of the family is CoFG. -/
theorem CoFG.sSup {s : Set (Submodule R M)} (hs : ∃ S ∈ s, S.CoFG) : (sSup s).CoFG := by
  obtain ⟨S, hS, hcofg⟩ := hs
  rw [right_eq_sup.mpr <| le_sSup hS]
  exact hcofg.sup _

section LinearMap

open LinearMap

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The range of a linear map is FG if and only if the kernel is CoFG. -/
theorem range_fg_iff_ker_cofg {f : M →ₗ[R] N} : (range f).FG ↔ (ker f).CoFG := by
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.equiv_iff <| f.quotKerEquivRange.symm

/-- The kernel of a linear map into a Noetherian module is CoFG. -/
theorem ker_cofg [IsNoetherian R N] (f : M →ₗ[R] N) : (ker f).CoFG
    := range_fg_iff_ker_cofg.mp <| IsNoetherian.noetherian _

end LinearMap

section IsNoetherianRing

variable [IsNoetherianRing R]

/-- Over a noetherian ring the intersection of two CoFG submodules is CoFG. -/
theorem CoFG.inf {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG) :
      (S ⊓ T).CoFG := by
  rw [← Submodule.ker_mkQ S, ← Submodule.ker_mkQ T, ← LinearMap.ker_prod]
  exact ker_cofg _

/-- Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG. -/
theorem CoFG.sInf {s : Finset (Submodule R M)} (hs : ∀ S ∈ s, S.CoFG) :
    (sInf (s : Set (Submodule R M))).CoFG := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact hs.1.inf (hs' hs.2)

/-- Over a noetherian ring the infimum of a finite family of CoFG submodules is CoFG. -/
theorem CoFG.sInf' {s : Set (Submodule R M)} (hs : s.Finite) (hcofg : ∀ S ∈ s, S.CoFG) :
    (InfSet.sInf s).CoFG := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact CoFG.sInf hcofg

end IsNoetherianRing

end Ring

end Submodule
