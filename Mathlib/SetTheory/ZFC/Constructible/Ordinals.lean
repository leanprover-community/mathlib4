/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Bounding

/-!
# Ordinals in the constructible universe

The property of being a von Neumann ordinal is expressed by a bounded
first-order formula.  Its absoluteness to a transitive level lets us prove,
simultaneously, that the ordinal elements of `LStageZF α` have rank below `α`
and that `α.toZFSet` is contained in that level.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

namespace OrdinalFormula

/-- `x` is transitive, in a context whose only free variable is `x`. -/
def transitive : FOFormula 1 :=
  FOFormula.boundedAll (0 : Fin 1)
    (FOFormula.boundedAll (Fin.last 1)
      (.mem (Fin.last 2) (0 : Fin 3)))

/-- Every member of `x` is transitive. -/
def membersTransitive : FOFormula 1 :=
  FOFormula.boundedAll (0 : Fin 1)
    (FOFormula.boundedAll (Fin.last 1)
      (FOFormula.boundedAll (Fin.last 2)
        (.mem (Fin.last 3) (1 : Fin 4))))

/-- The bounded formula saying that `x` is a von Neumann ordinal. -/
def isOrdinal : FOFormula 1 :=
  .conj transitive membersTransitive

theorem satisfies_transitive {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) transitive ![x] ↔
      x.1.IsTransitive := by
  simp only [transitive, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, zfCarrierMem, Matrix.cons_val_zero,
    snoc_last]
  constructor
  · intro h y hy z hz
    have hyU : y ∈ U := hU.mem_trans hy x.2
    have hzU : z ∈ U := hU.mem_trans hz hyU
    exact h ⟨y, hyU⟩ hy ⟨z, hzU⟩ hz
  · intro hx y hy z hz
    exact hx.mem_trans hz hy

theorem satisfies_membersTransitive {U : ZFSet.{u}}
    (hU : U.IsTransitive) (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) membersTransitive ![x] ↔
      ∀ y ∈ x.1, y.IsTransitive := by
  simp only [membersTransitive, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, zfCarrierMem, Matrix.cons_val_zero,
    snoc_last]
  constructor
  · intro h y hy z hz w hw
    have hyU : y ∈ U := hU.mem_trans hy x.2
    have hzU : z ∈ U := hU.mem_trans hz hyU
    have hwU : w ∈ U := hU.mem_trans hw hzU
    exact h ⟨y, hyU⟩ hy ⟨z, hzU⟩ hz ⟨w, hwU⟩ hw
  · intro h y hy z hz w hw
    exact (h y.1 hy).mem_trans hw hz

theorem satisfies_isOrdinal {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) isOrdinal ![x] ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [isOrdinal, FOFormula.Satisfies, satisfies_transitive hU x,
    satisfies_membersTransitive hU x]

end OrdinalFormula

/--
If the ordinals in a transitive carrier are exactly those of rank below `α`,
then the internal code for `α` is a definable subset of that carrier.
-/
theorem ordinal_toZFSet_mem_DefZF {U : ZFSet.{u}} {α : Ordinal.{u}}
    (hU : U.IsTransitive) (hsub : α.toZFSet ⊆ U)
    (hrank : ∀ {x : ZFSet.{u}}, x.IsOrdinal → x ∈ U → x.rank < α) :
    α.toZFSet ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨hsub, 0, (fun i => Fin.elim0 i),
    OrdinalFormula.isOrdinal, ?_⟩
  intro x
  have hassign : snoc (fun i : Fin 0 => Fin.elim0 i) x = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact snoc_last (fun i : Fin 0 => Fin.elim0 i) x
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU x
  rw [hassign]
  rw [hsemantic]
  constructor
  · intro hx
    exact (ZFSet.isOrdinal_toZFSet α).mem hx
  · intro hx
    rw [← hx.toZFSet_rank_eq]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hrank hx x.2)

/--
The two mutually supporting stage invariants for ordinals: ordinal elements
of `L_α` have rank below `α`, and `α` itself is a subset of `L_α`.
-/
theorem ordinal_stage_invariants (α : Ordinal.{u}) :
    (∀ {x : ZFSet.{u}}, x.IsOrdinal → x ∈ LStageZF α → x.rank < α) ∧
      α.toZFSet ⊆ LStageZF α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      constructor
      · intro x _hxOrd hx
        rw [LStageZF_zero] at hx
        exact (ZFSet.notMem_empty x hx).elim
      · simp
  | add_one α ih =>
      rw [← Order.succ_eq_add_one]
      have hαmem : α.toZFSet ∈ LStageZF (Order.succ α) := by
        rw [LStageZF_succ]
        exact ordinal_toZFSet_mem_DefZF (LStageZF_isTransitive α) ih.2 ih.1
      constructor
      · intro x hxOrd hx
        rw [LStageZF_succ] at hx
        have hxsub : x ⊆ LStageZF α := (mem_DefZF_iff.mp hx).1
        have hxsubOrdinal : x ⊆ α.toZFSet := by
          intro y hy
          have hyOrd : y.IsOrdinal := hxOrd.mem hy
          have hyrank : y.rank < α := ih.1 hyOrd (hxsub hy)
          rw [← hyOrd.toZFSet_rank_eq]
          exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hyrank
        have hrank : x.rank ≤ α := by
          simpa using
            (ZFSet.IsOrdinal.rank_le_iff_subset hxOrd
              (ZFSet.isOrdinal_toZFSet α)).mpr hxsubOrdinal
        exact Order.lt_succ_iff.mpr hrank
      · intro x hx
        rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨β, hβα, rfl⟩
        rcases (Order.lt_succ_iff.mp hβα).eq_or_lt with hEq | hlt
        · subst β
          exact hαmem
        · exact LStageZF_subset_succ α
            (ih.2 (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt))
  | limit l hl ih =>
      constructor
      · intro x hxOrd hx
        rcases (mem_LStageZF_limit_iff hl).mp hx with ⟨β, hβl, hxβ⟩
        exact ((ih β hβl).1 hxOrd hxβ).trans hβl
      · intro x hx
        rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨β, hβl, rfl⟩
        have hβinv := ih β hβl
        have hβmem : β.toZFSet ∈ LStageZF (Order.succ β) := by
          rw [LStageZF_succ]
          exact ordinal_toZFSet_mem_DefZF
            (LStageZF_isTransitive β) hβinv.2 hβinv.1
        exact (mem_LStageZF_limit_iff hl).mpr
          ⟨Order.succ β, hl.succ_lt hβl, hβmem⟩

/-- Every ordinal code occurs at the successor of its index. -/
theorem ordinal_toZFSet_mem_LStage_succ (α : Ordinal.{u}) :
    α.toZFSet ∈ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact ordinal_toZFSet_mem_DefZF (LStageZF_isTransitive α)
    (ordinal_stage_invariants α).2 (ordinal_stage_invariants α).1

/-- Every von Neumann ordinal is constructible. -/
theorem ordinal_toZFSet_mem_L (α : Ordinal.{u}) : α.toZFSet ∈ L :=
  ⟨Order.succ α, ordinal_toZFSet_mem_LStage_succ α⟩

/-- The von Neumann code of `ω` belongs to the constructible universe. -/
theorem omega_mem_L : Ordinal.omega0.toZFSet ∈ L :=
  ordinal_toZFSet_mem_L Ordinal.omega0

end ZFC

end Constructible
