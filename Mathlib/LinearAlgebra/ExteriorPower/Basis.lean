/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module Set Set.powersetCard

variable (R n)

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearForm` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def ιMultiDual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]
lemma ιMultiDual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) (v : Fin n → M) :
    ιMultiDual R n b s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j) (v i)).det := by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma ιMultiDual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) :
    ιMultiDual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
lemma ιMultiDual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : powersetCard I n) (hst : s ≠ t) :
    ιMultiDual R n b s (ιMulti_family R n b t) = 0 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_apply, Basis.repr_self]
  intro j
  apply Finsupp.single_eq_of_ne
  by_contra! h
  apply hit
  rw [h, powersetCard.ofFinEmbEquiv_symm_apply, ← powersetCard.mem_coe_iff]
  exact Finset.orderEmbOfFin_mem t.val t.prop j

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s ↦ ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

variable {R} in
/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Module.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis (powersetCard I n) R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b :=
  Basis.coe_mk _ _

lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    b.exteriorPower n s = ιMulti_family R n b s := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.ιMultiDual`. -/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.coord (b.exteriorPower n) s = ιMultiDual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hst]

lemma basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
    (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) x s = ιMultiDual R n b s x := by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]
lemma basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) s = 1 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]
lemma basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : powersetCard I n} (hst : s ≠ t) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) t = 0 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm

lemma basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) = Finsupp.single s 1 := by
  ext t
  by_cases hst : s = t <;> simp [hst]

/-! ### Freeness and dimension of `⋀[R]^n M`. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (b.exteriorPower n)

variable [Nontrivial R]

/-- If `R` is non-trivial and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) = Nat.choose (Module.finrank R M) n := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M), Module.finrank_eq_card_basis B,
    Fintype.card_eq_nat_card, powersetCard.card, Fintype.card_eq_nat_card]

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  suffices ∃ b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb, ← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.subtype_injective _)))
  use Module.Basis.span hv
  ext i
  rw [Submodule.coe_subtype, Function.comp_apply, Basis.span_apply]

end exteriorPower
