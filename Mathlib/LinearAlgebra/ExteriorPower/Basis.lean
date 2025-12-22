/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.TensorPower
public import Mathlib.Order.Extension.Well
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module

variable (R n)

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearForm` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def ιMulti_dual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) : Module.Dual R (⋀[R]^n M) :=
  linearForm R n (fun i ↦ b.coord (Finset.orderIsoOfFin s.1 s.2 i))

@[simp]
lemma ιMulti_dual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) (v : Fin n → M) :
    ιMulti_dual R n b s (ιMulti R n v) = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
      ∏ i, b.coord (Finset.orderIsoOfFin s.1 s.2 i) (v (σ i)) := by
  rw [ιMulti_dual, linearForm_apply, toTensorPower_apply_ιMulti, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.map_smul_of_tower, PiTensorProduct.dprod_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma ιMulti_dual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) :
    ιMulti_dual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family, ιMulti_dual_apply_ιMulti]
  rw [Finset.sum_eq_single (Equiv.refl (Fin n)) _ (fun h => absurd (Finset.mem_univ _) h)]
  · simp
  · rintro σ - hσ
    simp_rw [ne_eq, Equiv.ext_iff, not_forall, Equiv.refl_apply, ← ne_eq] at hσ
    obtain ⟨i, hi⟩ := hσ
    rw [smul_eq_zero_iff_eq, Finset.prod_eq_zero (Finset.mem_univ i)]
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne]
    simp only [Finset.coe_orderIsoOfFin_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact hi.symm

lemma ιMulti_apply_nondiag_aux {I : Type*} [LinearOrder I]
    (s t : {a : Finset I // a.card = n}) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) :
    ∃ (i : Fin n), (Finset.orderIsoOfFin s.1 s.2 i).1 ≠ (Finset.orderIsoOfFin t.1 t.2 (σ i)).1 := by
  by_contra! habs
  apply hst
  rw [Subtype.ext_iff]
  apply Finset.eq_of_subset_of_card_le _ (by rw [s.2, t.2])
  intro a has
  let b := Finset.orderIsoOfFin t.1 t.2 (σ ((Finset.orderIsoOfFin s.1 s.2).symm ⟨a, has⟩))
  have heq : a = b.1 := by
    rw [← habs]
    simp only [OrderIso.apply_symm_apply]
  rw [heq]
  exact b.2

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
lemma ιMulti_dual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : {a : Finset I // a.card = n}) (hst : s ≠ t) :
    ιMulti_dual R n b s (ιMulti_family R n b t) = 0 := by
  simp only [ιMulti_family]
  rw [ιMulti_dual_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  have ⟨i, hi⟩ := ιMulti_apply_nondiag_aux n s t hst σ
  apply smul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [Basis.coord_apply, Basis.repr_self_apply, if_neg (ne_comm.mp hi)]

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.ofDualFamily _ (fun s ↦ ιMulti_dual R n b s)
    (fun _ _ h => ιMulti_dual_apply_nondiag R n b _ _ h)
    (fun _ => ιMulti_dual_apply_diag _ _ _ _)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {a : Finset I // Finset.card a = n} R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (Basis.exteriorPower R n b) = ιMulti_family R n b :=
  Basis.coe_mk _ _

@[simp]
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : {a : Finset I // a.card = n}) :
    Basis.exteriorPower R n b s = ιMulti_family R n b s := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.linearFormOfBasis`. -/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : {a : Finset I // a.card = n}) :
    Basis.coord (Basis.exteriorPower R n b) s = ιMulti_dual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases heq : s = t
  · rw [heq, ιMulti_dual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMulti_dual_apply_nondiag R n b s t heq, ← basis_apply,
      Basis.repr_self, Finsupp.single_eq_of_ne (by rw [ne_eq]; exact heq)]

/-! ### Freeness and dimension of `⋀[R]^n M. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [hfree : Module.Free R M] : Module.Free R (⋀[R]^n M) :=
  have ⟨I, b⟩ := hfree.exists_basis
  letI : LinearOrder I := IsWellFounded.wellOrderExtension emptyWf.rel
  Module.Free.of_basis (Basis.exteriorPower R n b)

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [hfree : Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) =
    Nat.choose (Module.finrank R M) n := by
  letI : LinearOrder hfree.ChooseBasisIndex := IsWellFounded.wellOrderExtension emptyWf.rel
  let B := Basis.exteriorPower R n hfree.chooseBasis
  rw [Module.finrank_eq_card_basis hfree.chooseBasis,
    Module.finrank_eq_card_basis B, Fintype.card_finset_len]

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  let v' : I → W := fun i ↦ ⟨v i, Submodule.subset_span <| exists_apply_eq_apply _ _⟩
  have h : v = W.subtype ∘ v' := by
    ext x
    simp only [Submodule.coe_subtype, Function.comp_apply]
    rw [Subtype.val]
  rw [h, ← map_comp_ιMulti_family]
  refine LinearIndependent.map' ?_ (map n W.subtype)
    (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.ker_subtype _)))
  have hv'span : ⊤ ≤ Submodule.span K (Set.range v') := by
    rintro x -
    rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W),
      ← Set.range_comp, ← h, Submodule.coe_subtype]
    exact SetLike.coe_mem _
  have heq : ιMulti_family K n v' =
      Basis.exteriorPower K n (Basis.mk (.of_comp W.subtype (h ▸ hv)) hv'span) := by
    rw [coe_basis, Basis.coe_mk]
  rw [heq]
  apply Basis.linearIndependent

instance instNonempty {I : Type*} [LinearOrder I] [Nonempty {v : I → E // LinearIndependent K v}] :
    Nonempty {v : {s : Finset I // Finset.card s = n} → (⋀[K]^n) E // LinearIndependent K v} :=
  Nonempty.map (fun v : {v : I → E // LinearIndependent K v} ↦
    ⟨ιMulti_family K n v, ιMulti_family_linearIndependent_field n v.2⟩) ‹_›

end exteriorPower
