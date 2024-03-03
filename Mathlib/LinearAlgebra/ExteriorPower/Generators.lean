/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Order.Extension.Well

/-!
# Basis of the exterior power

We construct generating families and bases for the exterior powers of a module.

## Definitions

* `Basis.exteriorPower`: If `b` is a basis of `M` (indexed by a linearly ordered type),
the basis of the `n`th exterior power of `M` formed by the `n`-fold exterior products of elements
of `b`.

## Theorems

* `exteriorPower.span_top_of_span_top` and `exteriorPower.span_top_of_span_top'`: If a family of
vectors spans `M`, then the family of its `n`-fold exterior products spans `⋀[R]^n M`. (We give
versions in the exterior algebra and in the exterior power.)

* `exteriorPower.finrank_eq`: If `R` satisfies the strong rank condition and `M` is
finite free of rank `r`, then the `n`th exterior power of `M` is of finrank `Nat.choose r n`.

* `exteriorPower.ιMulti_family_linearIndependent_field`: If `R` is a field, and if `v` is a
linearly independent family of vectors (indexed by a linearly ordered type), then the family of
`n`-fold exterior products of elements of `v` is also linearly independent.

## Instances

* `exteriorPower.instFinite`: The `n`th exterior power of a finite module is a finite module.

* `exteriorPower.instFree`: If `M` is a free module, then so is its `n`th exterior power.
-/

variable {R M N : Type*} {n : ℕ}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {K E F : Type*}
  [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) :=
  Module.Finite.mk ((Submodule.fg_top _).mpr (Submodule.FG.pow (by
  rw [LinearMap.range_eq_map]; exact Submodule.FG.map _  (Module.finite_def.mp inferInstance)) _ ))

variable (R n)

/-! Generators of exterior powers. -/

open Finset in
/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`⋀[R]^n M`. Here we work in the exterior algebra. -/
lemma span_top_of_span_top {I : Type*} [LinearOrder I] {v : I → M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ⋀[R]^n M := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro
    rw [SetLike.mem_coe, ιMulti_family_coe, Submodule.coeSubtype, Function.comp_apply]
    exact Submodule.coe_mem _
  · unfold ExteriorAlgebra.exteriorPower
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    have ⟨f, hf⟩ := Set.mem_pow.mp hu
    let g (i : Fin n) : M := ExteriorAlgebra.ιInv (f i).1
    have hfg : ∀ (i : Fin n), (f i).1 = ExteriorAlgebra.ι R (g i) := by
      intro i
      have ⟨_, _, hv⟩ := (Set.mem_image _ _ _).mp (f i).2
      simp only
      rw [← hv, ExteriorAlgebra.ι_inj, ExteriorAlgebra.ι_leftInverse]
    have heq : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ← hf]
      exact congrArg _ <| congrArg _ <| funext fun i ↦ hfg i
    rw [heq]
    have hg : ∀ (i : Fin n), ∃ (j : I), g i = v j := by
      intro i
      let ⟨x, hx⟩ := (Set.mem_image _ _ _).mp (f i).2
      let ⟨j, hj⟩ := Set.mem_range.mp hx.1
      rw [hfg i, ExteriorAlgebra.ι_inj] at hx
      exact ⟨j, by rw [hj, hx.2]⟩
    choose α hα using hg
    by_cases hinj : Function.Injective α
    · let h (i : Fin n) : image α univ :=
        ⟨α i, mem_image_univ_iff_mem_range.mpr <| Set.mem_range_self _⟩
      have hbij : Function.Bijective h := by
        refine ⟨fun i j hij ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
        · rw [← hinj.eq_iff, ← Subtype.mk.injEq]
          exact hij
        · have ⟨a, _, ha⟩ := Finset.mem_image.mp hi
          exact ⟨a, (Subtype.mk.injEq _ _ _ _).mpr ha⟩
      have hcard : (image α univ).card = n :=
        (card_image_of_injective univ hinj).trans (card_fin n)
      let g' (i : Fin n) : M := v ↑(orderIsoOfFin _ hcard i)
      have hg' : ExteriorAlgebra.ιMulti R n g' ∈
          Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) :=
        Submodule.subset_span ⟨⟨_, hcard⟩, rfl⟩
      let σ : Equiv.Perm (Fin n) :=
        (Equiv.ofBijective h hbij).trans (orderIsoOfFin _ hcard).toEquiv.symm
      have hgg' : g = g' ∘ σ := by
        ext i
        unfold_let g'
        rw [Function.comp_apply, Equiv.trans_apply, Equiv.ofBijective_apply,
          OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv, OrderIso.apply_symm_apply,
          Subtype.coe_mk]
        exact hα i
      rw [hgg', AlternatingMap.map_perm]
      exact Submodule.smul_mem _ _ hg'
    · change ¬(∀ (a b : Fin n), _) at hinj
      push_neg at hinj
      obtain ⟨i, j, hij1, hij2⟩ := hinj
      have heq : g = Function.update g i (g j) := by
        ext k
        by_cases hk : k = i
        · rw [hk, Function.update_same, hα i, hα j, hij1]
        · rw [Function.update_noteq hk]
      rw [heq, AlternatingMap.map_update_self _ _ hij2, SetLike.mem_coe]
      exact Submodule.zero_mem _

/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`⋀[R]^n M`. This is a variant of `exteriorPower.span_top_of_span_top` where we
work in the exterior power and not the exterior algebra. -/
lemma span_top_of_span_top' {I : Type*} [LinearOrder I]
    {v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ιMulti_family R n v)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨u, hu⟩ -
  have ⟨w, hw, huw⟩ : ∃ x ∈ Submodule.span R (Set.range (ιMulti_family R n v)), ↑x = u := by
    rw [← Submodule.coeSubtype, ← Submodule.mem_map, Submodule.map_span, ← Set.range_comp,
      ← ιMulti_family_coe, span_top_of_span_top R n hv]
    exact hu
  have heq : w = ⟨u, hu⟩ := SetCoe.ext huw
  rw [← heq]
  exact hw

/-- If `v` is a family of vectors of `M` indexed by a linearly ordered type, then the span of the
range of `exteriorPower.ιMult_family R n v`, i.e. of the family of `n`-fold exterior products
of elements of `v`, is the image of the map of exterior powers induced by the inclusion of
the span of `v` into `M`. -/
lemma span_of_span {I : Type*} [LinearOrder I] (v : I → M) :
    LinearMap.range (map n (Submodule.subtype (Submodule.span R (Set.range v)))) =
    Submodule.span R (Set.range (ιMulti_family R n v)) := by
  conv_lhs => rw [LinearMap.range_eq_map]
  rw [← span_top_of_span_top' (I := I) (R := R)
        (v := fun i ↦ ⟨v i, Submodule.subset_span <| Set.mem_range_self _⟩),
    Submodule.map_span, ← Set.range_comp]
  · congr; apply congrArg
    rw [map_ιMulti_family]
    congr
  · apply SetLike.coe_injective'
    apply Set.image_injective.mpr (Submodule.injective_subtype (Submodule.span R (Set.range v)))
    rw [← Submodule.map_coe, ← Submodule.span_image, ← Submodule.map_coe, ← LinearMap.range_eq_map,
      Submodule.range_subtype]
    rw [← Set.range_comp]
    congr

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearFormOfFamily` construction to the fanily of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) : ⋀[R]^n M →ₗ[R] R :=
  linearFormOfFamily R n (fun i ↦ b.coord (Finset.orderIsoOfFin s hs i))

@[simp]
lemma linearFormOfBasis_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
    linearFormOfBasis R n b hs (ιMulti R n v) = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
    ∏ i, b.coord (Finset.orderIsoOfFin s hs i) (v (σ i)) := by
  unfold linearFormOfBasis
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfFamily_apply, toTensorPower_apply_ιMulti,
    map_sum, LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod,
    Basis.coord_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma linearFormOfBasis_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨s, hs⟩) = 1 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  have hzero : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ Finset.univ → ¬σ ∈ ({Equiv.refl (Fin n)} :
    Finset (Equiv.Perm (Fin n))) → TensorPower.linearFormOfFamily R n
    (fun i ↦ b.coord (Finset.orderIsoOfFin s hs i)) (Equiv.Perm.sign σ • ⨂ₜ[R] (i : Fin n),
    b ((Finset.orderIsoOfFin s hs) (σ i))) = 0 := by
    intro σ _ hσ
    simp only [Finset.mem_singleton] at hσ
    erw [LinearMap.map_smul]
    apply smul_eq_zero_of_right
    simp only [Finset.coe_orderIsoOfFin_apply, TensorPower.linearFormOfFamily_apply_tprod]
    have h : ∃ (i : Fin n), ¬ σ i = i := by
      by_contra habs
      push_neg at habs
      apply hσ
      ext i
      simp only [Equiv.refl_apply]
      rw [habs i]
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Finset.coe_orderIsoOfFin_apply, OrderEmbedding.eq_iff_eq, ite_eq_right_iff]
    simp only [hi, IsEmpty.forall_iff]
  have heq := Finset.sum_subset (s₁ := {Equiv.refl (Fin n)}) (Finset.subset_univ _) hzero
  simp only [Finset.coe_orderIsoOfFin_apply, LinearMap.map_smul_of_tower,
    TensorPower.linearFormOfFamily_apply_tprod, Basis.coord_apply, Basis.repr_self, ne_eq,
    RelEmbedding.inj, Finset.sum_singleton, Equiv.Perm.sign_refl, Equiv.refl_apply,
    Finsupp.single_eq_same, Finset.prod_const_one, one_smul] at heq ⊢
  rw [← heq]

lemma linearFormOfBasis_apply_nondiag_aux {I : Type*} [LinearOrder I] {s t : Finset I}
    (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) :
    ∃ (i : Fin n), (Finset.orderIsoOfFin s hs i).1 ≠ (Finset.orderIsoOfFin t ht (σ i)).1 := by
  by_contra! habs
  push_neg at habs
  apply hst
  apply Finset.eq_of_subset_of_card_le
  · intro a has
    let b := Finset.orderIsoOfFin t ht (σ ((Finset.orderIsoOfFin s hs).symm ⟨a, has⟩))
    have heq : a = b.1 := by
      rw [← habs]
      simp only [OrderIso.apply_symm_apply]
    rw [heq]
    exact b.2
  · rw [hs, ht]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
lemma linearFormOfBasis_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨t, ht⟩) = 0 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  erw [zsmul_eq_smul_cast R]
  apply smul_eq_zero_of_right
  have ⟨i, hi⟩ := linearFormOfBasis_apply_nondiag_aux n hs ht hst σ
  apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
  rw [Basis.coord_apply, Basis.repr_self_apply]
  simp only [Finset.coe_orderIsoOfFin_apply, ne_eq] at hi
  simp only [Finset.coe_orderIsoOfFin_apply, Ne.symm hi, ite_false]

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  linearIndependent_of_dualFamily _ (fun s ↦ linearFormOfBasis R n b s.2)
  (fun ⟨_, _⟩ ⟨_, _⟩ hst ↦ by
    rw [ne_eq, Subtype.mk.injEq] at hst
    exact linearFormOfBasis_apply_nondiag _ _ _ _ _ hst)
  (fun ⟨_, _⟩ ↦ linearFormOfBasis_apply_diag _ _ _ _)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| span_top_of_span_top' R n (Basis.span_eq b))

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (Basis.exteriorPower R n b) = ιMulti_family R n b :=
  Basis.coe_mk _ _

@[simp]
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    Basis.exteriorPower R n b ⟨s, hs⟩ = ιMulti_family R n b ⟨s, hs⟩ := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.linearFormOfBasis`. -/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    Basis.coord (Basis.exteriorPower R n b) ⟨s, hs⟩ = linearFormOfBasis R n b hs := by
  apply LinearMap.ext_on (span_top_of_span_top' R n (Basis.span_eq b))
  intro x hx
  have ⟨⟨t, ht⟩, htx⟩ := Set.mem_range.mp hx
  rw [← htx]
  conv_lhs => rw [← basis_apply]
  by_cases heq : s = t
  · have heq' : (⟨s, hs⟩ : {s : Finset I // Finset.card s = n}) = ⟨t, ht⟩ := by
      simp only [Subtype.mk.injEq]; exact heq
    simp only [← heq', linearFormOfBasis_apply_diag, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same]
  · simp only [linearFormOfBasis_apply_nondiag R n b hs ht heq, Basis.coord_apply,
      Basis.repr_self_apply, Subtype.mk.injEq, Ne.symm heq, ite_false]

/-! ### Freeness and dimension of `⋀[R]^n M. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [hfree : Module.Free R M] : Module.Free R (⋀[R]^n M) :=
  let ⟨I, b⟩ := hfree.exists_basis
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  Module.Free.of_basis (Basis.exteriorPower R n b)

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [hfree : Module.Free R M] [Module.Finite R M] :
    FiniteDimensional.finrank R (⋀[R]^n M) =
    Nat.choose (FiniteDimensional.finrank R M) n := by
  letI := WellFounded.wellOrderExtension (emptyWf (α := hfree.ChooseBasisIndex)).wf
  let B := Basis.exteriorPower R n hfree.chooseBasis
  rw [FiniteDimensional.finrank_eq_card_basis hfree.chooseBasis,
    FiniteDimensional.finrank_eq_card_basis B, Fintype.card_finset_len]

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  let v' : I → W := fun i ↦ ⟨v i, Submodule.subset_span <| exists_apply_eq_apply _ _⟩
  have h : v = W.subtype ∘ v' :=
    funext (fun _ ↦ by simp only [Submodule.coeSubtype, Function.comp_apply])
  rw [h, ← map_ιMulti_family]
  refine LinearIndependent.map' ?_ (map n W.subtype)
    (LinearMap.ker_eq_bot.mpr (map_injective_field n (Submodule.ker_subtype _)))
  have hv'span : ⊤ ≤ Submodule.span K (Set.range v') := by
    rintro x -
    rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W),
      ← Set.range_comp, ← h, Submodule.coeSubtype]
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
