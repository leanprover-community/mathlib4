/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Order.Extension.Well

/-! Add description.-/

universe u v uM uN uN' uN'' uE uF

variable {R : Type u} {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
  [AddCommGroup N''] [Module R N''] {n : ℕ}

variable {K : Type v} {E : Type uE} {F: Type uF} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

open BigOperators

namespace ExteriorPower

/-! Finiteness of the exterior power.-/

/-- The `n`th exterior power of a finite module is a finite module.-/
def Finite [Module.Finite R M]: Module.Finite R ((Λ[R]^n) M) :=
  Module.Finite.mk ((Submodule.fg_top _).mpr (Submodule.FG.pow (by
  rw [LinearMap.range_eq_map]; exact Submodule.FG.map _  (Module.finite_def.mp inferInstance)) _ ))

variable (R n)

/-! Generators of exterior powers.-/

open Finset in
/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`Λ[R]^n M`. Here we work in the exterior algebra.-/
lemma span_top_of_span_top {I : Type*} [LinearOrder I] {v : I → M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = (Λ[R]^n) M := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun _ ↦ by simp only [ιMulti_family_coe, Submodule.coeSubtype, Function.comp_apply,
                                SetLike.mem_coe, SetLike.coe_mem]
  · change (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    obtain ⟨f, hf⟩ := Set.mem_pow.mp hu
    set g : Fin n → M := fun i => ExteriorAlgebra.ιInv (f i).1
    have hfg : ∀ (i : Fin n), (f i).1 = ExteriorAlgebra.ι R (g i) := by
      intro i
      obtain ⟨_, hv⟩ := LinearMap.mem_range.mp (let ⟨y, hy⟩ := ((Set.mem_image _ _ _).mp (f i).2);
        LinearMap.mem_range.mpr ⟨y, hy.2⟩)
      simp only
      rw [← hv, ExteriorAlgebra.ι_inj]
      erw [ExteriorAlgebra.ι_leftInverse]
    have heq : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ← hf]
      congr
      exact funext (fun i ↦ hfg i)
    rw [heq]
    have hg : ∀ (i : Fin n), ∃ (j : I), g i = v j := by
      intro i
      let ⟨x, hx⟩ := (Set.mem_image _ _ _).mp (f i).2
      let ⟨j, hj⟩ := Set.mem_range.mp hx.1
      rw [hfg i, ExteriorAlgebra.ι_inj] at hx
      exact ⟨j, by rw [hj, hx.2]⟩
    set α : Fin n → I := fun i => Classical.choose (hg i)
    set αprop := fun i => Classical.choose_spec (hg i)
    by_cases hinj : Function.Injective α
    · set h : Fin n → image α univ := fun i => ⟨α i, by simp only [mem_image, mem_univ, true_and,
        exists_apply_eq_apply]⟩
      have hbij : Function.Bijective h := by
        constructor
        · intro i j hij
          rw [Subtype.mk.injEq] at hij
          exact hinj hij
        · intro ⟨i, hi⟩
          rw [Finset.mem_image] at hi
          obtain ⟨a, ha⟩ := hi
          existsi a
          simp only [Subtype.mk.injEq]
          exact ha.2
      have hcard : (image α univ).card = n := by
        suffices h : Fintype.card (image α univ) = n
        · conv_rhs => rw [← h]
          simp only [mem_image, mem_univ, true_and, Fintype.card_coe]
        · rw [← Fintype.card_of_bijective hbij]
          simp only [Fintype.card_fin]
      set g' : Fin n → M := fun i => v (orderIsoOfFin _ hcard i)
      have hg' : ExteriorAlgebra.ιMulti R n g' ∈ Submodule.span R (Set.range
        (ExteriorAlgebra.ιMulti_family R n v)) := by
        apply Submodule.subset_span
        rw [Set.mem_range]
        existsi ⟨_, hcard⟩
        unfold ExteriorAlgebra.ιMulti_family
        simp only [coe_orderIsoOfFin_apply]
      set σ : Equiv.Perm (Fin n) := (Equiv.ofBijective h hbij).trans
        (orderIsoOfFin _ hcard).toEquiv.symm
      have hgg' : g = g' ∘ σ := by
        ext i
        rw [Function.comp_apply, Equiv.trans_apply]
        change g i = v (orderIsoOfFin _ hcard _)
        erw [Equiv.apply_symm_apply (orderIsoOfFin _ hcard).toEquiv]
        simp only [Equiv.ofBijective_apply]
        exact αprop i
      rw [hgg', AlternatingMap.map_perm]
      exact Submodule.smul_mem _ _ hg'
    · change ¬(∀ (a b : Fin n), _) at hinj
      push_neg at hinj
      obtain ⟨i, j, hij1, hij2⟩ := hinj
      have heq : g = Function.update g i (g j) := by
        ext k
        by_cases hk : k = i
        · rw [Function.update_apply]
          simp only [hk, ite_true]
          change g i = g j
          rw [αprop i, αprop j]
          change v (α i) = v (α j)
          rw [hij1]
        · simp only [ne_eq, hk, not_false_eq_true, Function.update_noteq]
      rw [heq, AlternatingMap.map_update_self _ _ hij2]
      simp only [SetLike.mem_coe, Submodule.zero_mem]

/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`Λ[R]^n M`. This is a variant of `ExteriorPower.span_top_of_span_top` where we
work in the exterior power and not the exterior algebra.-/
lemma span_top_of_span_top' {I : Type*} [LinearOrder I]
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R  (Set.range (ιMulti_family R n v)) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨u, hu⟩ _
  rw [← span_top_of_span_top R n hv, ιMulti_family_coe,
    Set.range_comp, ← Submodule.map_span, Submodule.mem_map] at hu
  obtain ⟨w, hw, huw⟩ := hu
  have heq : ⟨u, hu⟩ = w := by rw [← SetCoe.ext_iff]; simp only [Submodule.coeSubtype] at huw ⊢
                               exact (Eq.symm huw)
  rw [heq]
  exact hw

/-- If `v` is a family of vectors of `M` indexed by a linearly ordered type, then the span of the
range of `ExteriorPower.ιMult_family R n v`, i.e. of the family of `n`-fold exterior products
of elements of `v`, is the image of the map of exterior powers induced by the inclusion of
the span of `v` into `M`.-/
lemma span_of_span {I : Type*} [LinearOrder I] (v : I → M) :
LinearMap.range (map n (Submodule.subtype (Submodule.span R (Set.range v)))) =
    Submodule.span R (Set.range (ιMulti_family R n v)) := by
  conv_lhs => rw [LinearMap.range_eq_map]
  rw [← (span_top_of_span_top' (I := I) (R := R) (v := fun i =>
    ⟨v i, by apply Submodule.subset_span; simp only [Set.mem_range, exists_apply_eq_apply]⟩)),
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

/-! We construct a basis of `Λ[R]^n M` from a basis of `M`.-/

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `ExteriorPower.linearFormOfFamily` construction to the fanily of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`).-/
noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) : (Λ[R]^n) M →ₗ[R] R :=
  linearFormOfFamily R n (fun i => b.coord (Finset.orderIsoOfFin s hs i))

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
of cardinality `n`. If we apply the linear form on `Λ[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`.-/
lemma linearFormOfBasis_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨s, hs⟩) = 1 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  have hzero : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ Finset.univ → ¬σ ∈ ({Equiv.refl (Fin n)} :
    Finset (Equiv.Perm (Fin n))) → TensorPower.linearFormOfFamily R n
    (fun i => b.coord (Finset.orderIsoOfFin s hs i)) (Equiv.Perm.sign σ • ⨂ₜ[R] (i : Fin n),
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
  by_contra habs
  push_neg at habs
  apply hst
  apply Finset.eq_of_subset_of_card_le
  · intro a has
    set b := Finset.orderIsoOfFin t ht (σ ((Finset.orderIsoOfFin s hs).symm ⟨a, has⟩))
    have heq : a = b.1 := by
      rw [← habs]
      simp only [OrderIso.apply_symm_apply]
    rw [heq]
    exact b.2
  · rw [hs, ht]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `Λ[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`.-/
lemma linearFormOfBasis_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨t, ht⟩) = 0 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  erw [zsmul_eq_smul_cast R]
  apply smul_eq_zero_of_right
  obtain ⟨i, hi⟩ := linearFormOfBasis_apply_nondiag_aux n hs ht hst σ
  apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
  rw [Basis.coord_apply, Basis.repr_self_apply]
  simp only [Finset.coe_orderIsoOfFin_apply, ne_eq] at hi
  simp only [Finset.coe_orderIsoOfFin_apply, Ne.symm hi, ite_false]

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`ExteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`.-/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  linearIndependent_of_dualFamily _ (fun s => linearFormOfBasis R n b s.2)
  (fun ⟨_, _⟩ ⟨_, _⟩ hst ↦
  by simp only [ne_eq, Subtype.mk.injEq] at hst; simp only [Function.comp_apply]
     exact linearFormOfBasis_apply_nondiag _ _ _ _ _ hst)
  (fun ⟨_, _⟩ ↦ by simp only [Function.comp_apply]; apply linearFormOfBasis_apply_diag)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`..-/
noncomputable def BasisOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R ((Λ[R]^n) M) :=
  Basis.mk (v := ιMulti_family R n b) (ιMulti_family_linearIndependent_ofBasis _ _ _)
  (by rw [span_top_of_span_top']; rw [Basis.span_eq])

@[simp]
lemma BasisOfBasis_coe {I : Type*} [LinearOrder I] (b : Basis I R M) :
    FunLike.coe (BasisOfBasis R n b) = ιMulti_family R n b := Basis.coe_mk _ _

@[simp]
lemma BasisOfBasis_apply {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    BasisOfBasis R n b ⟨s, hs⟩ = ιMulti_family R n b ⟨s, hs⟩ := by rw [BasisOfBasis_coe]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `ExteriorPower.linearFormOfBasis`.-/
lemma BasisOfBasis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    Basis.coord (BasisOfBasis R n b) ⟨s, hs⟩ = linearFormOfBasis R n b hs := by
  apply LinearMap.ext_on (span_top_of_span_top' R n (Basis.span_eq b))
  intro x hx
  obtain ⟨⟨t, ht⟩, htx⟩ := Set.mem_range.mp hx
  rw [← htx]
  conv_lhs => rw [← BasisOfBasis_apply]
  by_cases heq : s = t
  · have heq' : (⟨s, hs⟩ : {s : Finset I // Finset.card s = n}) = ⟨t, ht⟩ := by
      simp only [Subtype.mk.injEq]; exact heq
    simp only [← heq', linearFormOfBasis_apply_diag, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same]
  · simp only [linearFormOfBasis_apply_nondiag R n b hs ht heq, Basis.coord_apply,
      Basis.repr_self_apply, Subtype.mk.injEq, Ne.symm heq, ite_false]

/-! Freeness and dimension of `Λ[R]^n M.-/

/-- If `M` is a free module, then so is its `n`th exterior power.-/
lemma FreeOfFree (hfree : Module.Free R M) : Module.Free R ((Λ[R]^n) M) :=
  let ⟨I, b⟩ := (Classical.choice hfree.exists_basis)
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  Module.Free.of_basis (BasisOfBasis R n b)

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`.-/
lemma FinrankOfFiniteFree (hfree : Module.Free R M) [Module.Finite R M] :
    FiniteDimensional.finrank R ((Λ[R]^n) M) =
    Nat.choose (FiniteDimensional.finrank R M) n :=
  letI := WellFounded.wellOrderExtension (emptyWf (α := hfree.ChooseBasisIndex)).wf
  let B :=  BasisOfBasis R n (hfree.chooseBasis)
  by rw [FiniteDimensional.finrank_eq_card_basis hfree.chooseBasis,
    FiniteDimensional.finrank_eq_card_basis B, Fintype.card_finset_len]

/-! Results that only hold over a field.-/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent.-/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  set W := Submodule.span K (Set.range v)
  set v' : I → W := fun i => ⟨v i, by apply Submodule.subset_span; simp only [Set.mem_range,
    exists_apply_eq_apply]⟩
  have h : v = (W.subtype) ∘ v' :=
    funext (fun _ ↦ by simp only [Submodule.coeSubtype, Function.comp_apply])
  rw [h, ← map_ιMulti_family]
  refine LinearIndependent.map' ?_ (map n W.subtype)
    (LinearMap.ker_eq_bot.mpr (map_injective_field n (Submodule.ker_subtype _)))
  have hv'span : ⊤ ≤ Submodule.span K (Set.range v') := by
    simp only [top_le_iff]
    ext x
    simp only [Submodule.mem_top, iff_true, ← Submodule.apply_mem_span_image_iff_mem_span
      (Submodule.injective_subtype W), ← Set.range_comp, ← h]
    simp only [Submodule.coeSubtype, SetLike.coe_mem]
  have heq : ιMulti_family K n v' = BasisOfBasis K n (Basis.mk (LinearIndependent.of_comp
    (W.subtype) (by rw [← h]; exact hv)) hv'span) := by simp only [BasisOfBasis_coe, Basis.coe_mk]
  rw [heq]
  apply Basis.linearIndependent

lemma nonemptyOfNonempty {I : Type*} [LinearOrder I]
    (hne : Nonempty {v : I → E // LinearIndependent K v}) :
    Nonempty {v : {s : Finset I // Finset.card s = n} →
    (Λ[K]^n) E // LinearIndependent K v} :=
  let v := Classical.choice hne
  Nonempty.intro ⟨ιMulti_family K n v, ιMulti_family_linearIndependent_field n v.2⟩

end ExteriorPower
