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

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  sorry

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
    rw [SetLike.mem_coe, ιMulti_family_coe, Submodule.coe_subtype, Function.comp_apply]
    exact Submodule.coe_mem _
  · unfold ExteriorAlgebra.exteriorPower
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    have ⟨f, hf⟩ := Set.mem_pow.mp hu
    let g (i : Fin n) : M := ExteriorAlgebra.ιInv (f i).1
    have hfg (i : Fin n) : (f i).1 = ExteriorAlgebra.ι R (g i) := by
      obtain ⟨x, -, hx⟩ := (Set.mem_image _ _ _).mp (f i).2
      simp only [g]
      rw [← hx, ExteriorAlgebra.ι_leftInverse]
    obtain rfl : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ← hf]
      exact congrArg (List.prod ∘ List.ofFn) (funext hfg)
    have hg (i : Fin n) : ∃ j : I, g i = v j := by
      have ⟨x, h, hx⟩ := (Set.mem_image _ _ _).mp (f i).2
      obtain ⟨j, rfl⟩ := Set.mem_range.mp h
      exact ⟨j, ExteriorAlgebra.ι_leftInverse.injective <| hfg i ▸ hx.symm⟩
    choose α hα using hg
    by_cases hinj : Function.Injective α
    · let h (i : Fin n) : image α univ :=
        ⟨α i, mem_image_univ_iff_mem_range.mpr <| Set.mem_range_self _⟩
      have hbij : Function.Bijective h :=
        ⟨fun i j hij ↦ hinj (Subtype.mk_eq_mk.mp hij),
          fun ⟨i, hi⟩ ↦
            have ⟨a, _, ha⟩ := Finset.mem_image.mp hi
            ⟨a, (Subtype.mk.injEq _ _ _ _).mpr ha⟩⟩
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
        unfold g'
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
        · rw [hk, Function.update_self, hα i, hα j, hij1]
        · rw [Function.update_of_ne hk]
      rw [heq, AlternatingMap.map_update_self _ _ hij2, SetLike.mem_coe]
      exact Submodule.zero_mem _

/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`⋀[R]^n M`. This is a variant of `exteriorPower.span_top_of_span_top` where we
work in the exterior power and not the exterior algebra. -/
lemma span_top_of_span_top' {I : Type*} [LinearOrder I]
    {v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ιMulti_family (R := R) (n := n) v)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨u, hu⟩ -
  have ⟨w, hw, huw⟩ : ∃ x ∈ Submodule.span R (Set.range (ιMulti_family (R := R) (n := n) v)),
    ↑x = u := by
    rw [← Submodule.coe_subtype, ← Submodule.mem_map, Submodule.map_span, ← Set.range_comp,
      ← ιMulti_family_coe, span_top_of_span_top R n hv]
    exact hu
  have heq : w = ⟨u, hu⟩ := SetCoe.ext huw
  rw [← heq]
  exact hw

/-- If `v` is a family of vectors of `M` indexed by a linearly ordered type, then the span of the
range of `exteriorPower.ιMulti_family R n v`, i.e., of the family of `n`-fold exterior products
of elements of `v`, is the image of the map of exterior powers induced by the inclusion of
the span of `v` into `M`. -/
lemma span_of_span {I : Type*} [LinearOrder I] (v : I → M) :
    LinearMap.range (map n (Submodule.subtype (Submodule.span R (Set.range v)))) =
    Submodule.span R (Set.range (ιMulti_family (R := R) (n := n) v)) := by
  have ⟨f, hf⟩ : ∃ f : I → Submodule.span R (Set.range v), Submodule.subtype _ ∘ f = v :=
    ⟨fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩, rfl⟩
  have htop : Submodule.span R (Set.range f) = ⊤ := by
    apply SetLike.coe_injective
    apply Set.image_injective.mpr (Submodule.span R (Set.range v)).injective_subtype
    rw [← Submodule.map_coe, ← Submodule.span_image, ← Set.range_comp, hf,
      ← Submodule.map_coe, ← LinearMap.range_eq_map, Submodule.range_subtype]
  rw [LinearMap.range_eq_map (M := ⋀[R]^n _), ← span_top_of_span_top' _ _ htop,
    Submodule.map_span, ← Set.range_comp, map_ιMulti_family, hf]

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearFormOfFamily` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) : ⋀[R]^n M →ₗ[R] R :=
  sorry

@[simp]
lemma linearFormOfBasis_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
    linearFormOfBasis R n b hs (ιMulti R n v) = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
    ∏ i, b.coord (Finset.orderIsoOfFin s hs i) (v (σ i)) := by
  sorry

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
lemma linearFormOfBasis_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    linearFormOfBasis R n b hs (ιMulti_family (R := R) (n := n) b ⟨s, hs⟩) = 1 := by
  sorry

lemma linearFormOfBasis_apply_nondiag_aux {I : Type*} [LinearOrder I] {s t : Finset I}
    (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) :
    ∃ (i : Fin n), (Finset.orderIsoOfFin s hs i).1 ≠ (Finset.orderIsoOfFin t ht (σ i)).1 := by
  by_contra! habs
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
    linearFormOfBasis R n b hs (ιMulti_family (R := R) (n := n) b ⟨t, ht⟩) = 0 := by
  simp only [ιMulti_family]
  rw [linearFormOfBasis_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  have ⟨i, hi⟩ := linearFormOfBasis_apply_nondiag_aux n hs ht hst σ
  apply smul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [Basis.coord_apply, Basis.repr_self_apply, if_neg (ne_comm.mp hi)]

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family (R := R) (n := n) b) :=
  sorry

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
noncomputable def _root_.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| span_top_of_span_top' R n (Basis.span_eq b))

@[simp]
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (Basis.exteriorPower R n b) = ιMulti_family b :=
  Basis.coe_mk _ _

@[simp]
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    Basis.exteriorPower R n b ⟨s, hs⟩ = ιMulti_family b ⟨s, hs⟩ := by
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
  rw [← htx, Basis.coord_apply]
  by_cases heq : s = t
  · rw [Subtype.mk_eq_mk.mpr heq.symm, linearFormOfBasis_apply_diag, ← basis_apply,
      Basis.repr_self, Finsupp.single_eq_same]
  · rw [linearFormOfBasis_apply_nondiag R n b hs ht heq, ← basis_apply,
      Basis.repr_self, Finsupp.single_eq_of_ne (by rwa [ne_comm, ne_eq, Subtype.mk_eq_mk])]

/-! ### Freeness and dimension of `⋀[R]^n M. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
instance instFree [hfree : Module.Free R M] : Module.Free R (⋀[R]^n M) :=
  sorry

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [hfree : Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) =
    Nat.choose (Module.finrank R M) n := by
  sorry

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family (R := K) (n := n) v) := by
  sorry

instance instNonempty {I : Type*} [LinearOrder I] [Nonempty {v : I → E // LinearIndependent K v}] :
    Nonempty {v : {s : Finset I // Finset.card s = n} → (⋀[K]^n) E // LinearIndependent K v} :=
  sorry

end exteriorPower
