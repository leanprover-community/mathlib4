/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The good products span

Most of the argument is developing an API for `π C (· ∈ s)` when `s : Finset I`; then the image
of `C` is finite with the discrete topology. In this case, there is a direct argument that the good
products span. The general result is deduced from this.

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main theorems

* `GoodProducts.spanFin` : The good products span the locally constant functions on `π C (· ∈ s)`
  if `s` is finite.
* `GoodProducts.span` : The good products span `LocallyConstant C ℤ` for every closed subset `C`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I]

section Fin

variable (s : Finset I)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (· ∈ s)`. -/
noncomputable
def πJ : LocallyConstant (π C (· ∈ s)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨_, (continuous_projRestrict C (· ∈ s))⟩

theorem eval_eq_πJ (l : Products I) (hl : l.isGood (π C (· ∈ s))) :
    l.eval C = πJ C s (l.eval (π C (· ∈ s))) := by
  ext f
  simp only [πJ, LocallyConstant.comapₗ, LinearMap.coe_mk, AddHom.coe_mk,
    LocallyConstant.coe_comap, Function.comp_apply]
  exact (congr_fun (Products.evalFacProp C (· ∈ s) (Products.prop_of_isGood C (· ∈ s) hl)) _).symm

/-- `π C (· ∈ s)` is finite for a finite set `s`. -/
noncomputable
instance : Fintype (π C (· ∈ s)) := by
  let f : π C (· ∈ s) → (s → Bool) := fun x j ↦ x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i ∈ s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]

open scoped Classical in
/-- The Kronecker delta as a locally constant map from `π C (· ∈ s)` to `ℤ`. -/
noncomputable
def spanFinBasis (x : π C (· ∈ s)) : LocallyConstant (π C (· ∈ s)) ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· ∈ s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _

open scoped Classical in
theorem spanFinBasis.span : ⊤ ≤ Submodule.span ℤ (Set.range (spanFinBasis C s)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ ℤ x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

/--
A certain explicit list of locally constant maps. The theorem `factors_prod_eq_basis` shows that the
product of the elements in this list is the delta function `spanFinBasis C s x`.
-/
def factors (x : π C (· ∈ s)) : List (LocallyConstant (π C (· ∈ s)) ℤ) :=
  List.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i else (1 - (e (π C (· ∈ s)) i)))
    (s.sort (· ≥ ·))

theorem list_prod_apply {I} (C : Set (I → Bool)) (x : C) (l : List (LocallyConstant C ℤ)) :
    l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l, LocallyConstant.evalMonoidHom_apply]

theorem factors_prod_eq_basis_of_eq {x y : (π C fun x ↦ x ∈ s)} (h : y = x) :
    (factors C s x).prod y = 1 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

theorem e_mem_of_eq_true {x : (π C (· ∈ s))} {a : I} (hx : x.val a = true) :
    e (π C (· ∈ s)) a ∈ factors C s x := by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)

theorem one_sub_e_mem_of_false {x y : (π C (· ∈ s))} {a : I} (ha : y.val a = true)
    (hx : x.val a = false) : 1 - e (π C (· ∈ s)) a ∈ factors C s x := by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)

theorem factors_prod_eq_basis_of_ne {x y : (π C (· ∈ s))} (h : y ≠ x) :
    (factors C s x).prod y = 0 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : ∃ a, y.val a ≠ x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· ∈ s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e, LocallyConstant.evalMonoidHom_apply, LocallyConstant.sub_apply,
      LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk, if_pos ha, sub_self]
  · refine ⟨e (π C (· ∈ s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply, e, LocallyConstant.coe_mk, if_neg ha]

/-- If `s` is finite, the product of the elements of the list `factors C s x`
is the delta function at `x`. -/
theorem factors_prod_eq_basis (x : π C (· ∈ s)) :
    (factors C s x).prod = spanFinBasis C s x := by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

theorem GoodProducts.finsuppSum_mem_span_eval {a : I} {as : List I}
    (ha : List.IsChain (· > ·) (a :: as)) {c : Products I →₀ ℤ}
    (hc : (c.support : Set (Products I)) ⊆ {m | m.val ≤ as}) :
    (Finsupp.sum c fun a_1 b ↦ e (π C (· ∈ s)) a * b • Products.eval (π C (· ∈ s)) a_1) ∈
      Submodule.span ℤ (Products.eval (π C (· ∈ s)) '' {m | m.val ≤ a :: as}) := by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val ≤ as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

/-- If `s` is a finite subset of `I`, then the good products span. -/
theorem GoodProducts.spanFin [WellFoundedLT I] :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· ∈ s)))) := by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (· ≥ ·)
  dsimp [factors]
  suffices l.IsChain (· > ·) → (l.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i
      else (1 - (e (π C (· ∈ s)) i)))).prod ∈
      Submodule.span ℤ ((Products.eval (π C (· ∈ s))) '' {m | m.val ≤ l}) from
    Submodule.span_mono (Set.image_subset_range _ _) (this (Finset.sort_sorted_gt _).isChain)
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.isChain_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons]
    intro ha
    specialize ih (by rw [List.isChain_cons] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g ↦ map_finsuppSum (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · noncomm_ring
      -- we use `noncomm_ring` even though this is a commutative ring, because we want a weaker
      -- normalization which preserves multiplication order (i.e. doesn't use commutativity rules)
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_setOf_eq]
        have hmas : m.val ≤ as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.isChain_cons_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)
      · apply Submodule.smul_mem
        exact finsuppSum_mem_span_eval _ _ ha hc

end Fin

theorem fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant C ℤ) : ∃ (s : Finset I)
    (g : LocallyConstant (π C (· ∈ s)) ℤ), f = g.comap ⟨(ProjRestrict C (· ∈ s)),
      continuous_projRestrict _ _⟩ := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) ℤ
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

/-- The good products span all of `LocallyConstant C ℤ` if `C` is closed. -/
theorem GoodProducts.span [WellFoundedLT I] (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : ∃ K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
  refine Submodule.span_mono ?_ <| Submodule.apply_mem_span_image_of_mem_span (πJ C K) <|
    spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

end Profinite.NobelingProof
