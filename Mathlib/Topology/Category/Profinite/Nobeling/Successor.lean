/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The successor case in the induction for Nöbeling's theorem

Here we assume that `o` is an ordinal such that `contained C (o+1)` and `o < I`. The element in `I`
corresponding to `o` is called `term I ho`, but in this informal docstring we refer to it simply as
`o`.

This section follows the proof in [scholze2019condensed] quite closely. A translation of the
notation there is as follows:

```
[scholze2019condensed]                  | This file
`S₀`                                    |`C0`
`S₁`                                    |`C1`
`\overline{S}`                          |`π C (ord I · < o)
`\overline{S}'`                         |`C'`
The left map in the exact sequence      |`πs`
The right map in the exact sequence     |`Linear_CC'`
```

When comparing the proof of the successor case in Theorem 5.4 in [scholze2019condensed] with this
proof, one should read the phrase "is a basis" as "is linearly independent". Also, the short exact
sequence in [scholze2019condensed] is only proved to be left exact here (indeed, that is enough
since we are only proving linear independence).

This section is split into two sections. The first one, `ExactSequence` defines the left exact
sequence mentioned in the previous paragraph (see `succ_mono` and `succ_exact`). It corresponds to
the penultimate paragraph of the proof in [scholze2019condensed]. The second one, `GoodProducts`
corresponds to the last paragraph in the proof in [scholze2019condensed].

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main definitions

The main definitions in the section `ExactSequence` are all just notation explained in the table
above.

The main definitions in the section `GoodProducts` are as follows:

* `MaxProducts`: the set of good products that contain the ordinal `o` (since we have
  `contained C (o+1)`, these all start with `o`).

* `GoodProducts.sum_equiv`: the equivalence between `GoodProducts C` and the disjoint union of
  `MaxProducts C` and `GoodProducts (π C (ord I · < o))`.

## Main results

* The main results in the section `ExactSequence` are `succ_mono` and `succ_exact` which together
  say that the sequence given by `πs` and `Linear_CC'` is left exact:
  ```
                                              f                        g
  0 --→ LocallyConstant (π C (ord I · < o)) ℤ --→ LocallyConstant C ℤ --→ LocallyConstant C' ℤ
  ```
  where `f` is `πs` and `g` is `Linear_CC'`.

The main results in the section `GoodProducts` are as follows:

* `Products.max_eq_eval` says that the linear map on the right in the exact sequence, i.e.
  `Linear_CC'`, takes the evaluation of a term of `MaxProducts` to the evaluation of the
  corresponding list with the leading `o` removed.

* `GoodProducts.maxTail_isGood` says that removing the leading `o` from a term of `MaxProducts C`
  yields a list which `isGood` with respect to `C'`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

open CategoryTheory

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I] [WellFoundedLT I]
  {o : Ordinal} (hC : IsClosed C) (hsC : contained C (Order.succ o))
  (ho : o < Ordinal.type (· < · : I → I → Prop))

section ExactSequence

/-- The subset of `C` consisting of those elements whose `o`-th entry is `false`. -/
def C0 := C ∩ {f | f (term I ho) = false}

/-- The subset of `C` consisting of those elements whose `o`-th entry is `true`. -/
def C1 := C ∩ {f | f (term I ho) = true}

include hC in
theorem isClosed_C0 : IsClosed (C0 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in
theorem isClosed_C1 : IsClosed (C1 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)

theorem contained_C1 : contained (π (C1 C ho) (ord I · < o)) o :=
  contained_proj _ _

theorem union_C0C1_eq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

/--
The intersection of `C0` and the projection of `C1`. We will apply the inductive hypothesis to
this set.
-/
def C' := C0 C ho ∩ π (C1 C ho) (ord I · < o)

include hC in
theorem isClosed_C' : IsClosed (C' C ho) :=
  IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))

theorem contained_C' : contained (C' C ho) o := fun f hf i hi ↦ contained_C1 C ho f hf.2 i hi

variable (o)

/-- Swapping the `o`-th coordinate to `true`. -/
noncomputable
def SwapTrue : (I → Bool) → I → Bool :=
  fun f i ↦ if ord I i = o then true else f i

theorem continuous_swapTrue : Continuous (SwapTrue o : (I → Bool) → I → Bool) := by
  dsimp +unfoldPartialApp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

variable {o}

include hsC in
theorem swapTrue_mem_C1 (f : π (C1 C ho) (ord I · < o)) :
    SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert hg
  dsimp +unfoldPartialApp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
    contrapose! hsC
    exact ⟨hsC, Order.succ_le_of_lt (h'.lt_of_ne' h)⟩

/-- The first way to map `C'` into `C`. -/
def CC'₀ : C' C ho → C := fun g ↦ ⟨g.val,g.prop.1.1⟩

/-- The second way to map `C'` into `C`. -/
noncomputable
def CC'₁ : C' C ho → C :=
  fun g ↦ ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩

theorem continuous_CC'₀ : Continuous (CC'₀ C ho) := Continuous.subtype_mk continuous_subtype_val _

theorem continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
  Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

/-- The `ℤ`-linear map induced by precomposing with `CC'₀` -/
noncomputable
def Linear_CC'₀ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(CC'₀ C ho), (continuous_CC'₀ C ho)⟩

/-- The `ℤ`-linear map induced by precomposing with `CC'₁` -/
noncomputable
def Linear_CC'₁ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(CC'₁ C hsC ho), (continuous_CC'₁ C hsC ho)⟩

/-- The difference between `Linear_CC'₁` and `Linear_CC'₀`. -/
noncomputable
def Linear_CC' : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

theorem CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((πs C o) y) = 0 := by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ ↦ rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).elim

include hsC in
theorem C0_projOrd {x : I → Bool} (hx : x ∈ C0 C ho) : Proj (ord I · < o) x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff, not_lt]
  intro hi
  rcases hi.lt_or_eq with hi | hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [eq_comm, ord_term ho] at hi
    rw [← hx.2, hi]

include hsC in
theorem C1_projOrd {x : I → Bool} (hx : x ∈ C1 C ho) : SwapTrue o (Proj (ord I · < o) x) = x := by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2, hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC h').symm

include hC in
open scoped Classical in
theorem CC_exact {f : LocallyConstant C ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, πs C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj] at hf
  let C₀C : C0 C ho → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C ho) (ord I · < o) → C :=
    fun x ↦ ⟨SwapTrue o x.val, (swapTrue_mem_C1 C hsC ho x).1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk
    ((continuous_swapTrue o).comp continuous_subtype_val) _
  refine ⟨LocallyConstant.piecewise' ?_ (isClosed_C0 C hC ho)
      (isClosed_proj _ o (isClosed_C1 C hC ho)) (f.comap ⟨C₀C, h₀⟩) (f.comap ⟨C₁C, h₁⟩) ?_, ?_⟩
  · rintro _ ⟨y, hyC, rfl⟩
    simp only [Set.mem_union]
    rw [← union_C0C1_eq C ho] at hyC
    refine hyC.imp (fun hyC ↦ ?_) (fun hyC ↦ ⟨y, hyC, rfl⟩)
    rwa [C0_projOrd C hsC ho hyC]
  · intro x hx
    simpa only [h₀, h₁, LocallyConstant.coe_comap] using (congrFun hf ⟨x, hx⟩).symm
  · ext ⟨x, hx⟩
    rw [← union_C0C1_eq C ho] at hx
    rcases hx with hx₀ | hx₁
    · have hx₀' : ProjRestrict C (ord I · < o) ⟨x, hx⟩ = x := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using C0_projOrd C hsC ho hx₀
      simp only [C₀C, πs_apply_apply, hx₀', hx₀, LocallyConstant.piecewise'_apply_left,
        LocallyConstant.coe_comap, ContinuousMap.coe_mk, Function.comp_apply]
    · have hx₁' : (ProjRestrict C (ord I · < o) ⟨x, hx⟩).val ∈ π (C1 C ho) (ord I · < o) := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using ⟨x, hx₁, rfl⟩
      simp only [C₁C, πs_apply_apply, LocallyConstant.coe_comap,
        Function.comp_apply, hx₁', LocallyConstant.piecewise'_apply_right]
      congr
      simp only [ContinuousMap.coe_mk, Subtype.mk.injEq]
      exact C1_projOrd C hsC ho hx₁

variable (o) in
theorem succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in
theorem succ_exact :
    (ShortComplex.mk (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho))
    (by ext : 2; apply CC_comp_zero)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC ho

end ExactSequence

namespace GoodProducts

/--
The `GoodProducts` in `C` that contain `o` (they necessarily start with `o`, see
`GoodProducts.head!_eq_o_of_maxProducts`)
-/
def MaxProducts : Set (Products I) := {l | l.isGood C ∧ term I ho ∈ l.val}

include hsC in
theorem union_succ : GoodProducts C = GoodProducts (π C (ord I · < o)) ∪ MaxProducts C ho := by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hh : term I ho ∈ l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp only [Order.lt_succ_iff] at h'
      simp only at hh
      have hh' : ∀ a ∈ l.val, ord I a < o := by
        intro a ha
        refine (h' a ha).lt_of_ne ?_
        rw [ne_eq, ord_term ho a]
        rintro rfl
        contradiction
      rwa [Products.eval_πs_image C hh', ← Products.eval_πs C hh',
        Submodule.apply_mem_span_image_iff_mem_span (injective_πs _ _)]
  · refine h.elim (fun hh ↦ ?_) And.left
    have := Products.isGood_mono C (Order.lt_succ o).le hh
    rwa [contained_eq_proj C (Order.succ o) hsC]

/-- The inclusion map from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `Products I`. -/
def sum_to : (GoodProducts (π C (ord I · < o))) ⊕ (MaxProducts C ho) → Products I :=
  Sum.elim Subtype.val Subtype.val

theorem injective_sum_to : Function.Injective (sum_to C ho) := by
  refine Function.Injective.sumElim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩ ↦ (fun (hab : a = b) ↦ ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'

theorem sum_to_range :
    Set.range (sum_to C ho) = GoodProducts (π C (ord I · < o)) ∪ MaxProducts C ho := by
  have h : Set.range (sum_to C ho) = _ ∪ _ := Set.Sum.elim_range _ _; rw [h]; congr <;> ext l
  · exact ⟨fun ⟨m,hm⟩ ↦ by rw [← hm]; exact m.prop, fun hl ↦ ⟨⟨l,hl⟩, rfl⟩⟩
  · exact ⟨fun ⟨m,hm⟩ ↦ by rw [← hm]; exact m.prop, fun hl ↦ ⟨⟨l,hl⟩, rfl⟩⟩

/-- The equivalence from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `GoodProducts C`. -/
noncomputable
def sum_equiv (hsC : contained C (Order.succ o)) (ho : o < Ordinal.type (· < · : I → I → Prop)) :
    GoodProducts (π C (ord I · < o)) ⊕ (MaxProducts C ho) ≃ GoodProducts C :=
  calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
       _ ≃ _ := Equiv.setCongr <| by rw [sum_to_range C ho, union_succ C hsC ho]

theorem sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun =
    (Sum.elim (fun (l : GoodProducts (π C (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  ext ⟨_, _⟩ <;> [rfl; rfl]

/-- Let

`N := LocallyConstant (π C (ord I · < o)) ℤ`

`M := LocallyConstant C ℤ`

`P := LocallyConstant (C' C ho) ℤ`

`ι := GoodProducts (π C (ord I · < o))`

`ι' := GoodProducts (C' C ho')`

`v : ι → N := GoodProducts.eval (π C (ord I · < o))`

Then `SumEval C ho` is the map `u` in the diagram below. It is linearly independent if and only if
`GoodProducts.eval C` is, see `linearIndependent_iff_sum`. The top row is the exact sequence given
by `succ_exact` and `succ_mono`. The left square commutes by `GoodProducts.square_commutes`.
```
0 --→ N --→ M --→  P
      ↑     ↑      ↑
     v|    u|      |
      ι → ι ⊕ ι' ← ι'
```
-/
def SumEval : GoodProducts (π C (ord I · < o)) ⊕ MaxProducts C ho →
    LocallyConstant C ℤ :=
  Sum.elim (fun l ↦ l.1.eval C) (fun l ↦ l.1.eval C)

include hsC in
theorem linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (SumEval C ho) := by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho), SumEval,
    ← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

include hsC in
theorem span_sum : Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (π C (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho, Equiv.toFun_as_coe,
    EquivLike.range_comp (e := sum_equiv C hsC ho)]


theorem square_commutes : SumEval C ho ∘ Sum.inl =
    ModuleCat.ofHom (πs C o) ∘ eval (π C (ord I · < o)) := by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood _ _ l.prop)]
  simp [eval]

end GoodProducts

theorem swapTrue_eq_true (x : I → Bool) : SwapTrue o x (term I ho) = true := by
  simp only [SwapTrue, ord_term_aux, ite_true]

theorem mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

/-- `List.tail` as a `Products`. -/
def Products.Tail (l : Products I) : Products I :=
  ⟨l.val.tail, List.IsChain.tail l.prop⟩

theorem Products.max_eq_o_cons_tail [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  simp [Tail]

theorem Products.max_eq_o_cons_tail' [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) (hlc : List.IsChain (· > ·) (term I ho :: l.Tail.val)) :
    l = ⟨term I ho :: l.Tail.val, hlc⟩ := by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh, Subtype.coe_eta]

include hsC in
theorem GoodProducts.head!_eq_o_of_maxProducts [Inhabited I] (l : ↑(MaxProducts C ho)) :
    l.val.val.head! = term I ho := by
  rw [eq_comm, ← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (term I ho) ≤ ord I l.val.val.head! := by
    simp only [ord, Ordinal.typein_le_typein, not_lt]
    exact Products.rel_head!_of_mem hm
  rwa [ord_term_aux] at h

include hsC in
theorem GoodProducts.max_eq_o_cons_tail (l : MaxProducts C ho) :
    l.val.val = (term I ho) :: l.val.Tail.val :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

theorem Products.evalCons {I} [LinearOrder I] {C : Set (I → Bool)} {l : List I} {a : I}
    (hla : (a::l).IsChain (· > ·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.IsChain.sublist hla (List.tail_sublist (a::l))⟩ := by
  simp only [eval.eq_1, List.map, List.prod_cons]

theorem Products.max_eq_eval [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hlc : ((term I ho) :: l.Tail.val).IsChain (· > ·) := by
    rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc, Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.sub_apply,
    LocallyConstant.coe_comap, LocallyConstant.coe_mul, ContinuousMap.coe_mk, Function.comp_apply,
    Pi.mul_apply]
  rw [CC'₁, CC'₀, Products.eval_eq, Products.eval_eq, Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i) := by
    intro i hi
    simp only [SwapTrue, @eq_comm _ (x.val i), ite_eq_right_iff, ord_term ho]
    rintro rfl
    exact ((List.IsChain.rel_cons hlc hi).ne rfl).elim
  have H : (∀ i, i ∈ l.Tail.val → (x.val i = true)) =
      (∀ i, i ∈ l.Tail.val → (SwapTrue o x.val i = true)) := by
    apply forall_congr; intro i; apply forall_congr; intro hi; rw [hi' i hi]
  simp only [H]
  split_ifs with h₁ h₂ h₃ <;> try (dsimp [e])
  · rw [if_pos (swapTrue_eq_true _ _), if_neg]
    · rfl
    · simp [mem_C'_eq_false C ho x x.prop]
  · push_neg at h₂; obtain ⟨i, hi⟩ := h₂; exfalso; rw [hi' i hi.1] at hi; exact hi.2 (h₁ i hi.1)
  · push_neg at h₁; obtain ⟨i, hi⟩ := h₁; exfalso; rw [← hi' i hi.1] at hi; exact hi.2 (h₃ i hi.1)

namespace GoodProducts

theorem max_eq_eval (l : MaxProducts C ho) :
    Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho) :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

theorem max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) ↦ Products.eval C l.val) =
    (fun l ↦ l.val.Tail.eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

include hsC in
theorem isChain_cons_of_lt (l : MaxProducts C ho)
    (q : Products I) (hq : q < l.val.Tail) :
    List.IsChain (fun x x_1 ↦ x > x_1) (term I ho :: q.val) := by
  have : Inhabited I := ⟨term I ho⟩
  rw [List.isChain_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha ↦ lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.isChain_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_mem ha)) ?_
  by_cases hM : l.val.Tail.val = []
  · rw [Products.lt_iff_lex_lt, hM] at hq
    simp only [List.not_lex_nil] at hq
  · have := l.val.prop
    rw [max_eq_o_cons_tail C hsC ho l, List.isChain_iff_pairwise] at this
    exact List.rel_of_pairwise_cons this (List.head!_mem_self hM)

@[deprecated (since := "2025-09-24")] alias chain'_cons_of_lt := isChain_cons_of_lt

include hsC in
theorem good_lt_maxProducts (q : GoodProducts (π C (ord I · < o)))
    (l : MaxProducts C ho) : List.Lex (· < ·) q.val.val l.val.val := by
  have : Inhabited I := ⟨term I ho⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (· < ·)]
    simp only [term, Ordinal.typein_enum]
    exact Products.prop_of_isGood C _ q.prop q.val.val.head! (List.head!_mem_self h)

include hC hsC in
/--
Removing the leading `o` from a term of `MaxProducts C` yields a list which `isGood` with respect to
`C'`.
-/
theorem maxTail_isGood (l : MaxProducts C ho)
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    l.val.Tail.isGood (C' C ho) := by
  have : Inhabited I := ⟨term I ho⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination, ← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum
  -- Write the image of `l` under `Linear_CC'` as `Linear_CC'` applied to the linear combination
  -- above, with leading `term I ho`'s added to each term:
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
      (Finsupp.sum m fun i a ↦ a • ((term I ho :: i.1).map (e C)).prod) := by
    rw [← hmsum]
    simp only [map_finsuppSum]
    apply Finsupp.sum_congr
    intro q hq
    rw [LinearMap.map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < l.val.Tail := hmmem hq
    have : ∃ (p : Products I), p.val ≠ [] ∧ p.val.head! = term I ho ∧ q = p.Tail :=
      ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q hx''⟩,
        ⟨List.cons_ne_nil _ _, by simp only [List.head!_cons],
        by simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]⟩⟩
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1, List.map_cons, List.prod_cons]
  have hse := succ_exact C hC hsC ho
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hse
  dsimp [ModuleCat.ofHom] at hse
  -- Rewrite `this` using exact sequence manipulations to conclude that a term is in the range of
  -- the linear map `πs`:
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨(n : LocallyConstant (π C (ord I · < o)) ℤ), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n ∈ ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w,hc⟩ := hn'
  rw [← hc, map_finsuppSum] at hn
  apply l.prop.1
  rw [← hn]
  -- Now we just need to prove that a sum of two terms belongs to a span:
  apply Submodule.add_mem
  · apply Submodule.finsuppSum_mem
    intro q _
    rw [LinearMap.map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    dsimp only [eval]
    rw [Products.eval_πs C (Products.prop_of_isGood _ _ q.prop)]
    refine ⟨q.val, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    exact good_lt_maxProducts C hsC ho q l
  · apply Submodule.finsuppSum_mem
    intro q hq
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finsupp.mem_supported] at hmmem
    rw [← Finsupp.mem_support_iff] at hq
    refine ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q (hmmem hq)⟩, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    rw [max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.cons ((Products.lt_iff_lex_lt q l.val.Tail).mp (hmmem hq))

/-- Given `l : MaxProducts C ho`, its `Tail` is a `GoodProducts (C' C ho)`. -/
noncomputable
def MaxToGood
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    MaxProducts C ho → GoodProducts (C' C ho) :=
  fun l ↦ ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩

theorem maxToGood_injective
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    (MaxToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m, max_eq_o_cons_tail C hsC ho n, h]

include hC in
theorem linearIndependent_comp_of_eval
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    LinearIndependent ℤ (eval (C' C ho)) →
    LinearIndependent ℤ (ModuleCat.ofHom (Linear_CC' C hsC ho) ∘ SumEval C ho ∘ Sum.inr) := by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l ↦ Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end GoodProducts

end Profinite.NobelingProof
