/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Order.ListOnPartialOrderTypes
import Mathlib.Order.JordanHolder
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.SimpleModule
import Init.Data.List.Lemmas

/-!

# Composition Series of a module

Let `M` be an `R`-module and `s : CompositionSeries R M` and let `N` be an `R`-submodule of `M`.
This file shows that by removing duplicates in `s ⊓ N`, it forms a composition series for `N`.

## Implementation details

for some reason unknown to me, some lemmas and definitions need extremely large `maxHeartbeats`

-/

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]
variable (s : CompositionSeries (Submodule R M)) (N : Submodule R M)

namespace CompositionSeries

/-- if `x ≤ y` are headh `R`-submodule of `M`, we can mathematically form their quotient but type
theoretically more complicated, so introduce a definition to use a notation. -/
private def quot {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) : Type _ :=
  x ⧸ (Submodule.comap x.subtype y)
local infix:80 "⧸ₛ" => quot

/-- quotient factor of a composition series -/
def qf (i : Fin s.length) : Type _ :=
s i.succ ⧸ₛ s i.castSucc

instance (i : Fin s.length) : AddCommGroup (s.qf i) := by
  delta qf quot; infer_instance

instance (i : Fin s.length) : Module R (s.qf i) := by
  delta qf quot; infer_instance

lemma qf_def (i : Fin s.length) : s.qf i = s i.succ ⧸ₛ s i.castSucc := rfl

instance qf_isSimpleModule (i : Fin s.length) : IsSimpleModule R $ s.qf i := by
  delta qf quot
  rw [← covBy_iff_quot_is_simple (s.strictMono.monotone _)]
  · exact s.step i
  · change i.1 ≤ i.1 + 1
    linarith

/-- Given an `R`-submodule `N`, we can form a list of submodule of `N` by taking intersections with
a given composition series-/
def interList : List (Submodule R N) :=
  s.toList.map $ fun si => Submodule.comap N.subtype (N ⊓ si)

lemma interList_length : (s.interList N).length = s.length + 1 :=
by rw [interList, List.length_map, RelSeries.toList, List.length_ofFn]

lemma interList_get_eq_aux (i : ℕ) (hi : i < s.length + 1) :
    (s.interList N).get ⟨i, by rw [interList_length]; linarith⟩ =
    Submodule.comap N.subtype (N ⊓ s ⟨i, by linarith⟩) := by
  delta interList
  rw [List.get_map]
  congr 2
  exact List.get_ofFn _ _

private def interList_get (i : Fin s.length) : Submodule R N :=
  (s.interList N).get (i.castLE <| by rw [interList_length]; linarith)

private def interList_get_succ (i : Fin s.length) : Submodule R N :=
  (s.interList N).get (i.succ.castLE <| by rw [interList_length])

lemma interList_get_eq (i : Fin s.length) :
    s.interList_get N i =
    Submodule.comap N.subtype (N ⊓ s i.castSucc) :=
  s.interList_get_eq_aux N i.1 $ i.2.trans $ by linarith

lemma interList_get_succ_eq (i : Fin s.length) :
    s.interList_get_succ N i =
    Submodule.comap N.subtype (N ⊓ s i.succ) :=
  s.interList_get_eq_aux N (i.1 + 1) $ by linarith [i.2]

lemma interList_get_le_get_succ (i : Fin s.length) :
    s.interList_get N i ≤ s.interList_get_succ N i := by
  rw [interList_get_eq _ _ _, interList_get_succ_eq _ _ _]
  refine Submodule.comap_mono (le_inf inf_le_left (inf_le_right.trans $ s.strictMono.monotone ?_))
  change i.1 ≤ i.1 + 1
  linarith

/-- Given composition series `s`, the canonical map `s_{i + 1} ⊓ N` to `i`-th quotient factor of
  `s`-/
@[simps! apply]
def interList_get_succ_to_qf (i : Fin s.length) :
    s.interList_get_succ N i →ₗ[R] s.qf i :=
(Submodule.mkQ _).comp $ N.subtype.restrict $ λ _ h ↦ by
  rw [interList_get_succ_eq] at h
  exact h.2

lemma interList_get_succ_to_qf_ker (i : Fin s.length) :
    LinearMap.ker (s.interList_get_succ_to_qf N i) =
    Submodule.comap (s.interList_get_succ N i).subtype (s.interList_get N i) := by
  ext ⟨x, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    interList_get_succ_to_qf_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  change x.1 ∈ _ ↔ _
  rw [interList_get_eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf,
    iff_and_self]
  rintro -
  exact x.2

/-- quotient factor of intersection between a submodule and a composition series. -/
def interList_qf (i : Fin s.length) : Type _ :=
    s.interList_get_succ N i ⧸ₛ s.interList_get N i

instance {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) :
  AddCommGroup (x ⧸ₛ y) := by delta quot; exact Submodule.Quotient.addCommGroup _

instance {M : Type _} [AddCommGroup M] [Module R M] (x y : Submodule R M) :
  Module R (x ⧸ₛ y) := by delta quot; exact Submodule.Quotient.module _

instance (i : Fin s.length) : AddCommGroup (s.interList_qf N i) := by
  delta interList_qf
  infer_instance

instance (i : Fin s.length) : Module R (s.interList_qf N i) := by
  delta interList_qf
  infer_instance

private noncomputable def aux1
    {x : Submodule R N} {k : Submodule R x} {y : Type _} [AddCommGroup y] [Module R y]
    (l : x →ₗ[R] y) (eq1 : LinearMap.ker l = k) : (x ⧸ k) ≃ₗ[R] LinearMap.range l :=
  LinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) $ by
      rw [eq1]
      exact Submodule.map_id _ : (x ⧸ k) ≃ₗ[R] (x ⧸ LinearMap.ker l))
    (LinearMap.quotKerEquivRange l)

set_option maxHeartbeats 1600000 in
/-- the `i`-th quotient factor of `s ⊓ N` is equivalent to the range of
  `(s.interList_get_succ_to_qf N i)`-/
noncomputable def interList_qf_equiv (i : Fin s.length) :
    (s.interList_qf N i) ≃ₗ[R] LinearMap.range (s.interList_get_succ_to_qf N i) :=
  aux1 N (s.interList_get_succ_to_qf N i) (s.interList_get_succ_to_qf_ker N i)

private noncomputable def interList_qf_aux (i : Fin s.length) :
    (s.interList_qf N i ≃ₗ[R] (PUnit : Type)) ⊕ s.interList_qf N i ≃ₗ[R] s.qf i :=
  IsSimpleModule.equiv_punit_sum_equiv_of_equiv_submodule (R := R) (m := s.qf i)
    (e := s.interList_qf_equiv N i)

private lemma interList_qf_aux' (i : Fin s.length) :
    Nonempty (s.interList_qf N i ≃ₗ[R] (PUnit : Type)) ∨
    Nonempty (s.interList_qf N i ≃ₗ[R] s.qf i) :=
  IsSimpleModule.equiv_punit_sum_equiv_of_equiv_submodule' (R := R) (m := s.qf i)
    (e := s.interList_qf_equiv N i)

lemma interList_get_succ_eq_get_of_equiv_punit (i : Fin s.length)
    (e : s.interList_qf N i ≃ₗ[R] (PUnit : Type)) :
    s.interList_get_succ N i = s.interList_get N i := by
  have uniq_qf : Nonempty (Unique (s.interList_qf N i)) := ⟨Equiv.unique e.toEquiv⟩
  delta interList_qf quot at uniq_qf
  replace uniq_qf := Submodule.unique_quotient_iff_forall_mem.mp uniq_qf
  ext x : 1; fconstructor
  · intro hx
    exact @uniq_qf ⟨x, hx⟩
  · intro hx; exact s.interList_get_le_get_succ N i hx

/-- the `i`-th element of `s ⊓ N` is either equal to the `i+1`-st element of `s ⊓ N` or
  the `i`-th quotient factor is a simple module. -/
noncomputable def eq_or_interList_qf_is_simple_module (i : Fin s.length) :
    Inhabited (s.interList_get_succ N i = s.interList_get N i) ⊕
    Inhabited (IsSimpleModule R (s.interList_qf N i)) :=
  match (s.interList_qf_aux N i) with
  | Sum.inl e => Sum.inl ⟨s.interList_get_succ_eq_get_of_equiv_punit N i e⟩
  | Sum.inr e => Sum.inr ⟨IsSimpleModule.congr e⟩

lemma eq_or_interList_qf_is_simple_module' (i : Fin s.length) :
    s.interList_get_succ N i = s.interList_get N i ∨ IsSimpleModule R (s.interList_qf N i) :=
  (s.eq_or_interList_qf_is_simple_module N i).recOn
    (Or.inl ∘ λ I ↦ I.default) (Or.inr ∘ λ I ↦ I.default)

lemma interList_get_eq_succ_or_covby (i : Fin s.length) :
    s.interList_get N i = s.interList_get_succ N i ∨
    s.interList_get N i ⋖ s.interList_get_succ N i := by
  rcases s.eq_or_interList_qf_is_simple_module' N i with (h | h)
  · left; rw [h]
  · right
    delta interList_qf quot at h
    rw [covBy_iff_quot_is_simple]
    convert h
    exact s.interList_get_le_get_succ N i

lemma interList_wcovby (i : Fin s.length) :
    s.interList_get N i ⩿ s.interList_get_succ N i :=
wcovBy_iff_covBy_or_eq.mpr $ Or.symm $ s.interList_get_eq_succ_or_covby N i

lemma interList_chain'_wcovby : (s.interList N).Chain' (. ⩿ .) :=
List.chain'_iff_get.mpr $ λ i h ↦ s.interList_wcovby N ⟨i, by simpa [s.interList_length] using h⟩

/-- either the `i`-th element of `s ⊓ N` is equal to `i+1`-st element of `s ⊓ N` or
  the `i`-th quotient factor of `s ⊓ N` is equal to `i`-th quotient factor of `s`-/
noncomputable def eq_sum_interList_qf_equiv_qf (i : Fin s.length) :
  (Inhabited $ s.interList_get_succ N i = s.interList_get N i) ⊕
  (s.interList_qf N i ≃ₗ[R] s.qf i) :=
(s.interList_qf_aux N i).map (λ e ↦ ⟨s.interList_get_succ_eq_get_of_equiv_punit N i e⟩) id

lemma eq_sum_interList_qf_equiv_qf' (i : Fin s.length) :
    (s.interList_get_succ N i = s.interList_get N i) ∨
    (Nonempty $ s.interList_qf N i ≃ₗ[R] s.qf i) :=
match (s.eq_sum_interList_qf_equiv_qf N i) with
| Sum.inl ⟨h⟩ => Or.inl h
| Sum.inr h => Or.inr ⟨h⟩

/-- the start of `s ⊓ N`. -/
def interList_head : Submodule R N :=
  (s.interList N).get ⟨0, by rw [s.interList_length]; norm_num⟩

lemma interList_head_eq :
    s.interList_head N = Submodule.comap N.subtype (N ⊓ s.head) :=
  s.interList_get_eq_aux N 0 $ by linarith

/-- the end of `s ⊓ N`. -/
def interList_last : Submodule R N :=
  (s.interList N).get ⟨s.length, by rw [s.interList_length]; linarith⟩

lemma interList_last_eq :
    s.interList_last N = Submodule.comap N.subtype (N ⊓ s.last) :=
  s.interList_get_eq_aux N s.length $ by linarith

lemma interList_head_eq_head_of_head_eq_head (s0 : s.head = ⊥) : s.interList_head N = ⊥ := by
    rw [eq_bot_iff, interList_head_eq]
    rintro x ⟨-, (hx2 : x.1 ∈ s.head)⟩
    rw [s0] at hx2
    ext1
    exact hx2

lemma interList_last_eq_top_of_last_eq_top (slast : s.last = ⊤) :
    s.interList_last N = ⊤ := by
  rw [eq_top_iff, interList_last_eq]
  rintro ⟨x, hx⟩ ⟨⟩
  exact ⟨hx, slast.symm ▸ ⟨⟩⟩

/-- if `s ⊓ N` has no duplication, then its quotient factors are the same as that of `s`. -/
noncomputable def interList_qf_equiv_of_nodup (h : (s.interList N).Nodup) (i : Fin s.length) :
  (s.interList_qf N i ≃ₗ[R] s.qf i) :=
match (s.eq_sum_interList_qf_equiv_qf N i) with
| Sum.inl ⟨e⟩ => by
    have : IsIrrefl (Submodule R N) (. ≠ .) := ⟨fun _ r ↦ r rfl⟩
    have := Fin.ext_iff.mp $ h.nodup.get_inj_iff.mp e
    norm_num at this
| Sum.inr e => e

lemma eq_interList_get_of_head_eq_head_and_interList_nodup (s0 : s.head = ⊥)
    (h : (s.interList N).Nodup) (i : Fin $ s.length + 1) :
  s i = Submodule.map N.subtype ((s.interList N).get $ i.cast (s.interList_length N).symm) := by
  classical
  have inter_chain := List.chain'_covby_of_chain'_wcovby_of_nodup _ (s.interList_chain'_wcovby N) h
  rcases i with ⟨i, hi⟩
  induction i with | zero => ?_ | succ i ih => ?_
  · simp only [Fin.mk_zero]
    rw [show s 0 = _ from s0, eq_comm, eq_bot_iff]
    rintro - ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, show (s.interList N).get (Fin.cast (s.interList_length N).symm 0) =
      Submodule.comap N.subtype (N ⊓ s.head) from s.interList_head_eq N, s0, inf_bot_eq,
      Submodule.comap_bot, LinearMap.mem_ker] at hy

    exact hy

  change i + 1 < _ at hi
  have ih' := ih ((lt_add_one _).trans hi) -- s i = N ⊓ s i
  have ih'' : s ⟨i, (lt_add_one _).trans hi⟩ = N ⊓ s ⟨i, (lt_add_one _).trans hi⟩ := by
    erw [ih']
    rw [eq_comm, inf_eq_right]
    rintro _ ⟨y, hy, rfl⟩
    simp only [Fin.cast_mk, SetLike.mem_coe] at hy
    rw [s.interList_get_eq_aux N i ((lt_add_one _).trans hi), Submodule.mem_comap] at hy
    exact hy.1

  rw [List.chain'_iff_get] at inter_chain
  have h1 := inter_chain i (by
    rw [interList_length, Nat.add_succ_sub_one, add_zero]
    exact Nat.succ_lt_succ_iff.mp $ hi)
  -- N ⊓ s i ⋖ N ⊓ s (i + 1) as N-submodule

  have le1 : N ⊓ s ⟨i, (lt_add_one _).trans hi⟩ ≤ N ⊓ s ⟨i + 1, hi⟩ := by
    simp only [le_inf_iff, inf_le_left, true_and]
    refine le_trans inf_le_right (s.strictMono.monotone $ by norm_num)

  have covby2 : s ⟨i, (lt_add_one _).trans hi⟩ ⋖ s ⟨i + 1, hi⟩ := s.step ⟨i, by linarith only [hi]⟩

  rw [← ih''] at le1
  obtain (H|H) := covby2.eq_or_eq le1 inf_le_right
  · have eq2 : (s.interList N).get ⟨i + 1, by rw [s.interList_length]; exact hi⟩ =
      (s.interList N).get ⟨i, by rw [s.interList_length]; exact (lt_add_one _).trans hi⟩ := by
      refine le_antisymm ?_ h1.le
      rw [s.interList_get_eq_aux N _ hi, s.interList_get_eq_aux N _ ((lt_add_one _).trans hi)]
      refine Submodule.comap_mono ?_
      simp only [le_inf_iff, inf_le_left, true_and]
      rw [H]
    have : IsIrrefl (Submodule R N) (. ≠ .) := ⟨fun _ r ↦ r rfl⟩
    have : i + 1 = i := Fin.ext_iff.mp $ h.nodup.get_inj_iff.mp eq2
    norm_num at this
  · rw [← H]
    ext1 x
    simp only [Fin.cast_mk, Submodule.mem_map, Submodule.coeSubtype, Subtype.exists,
      exists_and_right, exists_eq_right]
    rw [s.interList_get_eq_aux N _ hi]
    fconstructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, ⟨hx1, hx2⟩⟩
    · rintro ⟨hy0, ⟨-, hy1⟩⟩; exact ⟨hy0, hy1⟩

lemma eq_top_of_interList_nodup (s0 : s.head = ⊥) (slast : s.last = ⊤)
    (hinter : (s.interList N).Nodup) :  N = ⊤ := by
  classical
  have eq0 := s.eq_interList_get_of_head_eq_head_and_interList_nodup N s0 hinter (Fin.last _)
  rw [show s (Fin.last _) = _ from slast, interList_get_eq_aux (hi := by simp)] at eq0
  simp only [Fin.coe_cast, Fin.val_last, Submodule.comap_inf, Submodule.comap_subtype_self,
    _root_.le_top, inf_of_le_right] at eq0
  rw [show s ⟨s.length, _⟩ = _ from slast] at eq0
  simp only [Submodule.comap_top, Submodule.map_top, Submodule.range_subtype] at eq0
  exact eq0.symm

lemma interList_not_nodup_of_lt_top (s0 : s.head = ⊥) (slast : s.last = ⊤)
    (h : N < ⊤) : ¬ (s.interList N).Nodup := by
  contrapose! h
  rw [lt_top_iff_ne_top, not_ne_iff]
  apply eq_top_of_interList_nodup <;>
  assumption

/-- after removing duplication from `s ⊓ N`, it becomes a composition series. -/
@[simps!]
noncomputable def ofInterList :
  CompositionSeries (Submodule R N) :=
let _ : DecidableEq (Submodule R N) := Classical.decEq _
RelSeries.fromListChain' (s.interList N).dedup (List.dedup_ne_nil_of_ne_nil _ $
  List.map_ne_nil_of_ne_nil _ s.toList_ne_empty _) $ List.dedup_chain'_covby_of_chain'_wcovby _ $
  interList_chain'_wcovby s N

lemma ofInterList_head_eq_bot_of_head_eq_bot (s0 : s.head = ⊥) :
    (s.ofInterList N).head = ⊥ := by
  classical
  change List.get _ ⟨0, _⟩ = _
  have := List.dedup_head?_of_chain'_wcovby _ (s.interList_chain'_wcovby N)
  rw [← List.get?_zero, ← List.get?_zero] at this
  simpa [List.get_eq_get?, this] using interList_head_eq_head_of_head_eq_head (s0 := s0) _

lemma ofInterList_last_eq_top_of_last_eq_top (slast : s.last = ⊤) :
    (s.ofInterList N).last = ⊤ := by
  classical
  change List.get _ ⟨List.length _ - 1, _⟩ = _
  rw [List.get_length_sub_one, List.dedup_getLast_eq_getLast_of_chain'_wcovby (l_ne_nil :=
    show (s.interList N) ≠ [] from List.map_ne_nil_of_ne_nil _ s.toList_ne_empty _)
    (l_chain := interList_chain'_wcovby s N), List.getLast_eq_get]
  simp only [s.interList_length]
  exact s.interList_last_eq_top_of_last_eq_top N slast

lemma exists_compositionSeries_with_smaller_length_of_lt_top (h : N < ⊤)
    (s0 : s.head = ⊥) (slast : s.last = ⊤) :
    ∃ (s' : CompositionSeries (Submodule R N)),
      s'.head = ⊥ ∧ s'.last = ⊤ ∧ s'.length < s.length := by
  classical
  refine ⟨s.ofInterList N, s.ofInterList_head_eq_bot_of_head_eq_bot N s0,
    s.ofInterList_last_eq_top_of_last_eq_top N slast, ?_⟩
  have ineq1 : (s.interList N).dedup.length < (s.interList N).length :=
    List.dedup_length_lt_of_not_nodup _ (s.interList_not_nodup_of_lt_top N s0 slast h)
  rw [interList_length] at ineq1
  have ineq2 : 0 < (s.interList N).dedup.length := by
    by_contra rid
    push_neg at rid
    norm_num at rid
    exact List.map_ne_nil_of_ne_nil _ s.toList_ne_empty _ rid

  apply Nat.sub_lt_right_of_lt_add (H := ineq2) (h := ineq1)

end CompositionSeries
