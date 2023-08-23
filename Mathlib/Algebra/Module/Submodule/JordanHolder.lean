/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Order.JordanHolder
import Mathlib.Order.RelSeries
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule

/-!

# Composition Series of a module

This files relates `LTSeries` and `CompositionSeries` so that we can prove the two equivalent
definition of module length are the same

-/

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]
variable (s : CompositionSeries (Submodule R M)) (N : Submodule R M)

namespace CompositionSeries

/-- if `x ≤ y` are both `R`-submodule of `M`, we can mathematically form their quotient but type
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
  rw [←covby_iff_quot_is_simple (s.strictMono.monotone _)]
  · exact s.step i
  · change i.1 ≤ i.1 + 1
    linarith

/-- Given an `R`-submodule `N`, we can form a list of submodule of `N` by taking intersections with
a given composition series-/
def interList : List (Submodule R N) :=
  s.toList.map $ fun si => Submodule.comap N.subtype (N ⊓ si)

lemma interList_length : (s.interList N).length = s.length + 1 :=
by rw [interList, List.length_map, CompositionSeries.toList, List.length_ofFn]

private def interList_get (i : Fin s.length) : Submodule R N :=
  (s.interList N).get (i.castLE <| by rw [interList_length]; linarith)

private def interList_get_succ (i : Fin s.length) : Submodule R N :=
  (s.interList N).get (i.succ.castLE <| by rw [interList_length])

lemma interList_get_eq (i : Fin s.length) :
    s.interList_get N i =
    Submodule.comap N.subtype (N ⊓ s i.castSucc) := by
  delta interList_get interList
  rw [List.get_map]
  congr 2
  exact List.get_ofFn _ _

lemma interList_get_succ_eq (i : Fin s.length) :
    s.interList_get_succ N i =
    Submodule.comap N.subtype (N ⊓ s i.succ) := by
  delta interList_get_succ interList
  rw [List.get_map]
  congr 2
  exact List.get_ofFn _ _

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
  rw [interList_get_succ_eq, Submodule.mem_comap] at h
  exact h.2

lemma interList_get_succ_to_qf_ker (i : Fin s.length) :
    LinearMap.ker (s.interList_get_succ_to_qf N i) =
    Submodule.comap (s.interList_get_succ N i).subtype (s.interList_get N i) := by
  ext ⟨x, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    interList_get_succ_to_qf_apply, Submodule.Quotient.mk_eq_zero, LinearMap.restrict_apply,
    Submodule.mem_comap]
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

private lemma interList_qf_aux (i : Fin s.length) :
    Nonempty (s.interList_qf N i ≃ₗ[R] (PUnit : Type)) ∨
    Nonempty (s.interList_qf N i ≃ₗ[R] s.qf i) :=
  IsSimpleModule.equiv_punit_sum_equiv_of_equiv_submodule' (R := R) (m := s.qf i)
    (e := s.interList_qf_equiv N i)

set_option maxHeartbeats 500000 in
lemma eq_or_interList_qf_is_simple_module (i : Fin s.length) :
  s.interList_get_succ N i = s.interList_get N i ∨
  IsSimpleModule R (s.interList_qf N i) := by
  obtain ⟨⟨e⟩⟩|⟨⟨e⟩⟩ := s.interList_qf_aux N i
  · left
    have uniq_qf : Nonempty (Unique (s.interList_qf N i)) := ⟨Equiv.unique e.toEquiv⟩
    delta interList_qf quot at uniq_qf
    replace uniq_qf := Submodule.unique_quotient_iff_forall_mem.mp uniq_qf

    ext x : 1; fconstructor
    · intro hx
      have uniq_qf' := @uniq_qf ⟨x, hx⟩
      rw [Submodule.mem_comap] at uniq_qf'
      exact uniq_qf'
    · intro hx; exact s.interList_get_le_get_succ N i hx
  · right; exact IsSimpleModule.congr e

set_option maxHeartbeats 1600000 in
lemma interList_get_eq_succ_or_covby (i : Fin s.length) :
    s.interList_get N i = s.interList_get_succ N i ∨
    s.interList_get N i ⋖ s.interList_get_succ N i := by
  rcases s.eq_or_interList_qf_is_simple_module N i with (h|h)
  · left; rw [h]
  · right
    delta interList_qf quot at h
    rw [covby_iff_quot_is_simple]
    exact h

end CompositionSeries
