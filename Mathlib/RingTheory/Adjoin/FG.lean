/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `FG (S : Subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
  as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/


universe u v w

open Subsemiring Ring Submodule

open Pointwise

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [Algebra R A]
  {s t : Set A}

theorem fg_trans (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).toSubmodule.FG) :
    (adjoin R (s ∪ t)).toSubmodule.FG := by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm ?_ ?_⟩
  · rw [span_le, Set.mul_subset_iff]
    intro x hx y hy
    change x * y ∈ adjoin R (s ∪ t)
    refine Subalgebra.mul_mem _ ?_ ?_
    · have : x ∈ Subalgebra.toSubmodule (adjoin R s) := by
        rw [← hp']
        exact subset_span hx
      exact adjoin_mono Set.subset_union_left this
    have : y ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) := by
      rw [← hq']
      exact subset_span hy
    change y ∈ adjoin R (s ∪ t)
    rwa [adjoin_union_eq_adjoin_adjoin]
  · intro r hr
    change r ∈ adjoin R (s ∪ t) at hr
    rw [adjoin_union_eq_adjoin_adjoin] at hr
    change r ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) at hr
    rw [← hq', ← Set.image_id q, Finsupp.mem_span_image_iff_linearCombination (adjoin R s)] at hr
    rcases hr with ⟨l, hlq, rfl⟩
    have := @Finsupp.linearCombination_apply A A (adjoin R s)
    rw [this, Finsupp.sum]
    refine sum_mem ?_
    intro z hz
    change (l z).1 * _ ∈ _
    have : (l z).1 ∈ Subalgebra.toSubmodule (adjoin R s) := (l z).2
    rw [← hp', ← Set.image_id p, Finsupp.mem_span_image_iff_linearCombination R] at this
    rcases this with ⟨l2, hlp, hl⟩
    have := @Finsupp.linearCombination_apply A A R
    rw [this] at hl
    rw [← hl, Finsupp.sum_mul]
    refine sum_mem ?_
    intro t ht
    change _ * _ ∈ _
    rw [smul_mul_assoc]
    refine smul_mem _ _ ?_
    exact subset_span ⟨t, hlp ht, z, hlq hz, rfl⟩

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : Finset A` such that
`Algebra.adjoin R t = S`. -/
def FG (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R ↑t = S

theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).FG :=
  ⟨s, rfl⟩

theorem fg_def {S : Subalgebra R A} : S.FG ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset

theorem fg_bot : (⊥ : Subalgebra R A).FG :=
  ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩

theorem fg_of_fg_toSubmodule {S : Subalgebra R A} : S.toSubmodule.FG → S.FG :=
  fun ⟨t, ht⟩ ↦ ⟨t, le_antisymm
    (Algebra.adjoin_le fun x hx ↦ show x ∈ Subalgebra.toSubmodule S from ht ▸ subset_span hx) <|
    show Subalgebra.toSubmodule S ≤ Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx ↦
      span_le.mpr (fun _ hx ↦ Algebra.subset_adjoin hx)
        (show x ∈ span R ↑t by
          rw [ht]
          exact hx)⟩

theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.FG :=
  fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))

theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := h
  ⟨s, toSubmodule.injective <| by
    rw [Algebra.top_toSubmodule, eq_top_iff, ← hs, span_le]
    exact Algebra.subset_adjoin⟩

theorem FG.prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.FG) (hT : T.FG) :
    (S.prod T).FG := by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2, ← ht.2]
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
    Algebra.adjoin_inl_union_inr_eq_prod R s t⟩

section

theorem FG.map {S : Subalgebra R A} (f : A →ₐ[R] B) (hs : S.FG) : (S.map f).FG := by
  let ⟨s, hs⟩ := hs
  classical
  exact ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

end

theorem fg_of_fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hf : Function.Injective f)
    (hs : (S.map f).FG) : S.FG :=
  let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h ↦ hf h,
    map_injective hf <| by
      rw [← Algebra.adjoin_image, Finset.coe_preimage, Set.image_preimage_eq_of_subset, hs]
      rw [← AlgHom.coe_range, ← Algebra.adjoin_le_iff, hs, ← Algebra.map_top]
      exact map_mono le_top⟩

theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG ↔ S.FG :=
  ⟨fun h ↦ by
    rw [← S.range_val, ← Algebra.map_top]
    exact FG.map _ h, fun h ↦
    fg_of_fg_map _ S.val Subtype.val_injective <| by
      rw [Algebra.map_top, range_val]
      exact h⟩

theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A → Prop) (base : P ⊥)
    (ih : ∀ (S : Subalgebra R A) (x : A), P S → P (Algebra.adjoin R (insert x S)))
    (S : Subalgebra R A) : P S := by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine Finset.induction_on t ?_ ?_
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h

theorem FG.sup {S S' : Subalgebra R A} (hS : Subalgebra.FG S) (hS' : Subalgebra.FG S') :
    Subalgebra.FG (S ⊔ S') :=
  let ⟨s, hs⟩ := Subalgebra.fg_def.1 hS
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hS'
  fg_def.mpr ⟨s ∪ s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩

end Subalgebra

section Semiring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance AlgHom.isNoetherianRing_range (f : A →ₐ[R] B) [IsNoetherianRing A] :
    IsNoetherianRing f.range :=
  _root_.isNoetherianRing_range f.toRingHom

end Semiring

section Ring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem isNoetherianRing_of_fg {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _

theorem is_noetherian_subring_closure (s : Set R) (hs : s.Finite) :
    IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end Ring
