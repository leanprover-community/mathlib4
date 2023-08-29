/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.MvPolynomial.Basic

#align_import ring_theory.adjoin.fg from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

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
  -- ⊢ FG (↑Subalgebra.toSubmodule (adjoin R (s ∪ t)))
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  -- ⊢ FG (↑Subalgebra.toSubmodule (adjoin R (s ∪ t)))
  refine' fg_def.2 ⟨p * q, hp.mul hq, le_antisymm _ _⟩
  -- ⊢ span R (p * q) ≤ ↑Subalgebra.toSubmodule (adjoin R (s ∪ t))
  · rw [span_le]
    -- ⊢ p * q ⊆ ↑(↑Subalgebra.toSubmodule (adjoin R (s ∪ t)))
    rintro _ ⟨x, y, hx, hy, rfl⟩
    -- ⊢ (fun x x_1 => x * x_1) x y ∈ ↑(↑Subalgebra.toSubmodule (adjoin R (s ∪ t)))
    change x * y ∈ adjoin R (s ∪ t)
    -- ⊢ x * y ∈ adjoin R (s ∪ t)
    refine' Subalgebra.mul_mem _ _ _
    -- ⊢ x ∈ adjoin R (s ∪ t)
    · have : x ∈ Subalgebra.toSubmodule (adjoin R s) := by
        rw [← hp']
        exact subset_span hx
      exact adjoin_mono (Set.subset_union_left _ _) this
      -- 🎉 no goals
    have : y ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) := by
      rw [← hq']
      exact subset_span hy
    change y ∈ adjoin R (s ∪ t)
    -- ⊢ y ∈ adjoin R (s ∪ t)
    rwa [adjoin_union_eq_adjoin_adjoin]
    -- 🎉 no goals
  · intro r hr
    -- ⊢ r ∈ span R (p * q)
    change r ∈ adjoin R (s ∪ t) at hr
    -- ⊢ r ∈ span R (p * q)
    rw [adjoin_union_eq_adjoin_adjoin] at hr
    -- ⊢ r ∈ span R (p * q)
    change r ∈ Subalgebra.toSubmodule (adjoin (adjoin R s) t) at hr
    -- ⊢ r ∈ span R (p * q)
    rw [← hq', ← Set.image_id q, Finsupp.mem_span_image_iff_total (adjoin R s)] at hr
    -- ⊢ r ∈ span R (p * q)
    rcases hr with ⟨l, hlq, rfl⟩
    -- ⊢ ↑(Finsupp.total A A { x // x ∈ adjoin R s } _root_.id) l ∈ span R (p * q)
    have := @Finsupp.total_apply A A (adjoin R s)
    -- ⊢ ↑(Finsupp.total A A { x // x ∈ adjoin R s } _root_.id) l ∈ span R (p * q)
    rw [this, Finsupp.sum]
    -- ⊢ (Finset.sum l.support fun a => ↑l a • _root_.id a) ∈ span R (p * q)
    refine' sum_mem _
    -- ⊢ ∀ (c : A), c ∈ l.support → ↑l c • _root_.id c ∈ span R (p * q)
    intro z hz
    -- ⊢ ↑l z • _root_.id z ∈ span R (p * q)
    change (l z).1 * _ ∈ _
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    have : (l z).1 ∈ Subalgebra.toSubmodule (adjoin R s) := (l z).2
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    rw [← hp', ← Set.image_id p, Finsupp.mem_span_image_iff_total R] at this
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    rcases this with ⟨l2, hlp, hl⟩
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    have := @Finsupp.total_apply A A R
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    rw [this] at hl
    -- ⊢ ↑(↑l z) * _root_.id z ∈ span R (p * q)
    rw [← hl, Finsupp.sum_mul]
    -- ⊢ (Finsupp.sum l2 fun a c => c • _root_.id a * _root_.id z) ∈ span R (p * q)
    refine' sum_mem _
    -- ⊢ ∀ (c : A), c ∈ l2.support → (fun a c => c • _root_.id a * _root_.id z) c (↑l …
    intro t ht
    -- ⊢ (fun a c => c • _root_.id a * _root_.id z) t (↑l2 t) ∈ span R (p * q)
    change _ * _ ∈ _
    -- ⊢ ↑l2 t • _root_.id t * _root_.id z ∈ span R (p * q)
    rw [smul_mul_assoc]
    -- ⊢ ↑l2 t • (_root_.id t * _root_.id z) ∈ span R (p * q)
    refine' smul_mem _ _ _
    -- ⊢ _root_.id t * _root_.id z ∈ span R (p * q)
    exact subset_span ⟨t, z, hlp ht, hlq hz, rfl⟩
    -- 🎉 no goals
#align algebra.fg_trans Algebra.fg_trans

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : Finset A` such that
`Algebra.adjoin R t = S`. -/
def FG (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R ↑t = S
#align subalgebra.fg Subalgebra.FG

theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).FG :=
  ⟨s, rfl⟩
#align subalgebra.fg_adjoin_finset Subalgebra.fg_adjoin_finset

theorem fg_def {S : Subalgebra R A} : S.FG ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset
#align subalgebra.fg_def Subalgebra.fg_def

theorem fg_bot : (⊥ : Subalgebra R A).FG :=
  ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩
#align subalgebra.fg_bot Subalgebra.fg_bot

theorem fg_of_fg_toSubmodule {S : Subalgebra R A} : S.toSubmodule.FG → S.FG :=
  fun ⟨t, ht⟩ ↦ ⟨t, le_antisymm
    (Algebra.adjoin_le fun x hx ↦ show x ∈ Subalgebra.toSubmodule S from ht ▸ subset_span hx) <|
    show Subalgebra.toSubmodule S ≤ Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx ↦
      span_le.mpr (fun x hx ↦ Algebra.subset_adjoin hx)
        (show x ∈ span R ↑t by
          rw [ht]
          -- ⊢ x ∈ ↑toSubmodule S
          exact hx)⟩
          -- 🎉 no goals
#align subalgebra.fg_of_fg_to_submodule Subalgebra.fg_of_fg_toSubmodule

theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.FG :=
  fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))
#align subalgebra.fg_of_noetherian Subalgebra.fg_of_noetherian

theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := h
  ⟨s, toSubmodule.injective <| by
    rw [Algebra.top_toSubmodule, eq_top_iff, ← hs, span_le]
    -- ⊢ ↑s ⊆ ↑(↑toSubmodule (Algebra.adjoin R ↑s))
    exact Algebra.subset_adjoin⟩
    -- 🎉 no goals
#align subalgebra.fg_of_submodule_fg Subalgebra.fg_of_submodule_fg

theorem FG.prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.FG) (hT : T.FG) :
    (S.prod T).FG := by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  -- ⊢ FG (Subalgebra.prod S T)
  obtain ⟨t, ht⟩ := fg_def.1 hT
  -- ⊢ FG (Subalgebra.prod S T)
  rw [← hs.2, ← ht.2]
  -- ⊢ FG (Subalgebra.prod (Algebra.adjoin R s) (Algebra.adjoin R t))
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
    Algebra.adjoin_inl_union_inr_eq_prod R s t⟩
#align subalgebra.fg.prod Subalgebra.FG.prod

section

open Classical

theorem FG.map {S : Subalgebra R A} (f : A →ₐ[R] B) (hs : S.FG) : (S.map f).FG :=
  let ⟨s, hs⟩ := hs
  ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩
                 -- 🎉 no goals
#align subalgebra.fg.map Subalgebra.FG.map

end

theorem fg_of_fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hf : Function.Injective f)
    (hs : (S.map f).FG) : S.FG :=
  let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h ↦ hf h,
    map_injective hf <| by
      rw [← Algebra.adjoin_image, Finset.coe_preimage, Set.image_preimage_eq_of_subset, hs]
      -- ⊢ ↑s ⊆ Set.range ↑f
      rw [← AlgHom.coe_range, ← Algebra.adjoin_le_iff, hs, ← Algebra.map_top]
      -- ⊢ map f S ≤ map f ⊤
      exact map_mono le_top⟩
      -- 🎉 no goals
#align subalgebra.fg_of_fg_map Subalgebra.fg_of_fg_map

theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG ↔ S.FG :=
  ⟨fun h ↦ by
    rw [← S.range_val, ← Algebra.map_top]
    -- ⊢ FG (map (val S) ⊤)
    exact FG.map _ h, fun h ↦
    -- 🎉 no goals
    fg_of_fg_map _ S.val Subtype.val_injective <| by
      rw [Algebra.map_top, range_val]
      -- ⊢ FG S
      exact h⟩
      -- 🎉 no goals
#align subalgebra.fg_top Subalgebra.fg_top

theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A → Prop) (base : P ⊥)
    (ih : ∀ (S : Subalgebra R A) (x : A), P S → P (Algebra.adjoin R (insert x S)))
    (S : Subalgebra R A) : P S := by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine' Finset.induction_on t _ _
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h
#align subalgebra.induction_on_adjoin Subalgebra.induction_on_adjoin

end Subalgebra

section Semiring

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance AlgHom.isNoetherianRing_range (f : A →ₐ[R] B) [IsNoetherianRing A] :
    IsNoetherianRing f.range :=
  _root_.isNoetherianRing_range f.toRingHom
#align alg_hom.is_noetherian_ring_range AlgHom.isNoetherianRing_range

end Semiring

section Ring

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem isNoetherianRing_of_fg {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _
#align is_noetherian_ring_of_fg isNoetherianRing_of_fg

theorem is_noetherian_subring_closure (s : Set R) (hs : s.Finite) :
    IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
#align is_noetherian_subring_closure is_noetherian_subring_closure

end Ring
