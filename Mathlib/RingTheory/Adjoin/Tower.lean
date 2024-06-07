/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Adjoin.FG

#align_import ring_theory.adjoin.tower from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Adjoining elements and being finitely generated in an algebra tower

## Main results

 * `Algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
   then `A` is finitely generated as `R`-algebra
 * `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is noetherian, and
   C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/


open Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Algebra

theorem adjoin_restrictScalars (C D E : Type*) [CommSemiring C] [CommSemiring D] [CommSemiring E]
    [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars
        C := by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E) by
    ext x
    change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
    rw [this]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨algebraMap D E y, ⟨y, ⟨Algebra.mem_top, rfl⟩⟩⟩, hy⟩
  · rintro ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩
    exact ⟨z, Eq.trans h1 h2⟩
#align algebra.adjoin_restrict_scalars Algebra.adjoin_restrictScalars

theorem adjoin_res_eq_adjoin_res (C D E F : Type*) [CommSemiring C] [CommSemiring D]
    [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F]
    [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set D} {T : Set E}
    (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C := by
  rw [adjoin_restrictScalars C E, adjoin_restrictScalars C D, ← hS, ← hT, ← Algebra.adjoin_image,
    ← Algebra.adjoin_image, ← AlgHom.coe_toRingHom, ← AlgHom.coe_toRingHom,
    IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom, ← adjoin_union_eq_adjoin_adjoin, ←
    adjoin_union_eq_adjoin_adjoin, Set.union_comm]
#align algebra.adjoin_res_eq_adjoin_res Algebra.adjoin_res_eq_adjoin_res

end Algebra

section

open scoped Classical

theorem Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).FG)
    (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := hRS
  let ⟨t, ht⟩ := hSA
  ⟨s.image (algebraMap S A) ∪ t, by
    rw [Finset.coe_union, Finset.coe_image, Algebra.adjoin_algebraMap_image_union_eq_adjoin_adjoin,
      hs, Algebra.adjoin_top, ht, Subalgebra.restrictScalars_top, Subalgebra.restrictScalars_top]⟩
#align algebra.fg_trans' Algebra.fg_trans'

end

section ArtinTate

variable (C : Type*)

section Semiring

variable [CommSemiring A] [CommSemiring B] [Semiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

open scoped Classical

theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) :
    ∃ B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG := by
  cases' hAC with x hx
  cases' hBC with y hy
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f hf using this
  let s : Finset B := Finset.image₂ f (x ∪ y * y) y
  have hxy :
    ∀ xi ∈ x, xi ∈ span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
          ⟨f xi yj, Algebra.subset_adjoin <| mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
          (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) ≤
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) := by
    rw [span_mul_span, span_le, coe_insert]
    rintro _ ⟨yi, rfl | hyi, yj, rfl | hyj, rfl⟩ <;> dsimp
    · rw [mul_one]
      exact subset_span (Set.mem_insert _ _)
    · rw [one_mul]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
    · rw [mul_one]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk,
                Algebra.subset_adjoin <|
                  mem_image₂_of_mem (mem_union_right _ <| mul_mem_mul hyi hyj) hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk ∈ _))
  refine ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, ?_⟩
  convert restrictScalars_injective A (Algebra.adjoin A (s : Set B)) C _
  rw [restrictScalars_top, eq_top_iff, ← Algebra.top_toSubmodule, ← hx, Algebra.adjoin_eq_span,
    span_le]
  refine fun r hr =>
    Submonoid.closure_induction hr (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _)
      fun p q hp hq => hyy <| Submodule.mul_mem_mul hp hq
#align exists_subalgebra_of_fg exists_subalgebra_of_fg

end Semiring

section Ring

variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : Module.Finite B₀ C := ⟨hB₀C⟩
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi
#align fg_of_fg_of_fg fg_of_fg_of_fg

end Ring

end ArtinTate
