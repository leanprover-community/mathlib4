/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.BilinearMap

#align_import algebra.module.submodule.bilinear from "leanprover-community/mathlib"@"6010cf523816335f7bae7f8584cb2edaace73940"

/-!
# Images of pairs of submodules under bilinear maps

This file provides `Submodule.map₂`, which is later used to implement `Submodule.mul`.

## Main results

* `Submodule.map₂_eq_span_image2`: the image of two submodules under a bilinear map is the span of
  their `Set.image2`.

## Notes

This file is quite similar to the n-ary section of `Data.Set.Basic` and to `Order.Filter.NAry`.
Please keep them in sync.
-/


universe uι u v

open Set

open BigOperators

open Pointwise

namespace Submodule

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

/-- Map a pair of submodules under a bilinear map.

This is the submodule version of `Set.image2`.  -/
def map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) : Submodule R P :=
  ⨆ s : p, q.map (f s)
#align submodule.map₂ Submodule.map₂

theorem apply_mem_map₂ (f : M →ₗ[R] N →ₗ[R] P) {m : M} {n : N} {p : Submodule R M}
    {q : Submodule R N} (hm : m ∈ p) (hn : n ∈ q) : f m n ∈ map₂ f p q :=
  (le_iSup _ ⟨m, hm⟩ : _ ≤ map₂ f p q) ⟨n, hn, by rfl⟩
                                                  -- 🎉 no goals
#align submodule.apply_mem_map₂ Submodule.apply_mem_map₂

theorem map₂_le {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q : Submodule R N}
    {r : Submodule R P} : map₂ f p q ≤ r ↔ ∀ m ∈ p, ∀ n ∈ q, f m n ∈ r :=
  ⟨fun H _m hm _n hn => H <| apply_mem_map₂ _ hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩
#align submodule.map₂_le Submodule.map₂_le

variable (R)
theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : Set M) (t : Set N) :
    map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n => f m n) s t) := by
  apply le_antisymm
  -- ⊢ map₂ f (span R s) (span R t) ≤ span R (image2 (fun m n => ↑(↑f m) n) s t)
  · rw [map₂_le]
    -- ⊢ ∀ (m : M), m ∈ span R s → ∀ (n : N), n ∈ span R t → ↑(↑f m) n ∈ span R (imag …
    apply @span_induction' R M _ _ _ s
    intro a ha
    apply @span_induction' R N _ _ _ t
    intro b hb
    exact subset_span ⟨_, _, ‹_›, ‹_›, rfl⟩
    all_goals intros; simp only [*, add_mem, smul_mem, zero_mem, _root_.map_zero, map_add,
                                 LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply,
                                 SMulHomClass.map_smul]
  · rw [span_le]
    -- ⊢ image2 (fun m n => ↑(↑f m) n) s t ⊆ ↑(map₂ f (span R s) (span R t))
    rintro _ ⟨a, b, ha, hb, rfl⟩
    -- ⊢ (fun m n => ↑(↑f m) n) a b ∈ ↑(map₂ f (span R s) (span R t))
    exact apply_mem_map₂ _ (subset_span ha) (subset_span hb)
    -- 🎉 no goals
#align submodule.map₂_span_span Submodule.map₂_span_span
variable {R}

@[simp]
theorem map₂_bot_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) : map₂ f p ⊥ = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m _hm n hn => by
      rw [Submodule.mem_bot] at hn
      -- ⊢ ↑(↑f m) n ∈ ⊥
      rw [hn, LinearMap.map_zero]; simp only [mem_bot]
      -- ⊢ 0 ∈ ⊥
                                   -- 🎉 no goals
#align submodule.map₂_bot_right Submodule.map₂_bot_right

@[simp]
theorem map₂_bot_left (f : M →ₗ[R] N →ₗ[R] P) (q : Submodule R N) : map₂ f ⊥ q = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m hm n hn => by
      rw [Submodule.mem_bot] at hm ⊢
      -- ⊢ ↑(↑f m) n = 0
      rw [hm, LinearMap.map_zero₂]
      -- 🎉 no goals
#align submodule.map₂_bot_left Submodule.map₂_bot_left

@[mono]
theorem map₂_le_map₂ {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q₁ q₂ : Submodule R N}
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) : map₂ f p₁ q₁ ≤ map₂ f p₂ q₂ :=
  map₂_le.2 fun _m hm _n hn => apply_mem_map₂ _ (hp hm) (hq hn)
#align submodule.map₂_le_map₂ Submodule.map₂_le_map₂

theorem map₂_le_map₂_left {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q : Submodule R N}
    (h : p₁ ≤ p₂) : map₂ f p₁ q ≤ map₂ f p₂ q :=
  map₂_le_map₂ h (le_refl q)
#align submodule.map₂_le_map₂_left Submodule.map₂_le_map₂_left

theorem map₂_le_map₂_right {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q₁ q₂ : Submodule R N}
    (h : q₁ ≤ q₂) : map₂ f p q₁ ≤ map₂ f p q₂ :=
  map₂_le_map₂ (le_refl p) h
#align submodule.map₂_le_map₂_right Submodule.map₂_le_map₂_right

theorem map₂_sup_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q₁ q₂ : Submodule R N) :
    map₂ f p (q₁ ⊔ q₂) = map₂ f p q₁ ⊔ map₂ f p q₂ :=
  le_antisymm
    (map₂_le.2 fun _m hm _np hnp =>
      let ⟨_n, hn, _p, hp, hnp⟩ := mem_sup.1 hnp
      mem_sup.2 ⟨_, apply_mem_map₂ _ hm hn, _, apply_mem_map₂ _ hm hp, hnp ▸ (map_add _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_right le_sup_left) (map₂_le_map₂_right le_sup_right))
#align submodule.map₂_sup_right Submodule.map₂_sup_right

theorem map₂_sup_left (f : M →ₗ[R] N →ₗ[R] P) (p₁ p₂ : Submodule R M) (q : Submodule R N) :
    map₂ f (p₁ ⊔ p₂) q = map₂ f p₁ q ⊔ map₂ f p₂ q :=
  le_antisymm
    (map₂_le.2 fun _mn hmn _p hp =>
      let ⟨_m, hm, _n, hn, hmn⟩ := mem_sup.1 hmn
      mem_sup.2
        ⟨_, apply_mem_map₂ _ hm hp, _, apply_mem_map₂ _ hn hp,
          hmn ▸ (LinearMap.map_add₂ _ _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_left le_sup_left) (map₂_le_map₂_left le_sup_right))
#align submodule.map₂_sup_left Submodule.map₂_sup_left

theorem image2_subset_map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    Set.image2 (fun m n => f m n) (↑p : Set M) (↑q : Set N) ⊆ (↑(map₂ f p q) : Set P) := by
  rintro _ ⟨i, j, hi, hj, rfl⟩
  -- ⊢ (fun m n => ↑(↑f m) n) i j ∈ ↑(map₂ f p q)
  exact apply_mem_map₂ _ hi hj
  -- 🎉 no goals
#align submodule.image2_subset_map₂ Submodule.image2_subset_map₂

theorem map₂_eq_span_image2 (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f p q = span R (Set.image2 (fun m n => f m n) (p : Set M) (q : Set N)) := by
  rw [← map₂_span_span, span_eq, span_eq]
  -- 🎉 no goals
#align submodule.map₂_eq_span_image2 Submodule.map₂_eq_span_image2

theorem map₂_flip (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f.flip q p = map₂ f p q := by
  rw [map₂_eq_span_image2, map₂_eq_span_image2, Set.image2_swap]
  -- ⊢ span R (image2 (fun a b => ↑(↑(LinearMap.flip f) b) a) ↑p ↑q) = span R (imag …
  rfl
  -- 🎉 no goals
#align submodule.map₂_flip Submodule.map₂_flip

theorem map₂_iSup_left (f : M →ₗ[R] N →ₗ[R] P) (s : ι → Submodule R M) (t : Submodule R N) :
    map₂ f (⨆ i, s i) t = ⨆ i, map₂ f (s i) t := by
  suffices map₂ f (⨆ i, span R (s i : Set M)) (span R t) = ⨆ i, map₂ f (span R (s i)) (span R t) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_iUnion, map₂_span_span, Set.image2_iUnion_left]
  -- 🎉 no goals
#align submodule.map₂_supr_left Submodule.map₂_iSup_left

theorem map₂_iSup_right (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (t : ι → Submodule R N) :
    map₂ f s (⨆ i, t i) = ⨆ i, map₂ f s (t i) := by
  suffices map₂ f (span R s) (⨆ i, span R (t i : Set N)) = ⨆ i, map₂ f (span R s) (span R (t i)) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_iUnion, map₂_span_span, Set.image2_iUnion_right]
  -- 🎉 no goals
#align submodule.map₂_supr_right Submodule.map₂_iSup_right

theorem map₂_span_singleton_eq_map (f : M →ₗ[R] N →ₗ[R] P) (m : M) :
    map₂ f (span R {m}) = map (f m) := by
  funext; rw [map₂_eq_span_image2]; apply le_antisymm
  -- ⊢ map₂ f (span R {m}) x✝ = map (↑f m) x✝
          -- ⊢ span R (image2 (fun m n => ↑(↑f m) n) ↑(span R {m}) ↑x✝) = map (↑f m) x✝
                                    -- ⊢ span R (image2 (fun m n => ↑(↑f m) n) ↑(span R {m}) ↑x✝) ≤ map (↑f m) x✝
  · rw [span_le, Set.image2_subset_iff]
    -- ⊢ ∀ (x : M), x ∈ ↑(span R {m}) → ∀ (y : N), y ∈ ↑x✝ → ↑(↑f x) y ∈ ↑(map (↑f m) …
    intro x hx y hy
    -- ⊢ ↑(↑f x) y ∈ ↑(map (↑f m) x✝)
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hx
    -- ⊢ ↑(↑f (a • m)) y ∈ ↑(map (↑f m) x✝)
    rw [f.map_smul]
    -- ⊢ ↑(a • ↑f m) y ∈ ↑(map (↑f m) x✝)
    exact smul_mem _ a (mem_map_of_mem hy)
    -- 🎉 no goals
  · rintro _ ⟨n, hn, rfl⟩
    -- ⊢ ↑(↑f m) n ∈ span R (image2 (fun m n => ↑(↑f m) n) ↑(span R {m}) ↑x✝)
    exact subset_span ⟨m, n, mem_span_singleton_self m, hn, rfl⟩
    -- 🎉 no goals
#align submodule.map₂_span_singleton_eq_map Submodule.map₂_span_singleton_eq_map

theorem map₂_span_singleton_eq_map_flip (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (n : N) :
    map₂ f s (span R {n}) = map (f.flip n) s := by rw [← map₂_span_singleton_eq_map, map₂_flip]
                                                   -- 🎉 no goals
#align submodule.map₂_span_singleton_eq_map_flip Submodule.map₂_span_singleton_eq_map_flip

end Submodule
