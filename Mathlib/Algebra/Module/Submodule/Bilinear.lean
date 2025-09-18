/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Images of pairs of submodules under bilinear maps

This file provides `Submodule.map₂`, which is later used to implement `Submodule.mul`.

## Main results

* `Submodule.map₂_eq_span_image2`: the image of two submodules under a bilinear map is the span of
  their `Set.image2`.

## Notes

This file is quite similar to the n-ary section of `Data.Set.Basic` and to `Order.Filter.NAry`.
Please keep them in sync.

## TODO

Generalize this file to semilinear maps.
-/


universe uι u v

open Set

open Pointwise

namespace Submodule

variable {ι : Sort uι} {R M N P : Type*}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]

/-- Map a pair of submodules under a bilinear map.

This is the submodule version of `Set.image2`. -/
def map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) : Submodule R P :=
  ⨆ s : p, q.map (f s)

theorem apply_mem_map₂ (f : M →ₗ[R] N →ₗ[R] P) {m : M} {n : N} {p : Submodule R M}
    {q : Submodule R N} (hm : m ∈ p) (hn : n ∈ q) : f m n ∈ map₂ f p q :=
  (le_iSup _ ⟨m, hm⟩ : _ ≤ map₂ f p q) ⟨n, hn, by rfl⟩

theorem map₂_le {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q : Submodule R N}
    {r : Submodule R P} : map₂ f p q ≤ r ↔ ∀ m ∈ p, ∀ n ∈ q, f m n ∈ r :=
  ⟨fun H _m hm _n hn => H <| apply_mem_map₂ _ hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩

variable (R) in
theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : Set M) (t : Set N) :
    map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n => f m n) s t) := by
  apply le_antisymm
  · rw [map₂_le]
    apply @span_induction R M _ _ _ s
    on_goal 1 =>
      intro a ha
      apply @span_induction R N _ _ _ t
      · intro b hb
        exact subset_span ⟨_, ‹_›, _, ‹_›, rfl⟩
    all_goals
      intros
      simp only [*, add_mem, smul_mem, zero_mem, map_zero, map_add,
        LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply, map_smul]
  · rw [span_le, image2_subset_iff]
    intro a ha b hb
    exact apply_mem_map₂ _ (subset_span ha) (subset_span hb)
@[simp]
theorem map₂_bot_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) : map₂ f p ⊥ = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m _hm n hn => by
      rw [Submodule.mem_bot] at hn
      rw [hn, LinearMap.map_zero]; simp only [mem_bot]

@[simp]
theorem map₂_bot_left (f : M →ₗ[R] N →ₗ[R] P) (q : Submodule R N) : map₂ f ⊥ q = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m hm n _ => by
      rw [Submodule.mem_bot] at hm ⊢
      rw [hm, LinearMap.map_zero₂]

@[gcongr, mono]
theorem map₂_le_map₂ {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q₁ q₂ : Submodule R N}
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) : map₂ f p₁ q₁ ≤ map₂ f p₂ q₂ :=
  map₂_le.2 fun _m hm _n hn => apply_mem_map₂ _ (hp hm) (hq hn)

theorem map₂_le_map₂_left {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q : Submodule R N}
    (h : p₁ ≤ p₂) : map₂ f p₁ q ≤ map₂ f p₂ q :=
  map₂_le_map₂ h (le_refl q)

theorem map₂_le_map₂_right {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q₁ q₂ : Submodule R N}
    (h : q₁ ≤ q₂) : map₂ f p q₁ ≤ map₂ f p q₂ :=
  map₂_le_map₂ (le_refl p) h

theorem map₂_sup_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q₁ q₂ : Submodule R N) :
    map₂ f p (q₁ ⊔ q₂) = map₂ f p q₁ ⊔ map₂ f p q₂ :=
  le_antisymm
    (map₂_le.2 fun _m hm _np hnp =>
      let ⟨_n, hn, _p, hp, hnp⟩ := mem_sup.1 hnp
      mem_sup.2 ⟨_, apply_mem_map₂ _ hm hn, _, apply_mem_map₂ _ hm hp, hnp ▸ (map_add _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_right le_sup_left) (map₂_le_map₂_right le_sup_right))

theorem map₂_sup_left (f : M →ₗ[R] N →ₗ[R] P) (p₁ p₂ : Submodule R M) (q : Submodule R N) :
    map₂ f (p₁ ⊔ p₂) q = map₂ f p₁ q ⊔ map₂ f p₂ q :=
  le_antisymm
    (map₂_le.2 fun _mn hmn _p hp =>
      let ⟨_m, hm, _n, hn, hmn⟩ := mem_sup.1 hmn
      mem_sup.2
        ⟨_, apply_mem_map₂ _ hm hp, _, apply_mem_map₂ _ hn hp,
          hmn ▸ (LinearMap.map_add₂ _ _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_left le_sup_left) (map₂_le_map₂_left le_sup_right))

theorem image2_subset_map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    Set.image2 (fun m n => f m n) (↑p : Set M) (↑q : Set N) ⊆ (↑(map₂ f p q) : Set P) := by
  rintro _ ⟨i, hi, j, hj, rfl⟩
  exact apply_mem_map₂ _ hi hj

theorem map₂_eq_span_image2 (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f p q = span R (Set.image2 (fun m n => f m n) (p : Set M) (q : Set N)) := by
  rw [← map₂_span_span, span_eq, span_eq]

theorem map₂_flip (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f.flip q p = map₂ f p q := by
  rw [map₂_eq_span_image2, map₂_eq_span_image2, Set.image2_swap]
  rfl

theorem map₂_iSup_left (f : M →ₗ[R] N →ₗ[R] P) (s : ι → Submodule R M) (t : Submodule R N) :
    map₂ f (⨆ i, s i) t = ⨆ i, map₂ f (s i) t := by
  suffices map₂ f (⨆ i, span R (s i : Set M)) (span R t) = ⨆ i, map₂ f (span R (s i)) (span R t) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_iUnion, map₂_span_span, Set.image2_iUnion_left]

theorem map₂_iSup_right (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (t : ι → Submodule R N) :
    map₂ f s (⨆ i, t i) = ⨆ i, map₂ f s (t i) := by
  suffices map₂ f (span R s) (⨆ i, span R (t i : Set N)) = ⨆ i, map₂ f (span R s) (span R (t i)) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_iUnion, map₂_span_span, Set.image2_iUnion_right]

theorem map₂_span_singleton_eq_map (f : M →ₗ[R] N →ₗ[R] P) (m : M) :
    map₂ f (span R {m}) = map (f m) := by
  funext s
  rw [← span_eq s, map₂_span_span, image2_singleton_left, map_span]

theorem map₂_span_singleton_eq_map_flip (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (n : N) :
    map₂ f s (span R {n}) = map (f.flip n) s := by rw [← map₂_span_singleton_eq_map, map₂_flip]

section comp
variable {M₂ N₂ P₂ : Type*}
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂]
variable [Module R M₂] [Module R N₂] [Module R P₂]

theorem map_map₂ (f : P →ₗ[R] P₂) (g : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map f (map₂ g p q) = map₂ (g.compr₂ f) p q :=
  map_iSup _ _ |>.trans <| iSup_congr fun _ => map_comp _ _ _ |>.symm

theorem map₂_map_right
    (f : M →ₗ[R] N₂ →ₗ[R] P) (g : N →ₗ[R] N₂) (p : Submodule R M) (q : Submodule R N) :
    map₂ f p (map g q) = map₂ (f.compl₂ g) p q :=
  iSup_congr fun _ => map_comp _ _ _ |>.symm

theorem map₂_map_left
    (f : M₂ →ₗ[R] N →ₗ[R] P) (g : M →ₗ[R] M₂) (p : Submodule R M) (q : Submodule R N) :
    map₂ f (map g p) q = map₂ (f ∘ₗ g) p q := by
  rw [← map₂_flip, map₂_map_right, ← map₂_flip]
  rfl

theorem map₂_map_map
    (f : M₂ →ₗ[R] N₂ →ₗ[R] P) (g : M →ₗ[R] M₂) (h : N →ₗ[R] N₂)
    (p : Submodule R M) (q : Submodule R N) :
    map₂ f (map g p) (map h q) = map₂ (f.compl₁₂ g h) p q := by
  rw [map₂_map_right, map₂_map_left]
  rfl

end comp

end Submodule
