/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalProperties

#align_import ring_theory.ring_hom.surjective from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!

# The meta properties of surjective ring homomorphisms.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

local notation "surjective" => fun {X Y : Type _} [CommRing X] [CommRing Y] => fun f : X →+* Y =>
  Function.Surjective f

theorem surjective_stableUnderComposition : StableUnderComposition surjective := by
  introv R hf hg; exact hg.comp hf
  -- ⊢ Function.Surjective ↑(comp g f)
                  -- 🎉 no goals
#align ring_hom.surjective_stable_under_composition RingHom.surjective_stableUnderComposition

theorem surjective_respectsIso : RespectsIso surjective := by
  apply surjective_stableUnderComposition.respectsIso
  -- ⊢ ∀ {R S : Type u_1} [inst : CommRing R] [inst_1 : CommRing S] (e : R ≃+* S),  …
  intros _ _ _ _ e
  -- ⊢ Function.Surjective ↑(RingEquiv.toRingHom e)
  exact e.surjective
  -- 🎉 no goals
#align ring_hom.surjective_respects_iso RingHom.surjective_respectsIso

theorem surjective_stableUnderBaseChange : StableUnderBaseChange surjective := by
  refine' StableUnderBaseChange.mk _ surjective_respectsIso _
  -- ⊢ ∀ ⦃R S T : Type u_1⦄ [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Com …
  classical
  introv h x
  skip
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨y, rfl⟩ := h y; use y • x; dsimp
    rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y ex ey => obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ex, ey; exact ⟨x + y, map_add _ x y⟩
#align ring_hom.surjective_stable_under_base_change RingHom.surjective_stableUnderBaseChange

open scoped BigOperators

theorem surjective_ofLocalizationSpan : OfLocalizationSpan surjective := by
  introv R hs H
  -- ⊢ Function.Surjective ↑f
  skip
  -- ⊢ Function.Surjective ↑f
  letI := f.toAlgebra
  -- ⊢ Function.Surjective ↑f
  show Function.Surjective (Algebra.ofId R S)
  -- ⊢ Function.Surjective ↑(Algebra.ofId R S)
  rw [← Algebra.range_top_iff_surjective, eq_top_iff]
  -- ⊢ ⊤ ≤ AlgHom.range (Algebra.ofId R S)
  rintro x -
  -- ⊢ x ∈ AlgHom.range (Algebra.ofId R S)
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_total R s 1).mp (show _ ∈ Ideal.span s by rw [hs]; trivial)
  fapply
    Subalgebra.mem_of_finset_sum_eq_one_of_pow_smul_mem _ l.support (fun x : s => f x) fun x : s =>
      f (l x)
  · dsimp only; simp_rw [← _root_.map_mul, ← map_sum, ← f.map_one]; exact f.congr_arg hl
    -- ⊢ ∑ i in l.support, ↑f (↑l i) * ↑f ↑i = 1
                -- ⊢ ↑f (∑ x in l.support, ↑l x * ↑x) = ↑f 1
                                                                    -- 🎉 no goals
  · exact fun _ => Set.mem_range_self _
    -- 🎉 no goals
  · exact fun _ => Set.mem_range_self _
    -- 🎉 no goals
  · intro r
    -- ⊢ ∃ n, ↑f ↑r ^ n • x ∈ AlgHom.range (Algebra.ofId R S)
    obtain ⟨y, hy⟩ := H r (IsLocalization.mk' _ x (1 : Submonoid.powers (f r)))
    -- ⊢ ∃ n, ↑f ↑r ^ n • x ∈ AlgHom.range (Algebra.ofId R S)
    obtain ⟨z, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r : R)) y
    -- ⊢ ∃ n, ↑f ↑r ^ n • x ∈ AlgHom.range (Algebra.ofId R S)
    erw [IsLocalization.map_mk', IsLocalization.eq] at hy
    -- ⊢ ∃ n, ↑f ↑r ^ n • x ∈ AlgHom.range (Algebra.ofId R S)
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hy
    -- ⊢ ∃ n, ↑f ↑r ^ n • x ∈ AlgHom.range (Algebra.ofId R S)
    refine' ⟨m + n, _⟩
    -- ⊢ ↑f ↑r ^ (m + n) • x ∈ AlgHom.range (Algebra.ofId R S)
    dsimp at hm ⊢
    -- ⊢ ↑f ↑r ^ (m + n) * x ∈ AlgHom.range (Algebra.ofId R S)
    simp_rw [_root_.one_mul, ← _root_.mul_assoc, ← map_pow, ← f.map_mul, ← pow_add, map_pow] at hm
    -- ⊢ ↑f ↑r ^ (m + n) * x ∈ AlgHom.range (Algebra.ofId R S)
    exact ⟨_, hm⟩
    -- 🎉 no goals
#align ring_hom.surjective_of_localization_span RingHom.surjective_ofLocalizationSpan

end RingHom
