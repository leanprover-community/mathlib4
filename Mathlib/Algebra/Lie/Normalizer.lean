/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Algebra.Lie.Quotient

#align_import algebra.lie.normalizer from "leanprover-community/mathlib"@"938fead7abdc0cbbca8eba7a1052865a169dc102"

/-!
# The normalizer of Lie submodules and subalgebras.

Given a Lie module `M` over a Lie subalgebra `L`, the normalizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the normalizer: `N ↦ N.normalizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the normalizer. This turns out to be a Lie subalgebra.

## Main definitions

  * `LieSubmodule.normalizer`
  * `LieSubalgebra.normalizer`
  * `LieSubmodule.gc_top_lie_normalizer`

## Tags

lie algebra, normalizer
-/


variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

/-- The normalizer of a Lie submodule. -/
def normalizer : LieSubmodule R L M where
  carrier := {m | ∀ x : L, ⁅x, m⁆ ∈ N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
                           -- ⊢ ⁅x, a✝⁆ + ⁅x, b✝⁆ ∈ N
                                         -- 🎉 no goals
  zero_mem' x := by simp
                    -- 🎉 no goals
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
                           -- ⊢ t • ⁅x, m⁆ ∈ N
                                          -- 🎉 no goals
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))
                           -- ⊢ ⁅⁅y, x⁆, m⁆ + ⁅x, ⁅y, m⁆⁆ ∈ N
                                             -- 🎉 no goals
#align lie_submodule.normalizer LieSubmodule.normalizer

@[simp]
theorem mem_normalizer (m : M) : m ∈ N.normalizer ↔ ∀ x : L, ⁅x, m⁆ ∈ N :=
  Iff.rfl
#align lie_submodule.mem_normalizer LieSubmodule.mem_normalizer

theorem le_normalizer : N ≤ N.normalizer := by
  intro m hm
  -- ⊢ m ∈ normalizer N
  rw [mem_normalizer]
  -- ⊢ ∀ (x : L), ⁅x, m⁆ ∈ N
  exact fun x => N.lie_mem hm
  -- 🎉 no goals
#align lie_submodule.le_normalizer LieSubmodule.le_normalizer

theorem normalizer_inf : (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer := by
  ext; simp [← forall_and]
  -- ⊢ m✝ ∈ normalizer (N₁ ⊓ N₂) ↔ m✝ ∈ normalizer N₁ ⊓ normalizer N₂
       -- 🎉 no goals
#align lie_submodule.normalizer_inf LieSubmodule.normalizer_inf

@[mono]
theorem monotone_normalizer : Monotone (normalizer : LieSubmodule R L M → LieSubmodule R L M) := by
  intro N₁ N₂ h m hm
  -- ⊢ m ∈ normalizer N₂
  rw [mem_normalizer] at hm ⊢
  -- ⊢ ∀ (x : L), ⁅x, m⁆ ∈ N₂
  exact fun x => h (hm x)
  -- 🎉 no goals
#align lie_submodule.monotone_normalizer LieSubmodule.monotone_normalizer

@[simp]
theorem comap_normalizer (f : M' →ₗ⁅R,L⁆ M) : N.normalizer.comap f = (N.comap f).normalizer := by
  ext; simp
  -- ⊢ m✝ ∈ comap f (normalizer N) ↔ m✝ ∈ normalizer (comap f N)
       -- 🎉 no goals
#align lie_submodule.comap_normalizer LieSubmodule.comap_normalizer

theorem top_lie_le_iff_le_normalizer (N' : LieSubmodule R L M) :
    ⁅(⊤ : LieIdeal R L), N⁆ ≤ N' ↔ N ≤ N'.normalizer := by rw [lie_le_iff]; tauto
                                                           -- ⊢ (∀ (x : L), x ∈ ⊤ → ∀ (m : M), m ∈ N → ⁅x, m⁆ ∈ N') ↔ N ≤ normalizer N'
                                                                            -- 🎉 no goals
#align lie_submodule.top_lie_le_iff_le_normalizer LieSubmodule.top_lie_le_iff_le_normalizer

theorem gc_top_lie_normalizer :
    GaloisConnection (fun N : LieSubmodule R L M => ⁅(⊤ : LieIdeal R L), N⁆) normalizer :=
  top_lie_le_iff_le_normalizer
#align lie_submodule.gc_top_lie_normalizer LieSubmodule.gc_top_lie_normalizer

variable (R L M)

theorem normalizer_bot_eq_maxTrivSubmodule :
    (⊥ : LieSubmodule R L M).normalizer = LieModule.maxTrivSubmodule R L M :=
  rfl
#align lie_submodule.normalizer_bot_eq_max_triv_submodule LieSubmodule.normalizer_bot_eq_maxTrivSubmodule

end LieSubmodule

namespace LieSubalgebra

variable (H : LieSubalgebra R L)

/-- Regarding a Lie subalgebra `H ⊆ L` as a module over itself, its normalizer is in fact a Lie
subalgebra. -/
def normalizer : LieSubalgebra R L :=
  { H.toLieSubmodule.normalizer with
    lie_mem' := fun {y z} hy hz x => by
      rw [coe_bracket_of_module, mem_toLieSubmodule, leibniz_lie, ← lie_skew y, ← sub_eq_add_neg]
      -- ⊢ ⁅⁅↑x, y⁆, z⁆ - ⁅⁅↑x, z⁆, y⁆ ∈ H
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }
      -- 🎉 no goals
#align lie_subalgebra.normalizer LieSubalgebra.normalizer

theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y, x⁆ ∈ H := by
  rw [Subtype.forall']; rfl
  -- ⊢ x ∈ normalizer H ↔ ∀ (x_1 : { a // a ∈ H }), ⁅↑x_1, x⁆ ∈ H
                        -- 🎉 no goals
#align lie_subalgebra.mem_normalizer_iff' LieSubalgebra.mem_normalizer_iff'

theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x, y⁆ ∈ H := by
  rw [mem_normalizer_iff']
  -- ⊢ (∀ (y : L), y ∈ H → ⁅y, x⁆ ∈ H) ↔ ∀ (y : L), y ∈ H → ⁅x, y⁆ ∈ H
  refine' forall₂_congr fun y hy => _
  -- ⊢ ⁅y, x⁆ ∈ H ↔ ⁅x, y⁆ ∈ H
  rw [← lie_skew, neg_mem_iff (G := L)]
  -- 🎉 no goals
#align lie_subalgebra.mem_normalizer_iff LieSubalgebra.mem_normalizer_iff

theorem le_normalizer : H ≤ H.normalizer :=
  H.toLieSubmodule.le_normalizer
#align lie_subalgebra.le_normalizer LieSubalgebra.le_normalizer

theorem coe_normalizer_eq_normalizer :
    (H.toLieSubmodule.normalizer : Submodule R L) = H.normalizer :=
  rfl
#align lie_subalgebra.coe_normalizer_eq_normalizer LieSubalgebra.coe_normalizer_eq_normalizer

variable {H}

theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x ∈ H.normalizer) (hy : y ∈ (R ∙ x) ⊔ ↑H)
    (hz : z ∈ (R ∙ x) ⊔ ↑H) : ⁅y, z⁆ ∈ (R ∙ x) ⊔ ↑H := by
  rw [Submodule.mem_sup] at hy hz
  -- ⊢ ⁅y, z⁆ ∈ Submodule.span R {x} ⊔ H.toSubmodule
  obtain ⟨u₁, hu₁, v, hv : v ∈ H, rfl⟩ := hy
  -- ⊢ ⁅u₁ + v, z⁆ ∈ Submodule.span R {x} ⊔ H.toSubmodule
  obtain ⟨u₂, hu₂, w, hw : w ∈ H, rfl⟩ := hz
  -- ⊢ ⁅u₁ + v, u₂ + w⁆ ∈ Submodule.span R {x} ⊔ H.toSubmodule
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  -- ⊢ ⁅t • x + v, u₂ + w⁆ ∈ Submodule.span R {x} ⊔ H.toSubmodule
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
  -- ⊢ ⁅t • x + v, s • x + w⁆ ∈ Submodule.span R {x} ⊔ H.toSubmodule
  apply Submodule.mem_sup_right
  -- ⊢ ⁅t • x + v, s • x + w⁆ ∈ H.toSubmodule
  simp only [LieSubalgebra.mem_coe_submodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine' H.add_mem (H.smul_mem s _) (H.add_mem (H.smul_mem t _) (H.lie_mem hv hw))
  -- ⊢ ⁅v, x⁆ ∈ H
  exacts [(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]
  -- 🎉 no goals
#align lie_subalgebra.lie_mem_sup_of_mem_normalizer LieSubalgebra.lie_mem_sup_of_mem_normalizer

/-- A Lie subalgebra is an ideal of its normalizer. -/
theorem ideal_in_normalizer {x y : L} (hx : x ∈ H.normalizer) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [← lie_skew, neg_mem_iff (G := L)]
  -- ⊢ ⁅y, x⁆ ∈ H
  exact hx ⟨y, hy⟩
  -- 🎉 no goals
#align lie_subalgebra.ideal_in_normalizer LieSubalgebra.ideal_in_normalizer

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
theorem exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K)
    (h₂ : K ≤ H.normalizer) : ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  -- ⊢ ∀ (x y : L), x ∈ K → y ∈ H → ⁅x, y⁆ ∈ H
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy
  -- 🎉 no goals
#align lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer

variable (H)

theorem normalizer_eq_self_iff :
    H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  -- ⊢ normalizer H = H ↔ ∀ (m : L ⧸ toLieSubmodule H), m ∈ LieModule.maxTrivSubmod …
  refine' ⟨fun h => _, fun h => le_antisymm _ H.le_normalizer⟩
  -- ⊢ ∀ (m : L ⧸ toLieSubmodule H), m ∈ LieModule.maxTrivSubmodule R { x // x ∈ H  …
  · rintro ⟨x⟩ hx
    -- ⊢ Quot.mk Setoid.r x = 0
    suffices x ∈ H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_coe_submodule]
    rw [← h, H.mem_normalizer_iff']
    -- ⊢ ∀ (y : L), y ∈ H → ⁅y, x⁆ ∈ H
    intro y hy
    -- ⊢ ⁅y, x⁆ ∈ H
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    -- ⊢ ⁅y, x⁆ ∈ H
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
    -- 🎉 no goals
  · intro x hx
    -- ⊢ x ∈ H
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    -- ⊢ x ∈ H
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module,
        Submodule.coe_mk, mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa using h y hy
    -- 🎉 no goals
#align lie_subalgebra.normalizer_eq_self_iff LieSubalgebra.normalizer_eq_self_iff

end LieSubalgebra
