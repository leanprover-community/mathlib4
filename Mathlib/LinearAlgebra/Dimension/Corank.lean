/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Corank of a submodule

For a submodule `p : Submodule R M`, its `corank` is the rank of the quotient
`M ⧸ p`.
-/

public section

universe u v w

variable {R M N : Type*}

namespace Submodule

variable [Ring R] [AddCommGroup M] [Module R M]

/-- The corank of a submodule `p` is the rank of the quotient `M ⧸ p`. -/
noncomputable def corank (p : Submodule R M) : Cardinal :=
  Module.rank R (M ⧸ p)

theorem corank_def (p : Submodule R M) :
    p.corank = Module.rank R (M ⧸ p) :=
  by rfl

/-- The corank of a submodule is at most the rank of the ambient module. -/
theorem corank_le (p : Submodule R M) :
    p.corank ≤ Module.rank R M := by
  simpa [corank] using rank_quotient_le p

theorem corank_anti {p q : Submodule R M} (h : p ≤ q) :
    q.corank ≤ p.corank := by
  simpa [corank] using (factor h).rank_le_of_surjective (factor_surjective h)

theorem corank_antitone :
    Antitone (corank : Submodule R M → Cardinal) :=
  fun _ _ => corank_anti

@[simp]
theorem corank_bot : (⊥ : Submodule R M).corank = Module.rank R M := by
  simpa [corank] using ((⊥ : Submodule R M).quotEquivOfEqBot rfl).rank_eq

@[simp]
theorem corank_top [Nontrivial R] : (⊤ : Submodule R M).corank = 0 := by
  rw [corank, rank_eq_zero_iff]
  exact fun _ => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩

end Submodule

namespace LinearEquiv

variable [Ring R]

variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Two linearly equivalent modules have the same corank, a version with different universes. -/
theorem lift_corank_map_eq (e : M ≃ₗ[R] N) (p : Submodule R M) :
    Cardinal.lift.{v, w} (p.map (e : M →ₗ[R] N)).corank =
      Cardinal.lift.{w, v} p.corank := by
  exact (Submodule.Quotient.equiv p (p.map (e : M →ₗ[R] N)) e rfl).lift_rank_eq.symm

variable {M N : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Two linearly equivalent modules have the same corank. -/
theorem corank_map_eq (e : M ≃ₗ[R] N) (p : Submodule R M) :
    (p.map (e : M →ₗ[R] N)).corank = p.corank := by
  exact (Submodule.Quotient.equiv p (p.map (e : M →ₗ[R] N)) e rfl).rank_eq.symm

end LinearEquiv

namespace Submodule

-- # Rank Nullity

variable {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]
variable [HasRankNullity.{v} R]

theorem corank_add_rank (p : Submodule R M) :
    p.corank + Module.rank R p = Module.rank R M := by
  simpa [corank] using rank_quotient_add_rank p

/-- The submodule `q.map p.mkQ` of `M ⧸ p` represents the relative quotient
`q / p`. This theorem says that the corank drops, from `p` to `q`, by the
rank of `q / p`.
-/
theorem corank_add_rank_quotient {p q : Submodule R M} (h : p ≤ q) :
    q.corank + Module.rank R (q.map p.mkQ) = p.corank := by
  change Module.rank R (M ⧸ q) + Module.rank R (q.map p.mkQ) = Module.rank R (M ⧸ p)
  rw [← (p.quotientQuotientEquivQuotient q h).rank_eq]
  exact rank_quotient_add_rank (q.map p.mkQ)

end Submodule
