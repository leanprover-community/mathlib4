import Mathlib.RingTheory.Ideal.Operations

namespace Submodule

-- TODO : Check where we use this:
-- These two lemmas are true, but they are usually not useful
-- It is rarely useful to write an element of the span as a linear combination
theorem mem_span_iff_exists_sum {R : Type _} [CommSemiring R] {M : Type _} [AddCommMonoid M]
    [Module R M] {ι : Type _} (f : ι → M) (x : M) :
    x ∈ span R (Set.range f) ↔ ∃ a : ι →₀ R, (a.sum fun (i : ι) (c : R) => c • f i) = x :=
  by
  rw [← top_smul (span R (Set.range f)), mem_ideal_smul_span_iff_exists_sum]
  exact exists_congr fun a => ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun i => mem_top, h⟩⟩
#align submodule.mem_span_iff_exists_sum Submodule.mem_span_iff_exists_sum

theorem mem_span_iff_exists_sum' {R : Type _} [CommSemiring R] {M : Type _} [AddCommMonoid M]
    [Module R M] {ι : Type _} (s : Set ι) (f : ι → M) (x : M) :
    x ∈ span R (f '' s) ↔ ∃ a : ↥s →₀ R, (a.sum fun (i : ↥s) (c : R) => c • f ↑i) = x :=
  by
  rw [← top_smul (span R (f '' s)), mem_ideal_smul_span_iff_exists_sum']
  apply exists_congr
  intro a
  constructor
  . rintro ⟨_, h⟩
    exact h
  . intro h
    simp only [mem_top, Subtype.forall, implies_true, exists_prop, true_and]
    exact h
#align submodule.mem_span_iff_exists_sum' Submodule.mem_span_iff_exists_sum'

theorem mem_span_set_iff_exists_sum {R : Type _} [CommSemiring R] {M : Type _} [AddCommMonoid M]
    [Module R M] (s : Set M) (x : M) :
    x ∈ span R s ↔ ∃ a : s →₀ R, ((a.sum fun (i : s) (c : R) => c • (i : M)) = x) :=
  by
  conv_lhs => rw [← Set.image_id s]
  rw [← top_smul (span R (id '' s)), mem_ideal_smul_span_iff_exists_sum']
  exact exists_congr fun a => ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun i => mem_top, h⟩⟩
#align submodule.mem_span_set_iff_exists_sum Submodule.mem_span_set_iff_exists_sum

end Submodule

