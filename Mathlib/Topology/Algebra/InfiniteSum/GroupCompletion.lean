/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums and products in the completion of a topological group
-/

open UniformSpace.Completion

variable {α β : Type*} [CommGroup α] [UniformSpace α] [UniformGroup α]

/-- A function `f` has a product in an uniform group `α` if and only if it has that product in the
completion of `α`. -/
@[to_additive "A function `f` has a sum in an uniform additive group `α` if and only if it has that
sum in the completion of `α`."]
theorem hasProd_iff_hasProd_compl (f : β → α) (a : α):
    HasProd (toComplMulHom ∘ f) a ↔ HasProd f a := (denseInducing_toComplMulHom α).hasProd_iff f a

/-- A function `f` is multipliable in a uniform group `α` if and only if it is multipliable in
`Completion α` and its product in `Completion α` lies in the range of
`toComplMulHom : α →* Completion α`. -/
@[to_additive "A function `f` is summable in a uniform additive group `α` if and only if it is
summable in `Completion α` and its sum in `Completion α` lies in the range of
`toComplAddHom : α →+ Completion α`."]
theorem multipliable_iff_multipliable_compl_and_tprod_mem (f : β → α) :
    Multipliable f ↔ Multipliable (toComplMulHom ∘ f) ∧
      ∏' i, toComplMulHom (f i) ∈ Set.range toComplMulHom :=
  (denseInducing_toComplMulHom α).multipliable_iff_tprod_comp_mem_range f

/-- A function `f` is multipliable in a uniform group `α` if and only if the net of its partial
products is Cauchy and its product in `Completion α` lies in the range of
`toComplMulHom : α →* Completion α`. (The condition that the net of partial products is Cauchy can
be checked using `cauchySeq_finset_iff_prod_vanishing` or `cauchySeq_finset_iff_tprod_vanishing`.)
-/
@[to_additive "A function `f` is summable in a uniform additive group `α` if and only if the net of
its partial sums is Cauchy and its sum in `Completion α` lies in the range of
`toComplAddHom : α →+ Completion α`. (The condition that the net of partial sums is Cauchy can be checked
using `cauchySeq_finset_iff_sum_vanishing` or `cauchySeq_finset_iff_tsum_vanishing`.)"]
theorem multipliable_iff_cauchySeq_finset_and_tprod_mem (f : β → α) :
    Multipliable f ↔ CauchySeq (fun s : Finset β ↦ ∏ b in s, f b) ∧
      ∏' i, toComplMulHom (f i) ∈ Set.range toComplMulHom := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((multipliable_iff_multipliable_compl_and_tprod_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (multipliable_iff_multipliable_compl_and_tprod_mem f).mpr
    constructor
    · apply multipliable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← map_prod]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum

/-- If a function `f` is multipliable in a uniform group `α`, then its product in `α` is the same
as its product in `Completion α`. -/
@[to_additive "If a function `f` is summable in a uniform additive group `α`, then its sum in `α` is
the same as its sum in `Completion α`"]
theorem Multipliable.toCompl_tprod {f : β → α} (hf : Multipliable f) :
    ∏' i, toComplMulHom (f i) = ∏' i, f i :=
  (hf.map_tprod toComplMulHom (continuous_coe α)).symm
