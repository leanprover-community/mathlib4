import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Tactic.LibrarySearch

set_option pp.unicode.fun true

-- TODO: uses sorry, but is hidden behind the `apply?`
/--
info: Try this: refine IsCompact.exists_forall_le _hK ?ne_s ?hf
---
info: Try this: refine ex_of_PSigma ?a✝
---
info: Try this: refine Iff.mp Set.nonempty_def ?a✝
---
info: Try this: refine Iff.mp Set.inter_nonempty ?a✝
---
info: Try this: refine Iff.mp Set.not_disjoint_iff ?a✝
---
info: Try this: refine ex_of_psig ?a✝
---
info: Try this: refine Iff.mp not_forall_not ?a✝
---
info: Try this: refine Iff.mp bex_def ?a✝
---
info: Try this: refine Iff.mp Filter.frequently_principal ?a✝
---
info: Try this: refine Iff.mp Set.inter_nonempty_iff_exists_left ?a✝
---
info: Try this: refine Iff.mp Set.inter_nonempty_iff_exists_right ?a✝
---
info: Try this: refine ExistsUnique.exists ?a✝
---
info: Try this: refine Iff.mp nonempty_subtype ?a✝
---
info: Try this: refine Iff.mp Filter.frequently_top ?a✝
---
info: Try this: refine Subtype.existsOfSubtype ?a✝
---
info: Try this: refine Set.exists_min_image K (fun a ↦ f a) ?h1 ?a✝
---
info: Try this: refine Iff.mpr IsEmpty.exists_iff ?a✝
---
info: Try this: refine Exists.intro ?w ?h
---
info: Try this: refine exists_of_bex ?a✝
---
info: Try this: refine Filter.Tendsto.exists_within_forall_le ?hs ?hf
---
info: Try this: refine Iff.mpr Unique.exists_iff ?a✝
---
info: Try this: refine Iff.mp exists_unique_iff_exists ?a✝
---
info: Try this: refine Filter.Frequently.exists ?hp
---
info: Try this: refine Iff.mp Decidable.not_forall_not ?a✝
---
info: Try this: refine Iff.mp (exists_congr ?h) ?a✝
---
info: Try this: refine Exists.imp ?h ?a✝
---
info: Try this: refine Iff.mp (exists_ge_and_iff_exists ?hP) ?a✝
---
info: Try this: refine Filter.Eventually.exists ?hp
---
info: Try this: refine Iff.mpr (Equiv.exists_congr_left ?f) ?a✝
---
info: Try this: refine ?self.nonempty
---
info: Try this: refine Dense.exists_mem_open ?hs ?ho ?hne
---
info: Try this: refine Iff.mpr (exists_congr ?h) ?a✝
---
info: Try this: refine Iff.mp (exists_le_and_iff_exists ?hP) ?a✝
---
info: Try this: refine Filter.HasBasis.ex_mem ?h
---
info: Try this: refine Iff.mpr (Function.Surjective.exists ?hf) ?a✝
---
info: Try this: refine ContinuousOn.exists_forall_le' ?hf ?hsc ?h₀ ?hc
---
info: Try this: refine Exists.imp' ?f ?hpq ?a✝
-/
#guard_msgs(info) in
example (f : ℝ → ℝ) {K : Set ℝ} (_hK : IsCompact K) : ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  fail_if_success exact?
  apply? -- Verify that this includes: `refine IsCompact.exists_forall_le _hK ?_ ?_`
