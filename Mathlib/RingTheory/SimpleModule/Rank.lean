import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A module over a division ring is simple iff it has rank one
-/

public section

theorem isSimpleModule_iff_finrank_eq_one {R M} [DivisionRing R] [AddCommGroup M] [Module R M] :
    IsSimpleModule R M ↔ Module.finrank R M = 1 :=
  ⟨fun h ↦ have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩
