-- import Mathlib.Algebra.Module.Equiv
-- import Init.Prelude
import Init.Tactics
-- abbrev SemilinearAut (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]: Type _ :=
--     (σ:RingAut R) × (
--       letI inst := RingHomInvPair.of_ringEquiv σ;
--       letI := inst.symm;
--       M ≃ₛₗ[(σ : R →+* R)] M)


-- def SemilinearAut.mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {σ σ': R →+* R}
--     [i1:RingHomInvPair σ σ'] [i2:RingHomInvPair σ' σ] (f: M ≃ₛₗ[σ] M) : SemilinearAut R M :=
--   ⟨RingEquiv.ofHomInv σ σ' i2.comp_eq₂ i1.comp_eq₂, f⟩

theorem congrDep
  (A : Type) (T : A → Type) (f g : (a : A) → T a) (x y : A)
  (hfg : f = g) (hxy : x = y) (hT : T x = T y) : f x = hT ▸ (g y) := by
  subst hxy
  subst hfg
  rfl
