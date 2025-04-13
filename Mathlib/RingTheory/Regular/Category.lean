/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.QuotSMulTop

/-!
# The categorical constructions for IsSMulRegular
-/

universe u

namespace CategoryTheory

theorem subsingleton_of_subsingleton_subsingleton {C : ShortComplex AddCommGrp.{u}} (h : C.Exact)
    (h0 : Subsingleton C.X₁) (h2 : Subsingleton C.X₃) : Subsingleton C.X₂ := by
  rw [CategoryTheory.ShortComplex.ab_exact_iff] at h
  suffices h : ∀ a : C.X₂, a = 0 from subsingleton_of_forall_eq 0 h
  intro a
  obtain ⟨b, hb⟩ := h a (@Subsingleton.elim _ h2 _ 0)
  rw [show b = 0 from (@Subsingleton.elim _ h0 _ 0), map_zero] at hb
  exact hb.symm

lemma ComposableArrows.Exact.isIso_map' {C : Type*} [Category C] [Preadditive C]
    [Balanced C] {n : ℕ} {S : ComposableArrows C n} (hS : S.Exact) (k : ℕ) (hk : k + 3 ≤ n)
    (h₀ : S.map' k (k + 1) = 0) (h₁ : S.map' (k + 2) (k + 3) = 0) :
    IsIso (S.map' (k + 1) (k + 2)) := by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

end CategoryTheory

universe v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Ideal Pointwise

/-- The short complex `M → M → M⧸xM` given by an element `x : R`. -/
@[simps]
def SMul_ShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (QuotSMulTop r M)
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom (r • (⊤ : Submodule R M)).mkQ
  zero := by
    ext m
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, Submodule.mkQ_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul m r ⊤ trivial

lemma SMul_ShortComplex_exact (r : R) : (SMul_ShortComplex M r).Exact := by
  simp only [SMul_ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ModuleCat.hom_ofHom]
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.ideal_span_singleton_smul r ⊤,
    Submodule.mem_smul_pointwise_iff_exists]

instance SMul_ShortComplex_g_epi (r : R) : Epi (SMul_ShortComplex M r).g := by
  simpa [SMul_ShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

variable {M} in
lemma IsSMulRegular.SMul_ShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (SMul_ShortComplex M r).ShortExact where
  exact := SMul_ShortComplex_exact M r
  mono_f := by simpa [SMul_ShortComplex, ModuleCat.mono_iff_injective] using reg
