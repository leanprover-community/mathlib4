/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Categorical constructions for `IsSMulRegular`
-/

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Ideal Pointwise

lemma LinearMap.exact_smul_id_smul_top_mkQ (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (r • LinearMap.id : M →ₗ[R] M) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps]
def smulShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (QuotSMulTop r M)
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom (r • (⊤ : Submodule R M)).mkQ
  zero := by
    ext x
    exact (LinearMap.exact_smul_id_smul_top_mkQ M r).apply_apply_eq_zero x

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact := by
  simp [smulShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    LinearMap.exact_smul_id_smul_top_mkQ]

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using reg

section FromPR

namespace CategoryTheory.Abelian

open CategoryTheory.Abelian.Ext DerivedCategory

namespace Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Ring

variable (R : Type*) [Ring R] [Linear R C]

instance {X Y : C} (n : ℕ) : Module R (Ext.{w} X Y n) := sorry

noncomputable def homEquiv₀_linearHom {X Y : C} : Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  __ := addEquiv₀
  map_smul' := sorry

end Ring

section CommRing

variable (R : Type*) [CommRing R] [Linear R C]

noncomputable def bilinearCompOfLinear (X Y Z : C) (a b c : ℕ) (h : a + b = c) :
    Ext.{w} X Y a →ₗ[R] Ext.{w} Y Z b →ₗ[R] Ext.{w} X Z c where
  toFun α :=
    { toFun := fun β ↦ α.comp β h
      map_add' x y := by simp
      map_smul' := sorry }
  map_add' α β := by
    ext
    simp
  map_smul' := sorry

noncomputable def postcompOfLinear {Y Z : C} {a b n : ℕ} (f : Ext.{w} Y Z n) (X : C)
    (h : a + n = b) : Ext.{w} X Y a →ₗ[R] Ext.{w} X Z b :=
  (bilinearCompOfLinear R X Y Z a n b h).flip f

end CommRing

end Ext

end CategoryTheory.Abelian

end FromPR

lemma Submodule.smul_top_eq_comap_smul_top_of_surjective {R M M₂ : Type*} [CommSemiring R]
    [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂] (I : Ideal R) (f : M →ₗ[R] M₂)
    (h : Function.Surjective f) : I • ⊤ ⊔ (LinearMap.ker f) = comap f (I • ⊤) := by
  refine le_antisymm (sup_le (smul_top_le_comap_smul_top I f) (LinearMap.ker_le_comap f)) ?_
  rw [← Submodule.comap_map_eq f (I • (⊤ : Submodule R M)),
    Submodule.comap_le_comap_iff_of_surjective h,
    Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr h]

open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian Pointwise
variable {R : Type u} [CommRing R] [Small.{v} R] {M N : ModuleCat.{v} R} {n : ℕ}
  [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

lemma ext_hom_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    (AddCommGrp.ofHom <| ((Ext.mk₀ <| r • (𝟙 M))).postcomp N (add_zero n)) = 0 := by
  ext h
  have : (((Ext.homEquiv₀_linearHom R).symm (r • 𝟙 M)).postcompOfLinear R N (add_zero n)) h =
    0 := by
    have : r • (𝟙 N) = 0 := ModuleCat.hom_ext
      (LinearMap.ext (fun x ↦ Module.mem_annihilator.mp mem_ann _))
    have : r • (Ext.bilinearCompOfLinear R N N M 0 n n (zero_add n)).flip
      h ((Ext.homEquiv₀_linearHom R).symm (𝟙 N)) = 0 := by
      rw [← map_smul, ← map_smul, this]
      simp
    have : r • h = 0 := by rwa [← Ext.mk₀_id_comp h]
    simpa [Ext.postcompOfLinear, Ext.bilinearCompOfLinear, Ext.homEquiv₀_linearHom]
  simpa only [AddCommGrp.hom_ofHom, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply,
    AddCommGrp.hom_zero, AddMonoidHom.zero_apply]
