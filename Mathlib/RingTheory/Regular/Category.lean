/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.HasEnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The categorical constructions for IsSMulRegular
-/

universe u v w

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

section FromPR

namespace CategoryTheory.Abelian

open CategoryTheory.Abelian.Ext DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (X Y : C)

namespace Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section Ring

variable (R : Type*) [Ring R] [Linear R C]

instance {X Y : C} (n : ℕ): Module R (Ext.{w} X Y n) := sorry

noncomputable def homEquiv₀_linearHom {X Y : C} : Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  __ := addEquiv₀
  map_smul' := sorry

end Ring

section CommRing

variable (R : Type*) [CommRing R]

noncomputable def bilinearCompOfLinear [Linear R C] (X Y Z : C) (a b c : ℕ) (h : a + b = c) :
    Ext.{w} X Y a →ₗ[R] Ext.{w} Y Z b →ₗ[R] Ext.{w} X Z c where
  toFun α :=
    { toFun := fun β ↦ α.comp β h
      map_add' x y := by simp
      map_smul' := sorry }
  map_add' α β := by
    ext
    simp
  map_smul' := sorry

noncomputable def postcompOfLinear [Linear R C] {Y Z : C} {a b n : ℕ} (f : Ext.{w} Y Z n) (X : C)
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
  apply congrArg AddCommGrp.ofHom <| AddMonoidHom.ext fun h ↦ ?_
  show (((Ext.homEquiv₀_linearHom R).symm (r • 𝟙 M)).postcompOfLinear R N _) h = 0
  simp only [Ext.postcompOfLinear, Ext.bilinearCompOfLinear, Ext.homEquiv₀_linearHom,
    AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, map_smul, LinearEquiv.coe_symm_mk, Ext.addEquiv₀_symm_apply,
    LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, Ext.comp_mk₀_id]
  rw [← Ext.mk₀_id_comp h]
  show r • (Ext.bilinearCompOfLinear R N N M 0 n n (zero_add n)).flip
    h ((Ext.homEquiv₀_linearHom R).symm (𝟙 N)) = 0
  have : r • (𝟙 N) = 0 := by
    ext
    exact Module.mem_annihilator.mp mem_ann _
  rw [← map_smul, ← map_smul, this]
  simp
