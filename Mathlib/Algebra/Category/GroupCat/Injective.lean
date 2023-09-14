/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Module.Injective
import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Rat
import Mathlib.LinearAlgebra.Isomorphisms

#align_import algebra.category.Group.injective from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups and that the category of abelian groups has enough injective objects.

-/


open CategoryTheory

open Pointwise

universe u

variable (A : Type u) [AddCommGroup A]

set_option linter.uppercaseLean3 false

namespace AddCommGroupCat

theorem injective_of_injective_as_module [Injective (⟨A⟩ : ModuleCat ℤ)] :
    CategoryTheory.Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  { factors := fun {X} {Y} g f m => by
      let G : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨A⟩ :=
        { g with
          map_smul' := by
            intros
            dsimp
            rw [map_zsmul] }
      let F : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨Y⟩ :=
        { f with
          map_smul' := by
            intros
            dsimp
            rw [map_zsmul] }
      have : Mono F := by
        refine' ⟨fun {Z} α β eq1 => _⟩
        -- Porting note: trouble getting to ℤ-module from ModuleCat ℤ
        -- AddCommGroup.intModule not defeq to .isModule
        let α' : AddCommGroupCat.of Z ⟶ X := @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ α
        let β' : AddCommGroupCat.of Z ⟶ X := @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ β
        have eq2 : α' ≫ f = β' ≫ f := by
          ext x
          simp only [CategoryTheory.comp_apply, LinearMap.toAddMonoidHom_coe]
          simpa only [ModuleCat.coe_comp, LinearMap.coe_mk, Function.comp_apply] using
            FunLike.congr_fun eq1 x
        rw [cancel_mono] at eq2
        have : ⇑α' = ⇑β' := congrArg _ eq2
        ext x
        apply congrFun this _
      refine' ⟨(Injective.factorThru G F).toAddMonoidHom, _⟩
      ext x
      convert FunLike.congr_fun (Injective.comp_factorThru G F) x}
#align AddCommGroup.injective_of_injective_as_module AddCommGroupCat.injective_of_injective_as_module

theorem injective_as_module_of_injective_as_Ab [Injective (⟨A,inferInstance⟩ : AddCommGroupCat)] :
    Injective (⟨A⟩ : ModuleCat ℤ) :=
  { factors := fun {X} {Y} g f m => by
      let G : (⟨X,inferInstance⟩ : AddCommGroupCat) ⟶ ⟨A,inferInstance⟩ :=
        @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ g
      let F : (⟨X,inferInstance⟩ : AddCommGroupCat) ⟶ ⟨Y,inferInstance⟩ :=
        @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) (_) _ f
      have : Mono F := by
        rw [mono_iff_injective]
        intro _ _ h
        exact ((ModuleCat.mono_iff_injective f).mp m) h
      refine ⟨ @LinearMap.mk _ _ _ _ _ _ _ _ _ (_) _ (Injective.factorThru G F).toAddHom ?_ , ?_⟩
      change ∀ r, ∀ x, (Injective.factorThru G F).toFun _ = _ • (Injective.factorThru G F).toFun _
      · intro m x
        rw [AddMonoidHom.toFun_eq_coe, RingHom.id_apply]
        induction' m using Int.induction_on with n hn n hn
        · rw [zero_smul]
          convert map_zero (M := Y) (N := A) (F := Y →+ A) _
          -- Porting note: hell of non-defeq instances; somehow this worked
          refine @zero_smul ℤ Y (MonoidWithZero.toZero) (AddMonoid.toZero) ?_ x
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [add_smul]
          rw [← hn, one_smul, ←map_add]
          congr
          convert @add_smul ℤ Y _ _ ?_ n 1 x
          refine @one_smul ℤ Y _ ?_ x|>.symm
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [sub_smul]
          rw [← hn, one_smul, ←map_sub]
          congr
          convert @sub_smul ℤ Y _ _ ?_ (-n) 1 x
          refine @one_smul ℤ Y _ ?_ x|>.symm
      ext x
      have := congrFun (congrArg (fun H => H.toFun) (Injective.comp_factorThru G F)) x
      simp only [ModuleCat.coe_comp, Function.comp_apply] at this
      apply this }
#align AddCommGroup.injective_as_module_of_injective_as_Ab AddCommGroupCat.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    CategoryTheory.Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  @injective_of_injective_as_module A _ <|
    @Module.injective_object_of_injective_module ℤ _ A _ _ <|
      Module.Baer.injective fun I g => by
        rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
        by_cases m_eq_zero : m = 0
        · subst m_eq_zero
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro _
            exact g 0
          · intro _ _
            simp only [map_zero, add_zero]
          · intro n1 _
            simp only [map_zero, smul_zero]
          · rw [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hn
            simp only [hn, map_zero]
            symm
            convert map_zero g
        · set gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩ with gm_eq
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro n
            exact n • DivisibleBy.div gₘ m
          · intro n1 n2
            simp only [add_smul]
          · intro n1 n2
            dsimp
            rw [mul_smul]
          · rw [Submodule.mem_span_singleton] at hn
            rcases hn with ⟨n, rfl⟩
            simp only [gm_eq, Algebra.id.smul_eq_mul, LinearMap.coe_mk]
            dsimp
            rw [mul_smul]
            -- Porting note: used to be able to just rw [Div...]
            have s := congrArg (fun l => n • l) <| DivisibleBy.div_cancel gₘ m_eq_zero
            dsimp at s
            rw [s, ← LinearMap.map_smul]
            congr
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

namespace enough_injectives_aux_proofs

variable (A_ : AddCommGroupCat.{u})

/-- the next term of `A`'s injective resolution is `∏_{A → ℚ/ℤ}, ℚ/ℤ`.-/
def next : AddCommGroupCat.{u} := of <|
  (A_ ⟶ of <| ULift <| AddCircle (1 : ℚ)) → AddCircle (1 : ℚ)

instance : CategoryTheory.Injective <| of <| ULift.{u} <| AddCircle (1 : ℚ) :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  @injective_of_divisible _ _ {
    div := λ a n ↦ ULift.up (DivisibleBy.div a.down n)
    div_zero := λ a ↦ by simp only [DivisibleBy.div_zero]; rfl
    div_cancel := λ {n} a ha ↦ by ext1; exact DivisibleBy.div_cancel a.down ha
  }

instance : CategoryTheory.Injective <| next A_ :=
  have : Fact ((0 : ℚ) < 1) := ⟨by norm_num⟩
  @injective_of_divisible _ _ <| @Pi.divisibleBy _ _ _ _ _ _ <| λ f ↦ inferInstance

/-- the next term of `A`'s injective resolution is `∏_{A → ℚ/ℤ}, ℚ/ℤ`.-/
@[simps] def toNext : A_ ⟶ next A_ where
  toFun := λ a i ↦ (i a).down
  map_zero' := by simp only [map_zero, ULift.zero_down]; rfl
  map_add' := by intros; simp only [map_add]; rfl

lemma toNext_inj_of_exists
    (h : ∀ (a : A_), a ≠ 0 →
      ∃ (f : ModuleCat.of ℤ (ℤ ∙ a) ⟶ ModuleCat.of ℤ (ULift <| AddCircle (1 : ℚ))),
        f ⟨a, Submodule.subset_span rfl⟩ ≠ 0) :
    Function.Injective $ toNext A_ :=
  (injective_iff_map_eq_zero _).2 λ a h0 ↦ not_not.1 λ ha ↦ by
    obtain ⟨f, hf⟩ := h a ha
    let g : ModuleCat.of ℤ (ℤ ∙ a) ⟶ ModuleCat.of ℤ A_ := Submodule.subtype _
    have hg : Mono g
    · rw [ModuleCat.mono_iff_injective]
      apply Submodule.injective_subtype
    have i1 : CategoryTheory.Injective <| of (ULift.{u} $ AddCircle (1 : ℚ))
    · infer_instance
    have i2 := @injective_as_module_of_injective_as_Ab (of (ULift $ AddCircle (1 : ℚ))) _ i1
    rw [← FunLike.congr_fun (@Injective.comp_factorThru (ModuleCat ℤ) _ _ _ _ i2 f g hg)
      ⟨a, Submodule.mem_span_singleton_self a⟩] at hf
    refine hf <| ULift.down_injective <| congr_fun h0
      (@Injective.factorThru (ModuleCat ℤ) _ _ _ _ i2 f g hg).toAddMonoidHom


section

variable {A_}
variable (a : A_)

/-- the `ℤ`-linear map of scalar multiplication (. • a)-/
@[simps] def smulBya : ℤ →ₗ[ℤ] A_ := {
  toFun := (. • a)
  map_smul' := by intros; simp [mul_smul]
  map_add' := by intros; simp [add_smul]
}

lemma smulBya_range : LinearMap.range (smulBya a) = ℤ ∙ a := by
  ext1 x
  rw [Submodule.mem_span_singleton]
  simp only [LinearMap.mem_range, smulBya_apply]

lemma smulBya_ker : LinearMap.ker (smulBya a) = Ideal.span {(addOrderOf a : ℤ)} := by
  ext1 x
  rw [Ideal.mem_span_singleton, LinearMap.mem_ker, addOrderOf_dvd_iff_zsmul_eq_zero, smulBya_apply]

/--
ℤ ⧸ ⟨ord(a)⟩ ≃ aℤ
-/
@[simps!] noncomputable def ZModSpanAddOrderOfEquiv :
    (ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)}) ≃ₗ[ℤ] ℤ ∙ a :=
  letI e1 : (ℤ ⧸ (LinearMap.ker <| smulBya a)) ≃ₗ[ℤ] (ℤ ∙ a) :=
    (LinearMap.quotKerEquivRange <| smulBya a).trans (LinearEquiv.ofEq _ _ <| smulBya_range a)
  letI e2 : (ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)}) ≃ₗ[ℤ] (ℤ ⧸ (LinearMap.ker <| smulBya a)) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl (R := ℤ) (M := ℤ)) <| by
      rw [smulBya_ker]
      exact Submodule.map_id _
  e2.trans e1

end

/-- given `n : ℕ`, the map `m ↦ n / m`. -/
@[simps] noncomputable def divBy (n : ℕ) : ℤ →ₗ[ℤ] AddCircle (1 : ℚ) where
  toFun := λ m ↦ Quotient.mk _ <| (m : ℚ) * (n : ℚ)⁻¹
  map_add' := λ x y ↦ by
    dsimp
    change _ = Quotient.mk _ (_ + _)
    apply Quotient.sound'
    rw [QuotientAddGroup.leftRel_eq, ← add_mul]
    dsimp only
    rw [neg_add_eq_sub, ← sub_mul]
    simpa only [Int.cast_add, sub_self, zero_mul] using (AddSubgroup.zmultiples 1).zero_mem
  map_smul' := λ x y ↦  by
    dsimp
    change _ = Quotient.mk _ (_ • _)
    apply Quotient.sound'
    rw [QuotientAddGroup.leftRel_eq]
    dsimp only
    rw [zsmul_eq_mul, ← mul_assoc, Int.cast_mul, neg_add_eq_sub, sub_self]
    exact (AddSubgroup.zmultiples (1 : ℚ)).zero_mem

namespace infinite_order

variable {A_}
variable {a : A_} (infinite_order : ¬IsOfFinAddOrder a)

/-- the map sending `n • a` to `n/2` when `a` has infinite order-/
@[simps!] noncomputable def toRatCircle : (ℤ ∙ a) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  let e : (ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)}) →ₗ[ℤ] AddCircle (1 : ℚ) :=
    Submodule.liftQSpanSingleton _ (divBy 2) <| by
      rw [← addOrderOf_eq_zero_iff] at infinite_order
      simp only [infinite_order, CharP.cast_eq_zero, map_zero]
  e ∘ₗ (ZModSpanAddOrderOfEquiv a).symm.toLinearMap

lemma toRatCircle_apply_self_eq_aux :
    toRatCircle infinite_order ⟨smulBya a 1,
      by rw [smulBya_apply, one_smul]; exact Submodule.mem_span_singleton_self a⟩ =
    Quotient.mk _ (2 : ℚ)⁻¹ := by
  rw [toRatCircle_apply]
  erw [LinearMap.quotKerEquivRange_symm_apply_image (smulBya a), LinearEquiv.coe_toEquiv]
  rw [← Submodule.Quotient.equiv_refl, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply]
  convert Submodule.liftQSpanSingleton_apply _ _ _ _ using 1
  · convert (smulBya_ker a).symm using 1
    exact Submodule.map_id _

lemma toRatCircle_apply_self_eq :
    toRatCircle infinite_order ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Quotient.mk _ (2 : ℚ)⁻¹ := by
  rw [← toRatCircle_apply_self_eq_aux infinite_order]
  simp

lemma toRatCircle_apply_self_ne_zero :
    toRatCircle infinite_order ⟨a, Submodule.mem_span_singleton_self a⟩ ≠ 0 := by
  rw [toRatCircle_apply_self_eq infinite_order]
  change _ ≠ Quotient.mk _ (0 : ℚ)
  intro r
  erw [QuotientAddGroup.mk'_eq_mk'] at r
  obtain ⟨_, ⟨z, rfl⟩, H⟩ := r
  simp only [zsmul_eq_mul, mul_one] at H
  rw [add_comm, add_eq_zero_iff_eq_neg] at H
  have ineq0 : |(z : ℚ)| < 1
  · rw [H, abs_neg, abs_inv, inv_lt_one_iff]; right; norm_num
  norm_cast at ineq0
  rw [Int.abs_lt_one_iff] at ineq0
  subst ineq0
  norm_num at H

end infinite_order

namespace finite_order

variable {A_}
variable {a : A_} (finite_order : IsOfFinAddOrder a)

lemma divBy_addOrderOf_addOrderOf : divBy (addOrderOf a) (addOrderOf a) = 0 := by
  simp only [divBy_apply, Int.cast_ofNat, ne_eq, Nat.cast_eq_zero]
  apply Quotient.sound'
  rw [QuotientAddGroup.leftRel_eq]
  simp only [ne_eq, Nat.cast_eq_zero, add_zero, neg_mem_iff]
  rw [mul_inv_cancel]
  · exact AddSubgroup.mem_zmultiples 1
  · rw [← addOrderOf_pos_iff] at finite_order
    norm_num
    linarith

/-- the map sending `n • a` to `n / ord(a)` when `a` has finite order. -/
@[simps!] noncomputable def toRatCircle : (ℤ ∙ a) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  let e : (ℤ ⧸ Ideal.span {(addOrderOf a : ℤ)}) →ₗ[ℤ] AddCircle (1 : ℚ) :=
    Submodule.liftQSpanSingleton _ (divBy <| addOrderOf a) <|
      divBy_addOrderOf_addOrderOf finite_order
  e ∘ₗ (ZModSpanAddOrderOfEquiv a).symm.toLinearMap

lemma toRatCircle_apply_self_eq_aux :
    toRatCircle finite_order ⟨smulBya a 1,
      by rw [smulBya_apply, one_smul]; exact Submodule.mem_span_singleton_self a⟩ =
    Quotient.mk _ (addOrderOf a : ℚ)⁻¹ := by
  rw [toRatCircle_apply]
  erw [LinearMap.quotKerEquivRange_symm_apply_image (smulBya a), LinearEquiv.coe_toEquiv]
  rw [← Submodule.Quotient.equiv_refl, Submodule.Quotient.equiv_symm,
    Submodule.Quotient.equiv_apply]
  convert Submodule.liftQSpanSingleton_apply _ _ _ _ using 1
  simp only [smulBya_apply, Eq.ndrec, id_eq, eq_mpr_eq_cast, cast_eq, LinearEquiv.refl_symm,
    LinearEquiv.refl_toLinearMap, LinearMap.id_coe, divBy_apply, Int.cast_one, one_mul]
  · convert (smulBya_ker a).symm using 1
    exact Submodule.map_id _

lemma toRatCircle_apply_self_eq :
    toRatCircle finite_order ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Quotient.mk _ (addOrderOf a : ℚ)⁻¹ := by
  rw [← toRatCircle_apply_self_eq_aux finite_order]
  simp

lemma toRatCircle_apply_self_ne_zero (ne_zero : a ≠ 0) :
    toRatCircle finite_order ⟨a, Submodule.mem_span_singleton_self a⟩ ≠ 0 := by
  rw [toRatCircle_apply_self_eq finite_order]
  change _ ≠ Quotient.mk _ (0 : ℚ)
  intro r
  erw [QuotientAddGroup.mk'_eq_mk'] at r
  obtain ⟨_, ⟨z, rfl⟩, H⟩ := r
  simp only [zsmul_eq_mul, mul_one] at H
  -- This proof is a bit stupid:
  -- we want to show that `ord(a)⁻¹ + z = 0` if contradiction
  -- this should be easy because `ord(a) ∈ ℤ` is invertible in `ℚ`,
  -- so `ord(a) = 1`, so `a = 0`, contradiction,
  -- but I don't know how to say this.
  replace H : addOrderOf a = 1
  · rw [← addOrderOf_pos_iff] at finite_order
    have eq0 : (addOrderOf a : ℚ) = -(z : ℚ)⁻¹
    · rw [add_eq_zero_iff_eq_neg, inv_eq_iff_eq_inv] at H
      rw [H, inv_neg]
    have eq1 : |(addOrderOf a : ℚ)| = |(z : ℚ)|⁻¹
    · rw [eq0, abs_neg, abs_inv]
    have ineq0 : 1 ≤ |(addOrderOf a : ℚ)|
    · norm_num
      linarith
    rw [eq1, le_inv, inv_one] at ineq0
    norm_cast at ineq0
    rw [Int.abs_le_one_iff] at ineq0
    pick_goal 2
    · norm_num
    pick_goal 2
    · simp only [abs_pos, ne_eq, Int.cast_eq_zero]
      rintro rfl
      simp only [Int.cast_zero, add_zero, inv_eq_zero, Nat.cast_eq_zero] at H
      linarith only [finite_order, H]
    obtain (rfl|rfl|rfl) := ineq0
    · simp only [Int.cast_zero, inv_zero, neg_zero, Nat.cast_eq_zero] at eq0
      linarith only [eq0, finite_order]
    · simp only [Nat.abs_cast, Int.cast_one, abs_one, inv_one, Nat.cast_eq_one,
        AddMonoid.addOrderOf_eq_one_iff] at eq1
      exact (ne_zero eq1).elim
    · rw [Int.cast_neg, Int.cast_one, ← sub_eq_add_neg, sub_eq_zero] at H
      simp only [inv_eq_one, Nat.cast_eq_one, AddMonoid.addOrderOf_eq_one_iff] at H
      exact (ne_zero H).elim

  rw [AddMonoid.addOrderOf_eq_one_iff] at H
  exact ne_zero H

end finite_order

lemma toNext_inj : Function.Injective $ toNext A_ := by
  apply toNext_inj_of_exists
  intro a ne_zero
  by_cases order : IsOfFinAddOrder a
  · let F := finite_order.toRatCircle order
    refine ⟨⟨⟨ULift.up, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ F, ?_⟩
    change _ ≠ ULift.up 0
    intro r
    rw [LinearMap.comp_apply] at r
    exact finite_order.toRatCircle_apply_self_ne_zero order ne_zero <| ULift.up_injective r
  · let F := infinite_order.toRatCircle order
    refine ⟨⟨⟨ULift.up, by intros; rfl⟩, by intros; rfl⟩ ∘ₗ F, ?_⟩
    change _ ≠ ULift.up 0
    intro r
    rw [LinearMap.comp_apply] at r
    exact infinite_order.toRatCircle_apply_self_ne_zero order <| ULift.up_injective r

/-- An injective presentation of `A`: A -> ∏_{A ⟶ ℚ/ℤ}, ℚ/ℤ-/
@[simps] def presentation : CategoryTheory.InjectivePresentation A_ where
  J := next A_
  injective := inferInstance
  f := toNext A_
  mono := (AddCommGroupCat.mono_iff_injective _).mpr $ toNext_inj _

end enough_injectives_aux_proofs

instance : CategoryTheory.EnoughInjectives (AddCommGroupCat.{u}) where
  presentation A_ := ⟨enough_injectives_aux_proofs.presentation A_⟩

end AddCommGroupCat
