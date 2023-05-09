/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Group.epi_mono
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.EquivalenceGroupAddGroup
import Mathbin.GroupTheory.QuotientGroup

/-!
# Monomorphisms and epimorphisms in `Group`
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[to_additive AddMonoidHom.ker_eq_bot_of_cancel]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using _root_.congr_arg range (h f.ker.subtype 1 (by tidy))
#align monoid_hom.ker_eq_bot_of_cancel MonoidHom.ker_eq_bot_of_cancel
#align add_monoid_hom.ker_eq_bot_of_cancel AddMonoidHom.ker_eq_bot_of_cancel

end

section

variable [CommGroup A] [CommGroup B]

@[to_additive AddMonoidHom.range_eq_top_of_cancel]
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ :=
  by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h
#align monoid_hom.range_eq_top_of_cancel MonoidHom.range_eq_top_of_cancel
#align add_monoid_hom.range_eq_top_of_cancel AddMonoidHom.range_eq_top_of_cancel

end

end MonoidHom

section

open CategoryTheory

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive AddGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show GroupCat.of f.ker ⟶ A from u) _).1
#align Group.ker_eq_bot_of_mono GroupCat.ker_eq_bot_of_mono
#align AddGroup.ker_eq_bot_of_mono AddGroupCat.ker_eq_bot_of_mono

@[to_additive AddGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align Group.mono_iff_ker_eq_bot GroupCat.mono_iff_ker_eq_bot
#align AddGroup.mono_iff_ker_eq_bot AddGroupCat.mono_iff_ker_eq_bot

@[to_additive AddGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align Group.mono_iff_injective GroupCat.mono_iff_injective
#align AddGroup.mono_iff_injective AddGroupCat.mono_iff_injective

namespace SurjectiveOfEpiAuxs

-- mathport name: exprX
local notation "X" => Set.range (Function.swap leftCoset f.range.carrier)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
@[nolint has_nonempty_instance]
inductive XWithInfinity
  | from_coset : Set.range (Function.swap leftCoset f.range.carrier) → X_with_infinity
  | infinity : X_with_infinity
#align Group.surjective_of_epi_auxs.X_with_infinity GroupCat.SurjectiveOfEpiAuxs.XWithInfinity

open XWithInfinity Equiv.Perm

open Coset

-- mathport name: exprX'
local notation "X'" => XWithInfinity f

-- mathport name: «expr∞»
local notation "∞" => XWithInfinity.infinity

-- mathport name: exprSX'
local notation "SX'" => Equiv.Perm X'

instance : SMul B X'
    where smul b x :=
    match x with
    | from_coset y =>
      from_coset
        ⟨b *l y, by
          rw [← Subtype.val_eq_coe, ← y.2.choose_spec, leftCoset_assoc]
          use b * y.2.some⟩
    | ∞ => ∞

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, leftCoset_assoc]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.mul_smul GroupCat.SurjectiveOfEpiAuxs.mul_smul

theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, one_leftCoset, Subtype.ext_iff_val]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.one_smul GroupCat.SurjectiveOfEpiAuxs.one_smul

theorem from_coset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
    from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ =
      from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by
  congr
  change b *l f.range = f.range
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb
#align Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range GroupCat.SurjectiveOfEpiAuxs.from_coset_eq_of_mem_range

theorem from_coset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
    from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ ≠
      from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by
  intro r
  simp only [Subtype.mk_eq_mk] at r
  change b *l f.range = f.range at r
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)
#align Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range GroupCat.SurjectiveOfEpiAuxs.from_coset_ne_of_nin_range

instance : DecidableEq X' :=
  Classical.decEq _

/-- Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
  Equiv.swap (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) ∞
#align Group.surjective_of_epi_auxs.tau GroupCat.SurjectiveOfEpiAuxs.tau

-- mathport name: exprτ
local notation "τ" => tau f

theorem τ_apply_infinity : τ ∞ = from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  Equiv.swap_apply_right _ _
#align Group.surjective_of_epi_auxs.τ_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_apply_infinity

theorem τ_apply_from_coset : τ (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) = ∞ :=
  Equiv.swap_apply_left _ _
#align Group.surjective_of_epi_auxs.τ_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_apply_from_coset

theorem τ_apply_from_coset' (x : B) (hx : x ∈ f.range) :
    τ (from_coset ⟨x *l f.range.carrier, ⟨x, rfl⟩⟩) = ∞ :=
  (from_coset_eq_of_mem_range _ hx).symm ▸ τ_apply_from_coset _
#align Group.surjective_of_epi_auxs.τ_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.τ_apply_from_coset'

theorem τ_symm_apply_from_coset :
    (Equiv.symm τ) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) = ∞ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_left]
#align Group.surjective_of_epi_auxs.τ_symm_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_from_coset

theorem τ_symm_apply_infinity :
    (Equiv.symm τ) ∞ = from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_right]
#align Group.surjective_of_epi_auxs.τ_symm_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity

/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β *l y`.
-/
def g : B →* SX'
    where
  toFun β :=
    { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_left_inv, one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_right_inv, one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' b1 b2 := by
    ext
    simp [mul_smul]
#align Group.surjective_of_epi_auxs.G GroupCat.SurjectiveOfEpiAuxs.g

-- mathport name: exprg
local notation "g" => g f

/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  toFun β := (τ.symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp
#align Group.surjective_of_epi_auxs.H GroupCat.SurjectiveOfEpiAuxs.h

-- mathport name: exprh
local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/


theorem g_apply_from_coset (x : B) (y : X) : (g x) (from_coset y) = from_coset ⟨x *l y, by tidy⟩ :=
  rfl
#align Group.surjective_of_epi_auxs.g_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.g_apply_from_coset

theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ :=
  rfl
#align Group.surjective_of_epi_auxs.g_apply_infinity GroupCat.SurjectiveOfEpiAuxs.g_apply_infinity

theorem h_apply_infinity (x : B) (hx : x ∈ f.range) : (h x) ∞ = ∞ :=
  by
  simp only [H, MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity, g_apply_from_coset]
  simpa only [← Subtype.val_eq_coe] using τ_apply_from_coset' f x hx
#align Group.surjective_of_epi_auxs.h_apply_infinity GroupCat.SurjectiveOfEpiAuxs.h_apply_infinity

theorem h_apply_from_coset (x : B) :
    (h x) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
      from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by simp [H, τ_symm_apply_from_coset, g_apply_infinity, τ_apply_infinity]
#align Group.surjective_of_epi_auxs.h_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset

theorem h_apply_from_coset' (x : B) (b : B) (hb : b ∈ f.range) :
    (h x) (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
      from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
  (from_coset_eq_of_mem_range _ hb).symm ▸ h_apply_from_coset f x
#align Group.surjective_of_epi_auxs.h_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset'

theorem h_apply_from_coset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
    (h x) (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
      from_coset ⟨x * b *l f.range.carrier, ⟨x * b, rfl⟩⟩ :=
  by
  simp only [H, tau, MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) ∞
      (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) (from_coset_ne_of_nin_range _ hb) (by simp)]
  simp only [g_apply_from_coset, ← Subtype.val_eq_coe, leftCoset_assoc]
  refine' Equiv.swap_apply_of_ne_of_ne (from_coset_ne_of_nin_range _ fun r => hb _) (by simp)
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, mul_left_inv, one_mul]
#align Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset_nin_range

theorem agree : f.range.carrier = { x | h x = g x } :=
  by
  refine' Set.ext fun b => ⟨_, fun hb : h b = g b => by_contradiction fun r => _⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_from_coset]
      by_cases m : y ∈ f.range
      · rw [h_apply_from_coset' _ _ _ m, from_coset_eq_of_mem_range _ m]
        change from_coset _ = from_coset ⟨f a *l (y *l _), _⟩
        simpa only [← from_coset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), leftCoset_assoc]
      · rw [h_apply_from_coset_nin_range _ _ ⟨_, rfl⟩ _ m]
        simpa only [← Subtype.val_eq_coe, leftCoset_assoc]
    · rw [g_apply_infinity, h_apply_infinity _ _ ⟨_, rfl⟩]
  · have eq1 :
      (h b) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
        from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
      by simp [H, tau, g_apply_infinity]
    have eq2 :
      (g b) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
        from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
      rfl
    exact (from_coset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, FunLike.congr_fun hb])
#align Group.surjective_of_epi_auxs.agree GroupCat.SurjectiveOfEpiAuxs.agree

theorem comp_eq : (f ≫ show B ⟶ GroupCat.of SX' from g) = f ≫ h :=
  FunLike.ext _ _ fun a => by
    simp only [comp_apply, show h (f a) = _ from (by simp [← agree] : f a ∈ { b | h b = g b })]
#align Group.surjective_of_epi_auxs.comp_eq GroupCat.SurjectiveOfEpiAuxs.comp_eq

theorem g_ne_h (x : B) (hx : x ∉ f.range) : g ≠ h :=
  by
  intro r
  replace r :=
    FunLike.congr_fun (FunLike.congr_fun r x) (from_coset ⟨f.range, ⟨1, one_leftCoset _⟩⟩)
  rw [H, g_apply_from_coset, MonoidHom.coe_mk, tau] at r
  simp only [MonoidHom.coe_range, Subtype.coe_mk, Equiv.symm_swap, Equiv.toFun_as_coe,
    Equiv.coe_trans, Function.comp_apply] at r
  erw [Equiv.swap_apply_left, g_apply_infinity, Equiv.swap_apply_right] at r
  exact from_coset_ne_of_nin_range _ hx r
#align Group.surjective_of_epi_auxs.g_ne_h GroupCat.SurjectiveOfEpiAuxs.g_ne_h

end SurjectiveOfEpiAuxs

theorem surjective_of_epi [Epi f] : Function.Surjective f :=
  by
  by_contra r
  push_neg  at r
  rcases r with ⟨b, hb⟩
  exact
    surjective_of_epi_auxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      ((cancel_epi f).1 (surjective_of_epi_auxs.comp_eq f))
#align Group.surjective_of_epi GroupCat.surjective_of_epi

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun h => @surjective_of_epi f h, ConcreteCategory.epi_of_surjective _⟩
#align Group.epi_iff_surjective GroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.range).symm
#align Group.epi_iff_range_eq_top GroupCat.epi_iff_range_eq_top

end GroupCat

namespace AddGroupCat

variable {A B : AddGroupCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  by
  have i1 : epi f ↔ epi (Group_AddGroup_equivalence.inverse.map f) :=
    by
    refine' ⟨_, Group_AddGroup_equivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply Group_AddGroup_equivalence.inverse.map_epi
  rwa [GroupCat.epi_iff_surjective] at i1
#align AddGroup.epi_iff_surjective AddGroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.range).symm
#align AddGroup.epi_iff_range_eq_top AddGroupCat.epi_iff_range_eq_top

end AddGroupCat

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive]
instance forget_groupCat_preserves_mono : (forget GroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align Group.forget_Group_preserves_mono GroupCat.forget_groupCat_preserves_mono
#align AddGroup.forget_Group_preserves_mono AddGroupCat.forget_groupCat_preserves_mono

@[to_additive]
instance forget_groupCat_preserves_epi : (forget GroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align Group.forget_Group_preserves_epi GroupCat.forget_groupCat_preserves_epi
#align AddGroup.forget_Group_preserves_epi AddGroupCat.forget_groupCat_preserves_epi

end GroupCat

namespace CommGroupCat

variable {A B : CommGroupCat.{u}} (f : A ⟶ B)

@[to_additive AddCommGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show CommGroupCat.of f.ker ⟶ A from u) _).1
#align CommGroup.ker_eq_bot_of_mono CommGroupCat.ker_eq_bot_of_mono
#align AddCommGroup.ker_eq_bot_of_mono AddCommGroupCat.ker_eq_bot_of_mono

@[to_additive AddCommGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align CommGroup.mono_iff_ker_eq_bot CommGroupCat.mono_iff_ker_eq_bot
#align AddCommGroup.mono_iff_ker_eq_bot AddCommGroupCat.mono_iff_ker_eq_bot

@[to_additive AddCommGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align CommGroup.mono_iff_injective CommGroupCat.mono_iff_injective
#align AddCommGroup.mono_iff_injective AddCommGroupCat.mono_iff_injective

@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h =>
    (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ MonoidHom.range f⟩ from u) v).1 h
#align CommGroup.range_eq_top_of_epi CommGroupCat.range_eq_top_of_epi
#align AddCommGroup.range_eq_top_of_epi AddCommGroupCat.range_eq_top_of_epi

@[to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| MonoidHom.range_top_iff_surjective.mp hf⟩
#align CommGroup.epi_iff_range_eq_top CommGroupCat.epi_iff_range_eq_top
#align AddCommGroup.epi_iff_range_eq_top AddCommGroupCat.epi_iff_range_eq_top

@[to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_top_iff_surjective]
#align CommGroup.epi_iff_surjective CommGroupCat.epi_iff_surjective
#align AddCommGroup.epi_iff_surjective AddCommGroupCat.epi_iff_surjective

@[to_additive]
instance forget_commGroupCat_preserves_mono : (forget CommGroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align CommGroup.forget_CommGroup_preserves_mono CommGroupCat.forget_commGroupCat_preserves_mono
#align AddCommGroup.forget_CommGroup_preserves_mono AddCommGroupCat.forget_commGroupCat_preserves_mono

@[to_additive]
instance forget_commGroupCat_preserves_epi : (forget CommGroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align CommGroup.forget_CommGroup_preserves_epi CommGroupCat.forget_commGroupCat_preserves_epi
#align AddCommGroup.forget_CommGroup_preserves_epi AddCommGroupCat.forget_commGroupCat_preserves_epi

end CommGroupCat

end

