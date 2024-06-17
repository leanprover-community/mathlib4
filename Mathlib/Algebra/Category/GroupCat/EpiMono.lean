/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

#align_import algebra.category.Group.epi_mono from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Monomorphisms and epimorphisms in `Group`
In this file, we prove monomorphisms in the category of groups are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

open scoped Pointwise

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

@[to_additive]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using _root_.congr_arg range (h f.ker.subtype 1 (by aesop_cat))
#align monoid_hom.ker_eq_bot_of_cancel MonoidHom.ker_eq_bot_of_cancel
#align add_monoid_hom.ker_eq_bot_of_cancel AddMonoidHom.ker_eq_bot_of_cancel

end

section

variable [CommGroup A] [CommGroup B]

@[to_additive]
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ := by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1 x
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' f.range).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h
#align monoid_hom.range_eq_top_of_cancel MonoidHom.range_eq_top_of_cancel
#align add_monoid_hom.range_eq_top_of_cancel AddMonoidHom.range_eq_top_of_cancel

end

end MonoidHom

section

open CategoryTheory

namespace GroupCat

set_option linter.uppercaseLean3 false

-- Porting note: already have Group G but Lean can't use that
@[to_additive]
instance (G : GroupCat) : Group G.α :=
  G.str

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u _ =>
    (@cancel_mono _ _ _ _ _ f _ (show GroupCat.of f.ker ⟶ A from u) _).1
#align Group.ker_eq_bot_of_mono GroupCat.ker_eq_bot_of_mono
#align AddGroup.ker_eq_bot_of_mono AddGroupCat.ker_eq_bot_of_mono

@[to_additive]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align Group.mono_iff_ker_eq_bot GroupCat.mono_iff_ker_eq_bot
#align AddGroup.mono_iff_ker_eq_bot AddGroupCat.mono_iff_ker_eq_bot

@[to_additive]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align Group.mono_iff_injective GroupCat.mono_iff_injective
#align AddGroup.mono_iff_injective AddGroupCat.mono_iff_injective

namespace SurjectiveOfEpiAuxs

set_option quotPrecheck false in
local notation "X" => Set.range (· • (f.range : Set B) : B → Set B)

/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
inductive XWithInfinity
  | fromCoset : Set.range (· • (f.range : Set B) : B → Set B) → XWithInfinity
  | infinity : XWithInfinity
#align Group.surjective_of_epi_auxs.X_with_infinity GroupCat.SurjectiveOfEpiAuxs.XWithInfinity

open XWithInfinity Equiv.Perm

local notation "X'" => XWithInfinity f

local notation "∞" => XWithInfinity.infinity

local notation "SX'" => Equiv.Perm X'

instance : SMul B X' where
  smul b x :=
    match x with
    | fromCoset y => fromCoset ⟨b • y, by
          rw [← y.2.choose_spec, leftCoset_assoc]
          -- Porting note: should we make `Bundled.α` reducible?
          let b' : B := y.2.choose
          use b * b'⟩
    | ∞ => ∞

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.mul_smul GroupCat.SurjectiveOfEpiAuxs.mul_smul

theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset, Subtype.ext_iff_val]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.one_smul GroupCat.SurjectiveOfEpiAuxs.one_smul

theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
    fromCoset ⟨b • ↑f.range, b, rfl⟩ = fromCoset ⟨f.range, 1, one_leftCoset _⟩ := by
  congr
  let b : B.α := b
  change b • (f.range : Set B) = f.range
  nth_rw 2 [show (f.range : Set B.α) = (1 : B) • f.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb
#align Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
    fromCoset ⟨b • ↑f.range, b, rfl⟩ ≠ fromCoset ⟨f.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  -- Porting note: annoying dance between types CoeSort.coe B, B.α, and B
  let b' : B.α := b
  change b' • (f.range : Set B) = f.range at r
  nth_rw 2 [show (f.range : Set B.α) = (1 : B) • f.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)
#align Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range

instance : DecidableEq X' :=
  Classical.decEq _

/-- Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
  Equiv.swap (fromCoset ⟨↑f.range, ⟨1, one_leftCoset _⟩⟩) ∞
#align Group.surjective_of_epi_auxs.tau GroupCat.SurjectiveOfEpiAuxs.tau

local notation "τ" => tau f

theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.range, 1, one_leftCoset _⟩ :=
  Equiv.swap_apply_right _ _
#align Group.surjective_of_epi_auxs.τ_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_apply_infinity

theorem τ_apply_fromCoset : τ (fromCoset ⟨f.range, 1, one_leftCoset _⟩) = ∞ :=
  Equiv.swap_apply_left _ _
#align Group.surjective_of_epi_auxs.τ_apply_fromCoset GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset

theorem τ_apply_fromCoset' (x : B) (hx : x ∈ f.range) :
    τ (fromCoset ⟨x • ↑f.range, ⟨x, rfl⟩⟩) = ∞ :=
  (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _
#align Group.surjective_of_epi_auxs.τ_apply_fromCoset' GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset'

theorem τ_symm_apply_fromCoset : Equiv.symm τ (fromCoset ⟨f.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_left]
#align Group.surjective_of_epi_auxs.τ_symm_apply_fromCoset GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset

theorem τ_symm_apply_infinity :
    Equiv.symm τ ∞ = fromCoset ⟨f.range, 1, one_leftCoset _⟩ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_right]
#align Group.surjective_of_epi_auxs.τ_symm_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity

/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β • y`.
-/
def g : B →* SX' where
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

local notation "g" => g f

/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  -- Porting note: mathport removed () from (τ) which are needed
  toFun β := ((τ).symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp
#align Group.surjective_of_epi_auxs.H GroupCat.SurjectiveOfEpiAuxs.h

local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/


theorem g_apply_fromCoset (x : B) (y : Set.range (· • (f.range : Set B) : B → Set B)) :
    g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl
#align Group.surjective_of_epi_auxs.g_apply_fromCoset GroupCat.SurjectiveOfEpiAuxs.g_apply_fromCoset

theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl
#align Group.surjective_of_epi_auxs.g_apply_infinity GroupCat.SurjectiveOfEpiAuxs.g_apply_infinity

theorem h_apply_infinity (x : B) (hx : x ∈ f.range) : (h x) ∞ = ∞ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity, g_apply_fromCoset]
  simpa only using τ_apply_fromCoset' f x hx
#align Group.surjective_of_epi_auxs.h_apply_infinity GroupCat.SurjectiveOfEpiAuxs.h_apply_infinity

theorem h_apply_fromCoset (x : B) :
    (h x) (fromCoset ⟨f.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.range, 1, one_leftCoset _⟩ := by
    change ((τ).symm.trans (g x)).trans τ _ = _
    simp [-MonoidHom.coe_range, τ_symm_apply_fromCoset, g_apply_infinity, τ_apply_infinity]
#align Group.surjective_of_epi_auxs.h_apply_fromCoset GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset

theorem h_apply_fromCoset' (x : B) (b : B) (hb : b ∈ f.range) :
    h x (fromCoset ⟨b • f.range, b, rfl⟩) = fromCoset ⟨b • ↑f.range, b, rfl⟩ :=
  (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x
#align Group.surjective_of_epi_auxs.h_apply_fromCoset' GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset'

theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
    h x (fromCoset ⟨b • f.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.range, x * b, rfl⟩ := by
  change ((τ).symm.trans (g x)).trans τ _ = _
  simp only [tau, MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.range, 1, one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.range, b, rfl⟩) (fromCoset_ne_of_nin_range _ hb) (by simp)]
  simp only [g_apply_fromCoset, leftCoset_assoc]
  refine Equiv.swap_apply_of_ne_of_ne (fromCoset_ne_of_nin_range _ fun r => hb ?_) (by simp)
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, mul_left_inv, one_mul]
#align Group.surjective_of_epi_auxs.h_apply_fromCoset_nin_range GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range

theorem agree : f.range = { x | h x = g x } := by
  refine Set.ext fun b => ⟨?_, fun hb : h b = g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_fromCoset]
      by_cases m : y ∈ f.range
      · rw [h_apply_fromCoset' _ _ _ m, fromCoset_eq_of_mem_range _ m]
        change fromCoset _ = fromCoset ⟨f a • (y • _), _⟩
        simp only [← fromCoset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), smul_smul]
      · rw [h_apply_fromCoset_nin_range f (f a) ⟨_, rfl⟩ _ m]
        simp only [leftCoset_assoc]
    · rw [g_apply_infinity, h_apply_infinity f (f a) ⟨_, rfl⟩]
  · have eq1 : (h b) (fromCoset ⟨f.range, 1, one_leftCoset _⟩) =
        fromCoset ⟨f.range, 1, one_leftCoset _⟩ := by
      change ((τ).symm.trans (g b)).trans τ _ = _
      dsimp [tau]
      simp [g_apply_infinity f]
    have eq2 :
      g b (fromCoset ⟨f.range, 1, one_leftCoset _⟩) = fromCoset ⟨b • ↑f.range, b, rfl⟩ := rfl
    exact (fromCoset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, DFunLike.congr_fun hb])
#align Group.surjective_of_epi_auxs.agree GroupCat.SurjectiveOfEpiAuxs.agree

theorem comp_eq : (f ≫ show B ⟶ GroupCat.of SX' from g) = f ≫ show B ⟶ GroupCat.of SX' from h := by
  ext a
  change g (f a) = h (f a)
  have : f a ∈ { b | h b = g b } := by
    rw [← agree]
    use a
  rw [this]
#align Group.surjective_of_epi_auxs.comp_eq GroupCat.SurjectiveOfEpiAuxs.comp_eq

theorem g_ne_h (x : B) (hx : x ∉ f.range) : g ≠ h := by
  intro r
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.range, ⟨1, one_leftCoset _⟩⟩)
  change _ = ((τ).symm.trans (g x)).trans τ _ at r
  rw [g_apply_fromCoset, MonoidHom.coe_mk] at r
  simp only [MonoidHom.coe_range, Subtype.coe_mk, Equiv.symm_swap, Equiv.toFun_as_coe,
    Equiv.coe_trans, Function.comp_apply] at r
  erw [Equiv.swap_apply_left, g_apply_infinity, Equiv.swap_apply_right] at r
  exact fromCoset_ne_of_nin_range _ hx r
#align Group.surjective_of_epi_auxs.g_ne_h GroupCat.SurjectiveOfEpiAuxs.g_ne_h

end SurjectiveOfEpiAuxs

theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  by_contra r
  dsimp [Function.Surjective] at r
  push_neg at r
  rcases r with ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f))
#align Group.surjective_of_epi GroupCat.surjective_of_epi

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun _ => surjective_of_epi f, ConcreteCategory.epi_of_surjective f⟩
#align Group.epi_iff_surjective GroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.range).symm
#align Group.epi_iff_range_eq_top GroupCat.epi_iff_range_eq_top

end GroupCat

namespace AddGroupCat

set_option linter.uppercaseLean3 false

variable {A B : AddGroupCat.{u}} (f : A ⟶ B)

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  have i1 : Epi f ↔ Epi (groupAddGroupEquivalence.inverse.map f) := by
    refine ⟨?_, groupAddGroupEquivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply groupAddGroupEquivalence.inverse.map_epi
  rwa [GroupCat.epi_iff_surjective] at i1
#align AddGroup.epi_iff_surjective AddGroupCat.epi_iff_surjective

theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.range).symm
#align AddGroup.epi_iff_range_eq_top AddGroupCat.epi_iff_range_eq_top

end AddGroupCat

namespace GroupCat

set_option linter.uppercaseLean3 false

variable {A B : GroupCat.{u}} (f : A ⟶ B)

@[to_additive AddGroupCat.forget_groupCat_preserves_mono]
instance forget_groupCat_preserves_mono : (forget GroupCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align Group.forget_Group_preserves_mono GroupCat.forget_groupCat_preserves_mono
#align AddGroup.forget_Group_preserves_mono AddGroupCat.forget_groupCat_preserves_mono

@[to_additive AddGroupCat.forget_groupCat_preserves_epi]
instance forget_groupCat_preserves_epi : (forget GroupCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align Group.forget_Group_preserves_epi GroupCat.forget_groupCat_preserves_epi
#align AddGroup.forget_Group_preserves_epi AddGroupCat.forget_groupCat_preserves_epi

end GroupCat

namespace CommGroupCat

set_option linter.uppercaseLean3 false

variable {A B : CommGroupCat.{u}} (f : A ⟶ B)

-- Porting note: again to help with non-transparency
private instance (A : CommGroupCat) : CommGroup A.α := A.str
private instance (A : CommGroupCat) : Group A.α := A.str.toGroup

@[to_additive]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u _ =>
    (@cancel_mono _ _ _ _ _ f _ (show CommGroupCat.of f.ker ⟶ A from u) _).1
#align CommGroup.ker_eq_bot_of_mono CommGroupCat.ker_eq_bot_of_mono
#align AddCommGroup.ker_eq_bot_of_mono AddCommGroupCat.ker_eq_bot_of_mono

@[to_additive]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono f, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align CommGroup.mono_iff_ker_eq_bot CommGroupCat.mono_iff_ker_eq_bot
#align AddCommGroup.mono_iff_ker_eq_bot AddCommGroupCat.mono_iff_ker_eq_bot

@[to_additive]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align CommGroup.mono_iff_injective CommGroupCat.mono_iff_injective
#align AddCommGroup.mono_iff_injective AddCommGroupCat.mono_iff_injective

@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h =>
    (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ MonoidHom.range f, inferInstance⟩ from u) v).1 h
#align CommGroup.range_eq_top_of_epi CommGroupCat.range_eq_top_of_epi
#align AddCommGroup.range_eq_top_of_epi AddCommGroupCat.range_eq_top_of_epi

-- Porting note: again lack of transparency
@[to_additive]
instance (G : CommGroupCat) : CommGroup <| (forget CommGroupCat).obj G :=
  G.str

@[to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| MonoidHom.range_top_iff_surjective.mp hf⟩
#align CommGroup.epi_iff_range_eq_top CommGroupCat.epi_iff_range_eq_top
#align AddCommGroup.epi_iff_range_eq_top AddCommGroupCat.epi_iff_range_eq_top

@[to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_top_iff_surjective]
#align CommGroup.epi_iff_surjective CommGroupCat.epi_iff_surjective
#align AddCommGroup.epi_iff_surjective AddCommGroupCat.epi_iff_surjective

@[to_additive AddCommGroupCat.forget_commGroupCat_preserves_mono]
instance forget_commGroupCat_preserves_mono : (forget CommGroupCat).PreservesMonomorphisms where
  preserves f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align CommGroup.forget_CommGroup_preserves_mono CommGroupCat.forget_commGroupCat_preserves_mono
#align AddCommGroup.forget_CommGroup_preserves_mono AddCommGroupCat.forget_commGroupCat_preserves_mono

@[to_additive AddCommGroupCat.forget_commGroupCat_preserves_epi]
instance forget_commGroupCat_preserves_epi : (forget CommGroupCat).PreservesEpimorphisms where
  preserves f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align CommGroup.forget_CommGroup_preserves_epi CommGroupCat.forget_commGroupCat_preserves_epi
#align AddCommGroup.forget_CommGroup_preserves_epi AddCommGroupCat.forget_commGroupCat_preserves_epi

end CommGroupCat

end
