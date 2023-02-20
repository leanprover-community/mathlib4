/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.group.seminorm
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Positivity
import Mathbin.Data.Real.Nnreal

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `add_group_seminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `nonarch_add_group_seminorm`: A function `f` from an additive group `G` to the reals that
  preserves zero, takes nonnegative values, is nonarchimedean and such that `f (-x) = f x`
  for all `x`.
* `group_seminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `add_group_norm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `nonarch_add_group_norm`: A nonarchimedean seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `group_norm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## Notes

The corresponding hom classes are defined in `analysis.order.hom.basic` to be used by absolute
values.

We do not define `nonarch_add_group_seminorm` as an extension of `add_group_seminorm` to avoid
having a superfluous `add_le'` field in the resulting structure. The same applies to
`nonarch_add_group_norm`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
-/


open Set

open NNReal

variable {ι R R' E F G : Type _}

/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
@[protect_proj]
structure AddGroupSeminorm (G : Type _) [AddGroup G] extends ZeroHom G ℝ where
  add_le' : ∀ r s, to_fun (r + s) ≤ to_fun r + to_fun s
  neg' : ∀ r, to_fun (-r) = to_fun r
#align add_group_seminorm AddGroupSeminorm

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive, protect_proj]
structure GroupSeminorm (G : Type _) [Group G] where
  toFun : G → ℝ
  map_one' : to_fun 1 = 0
  mul_le' : ∀ x y, to_fun (x * y) ≤ to_fun x + to_fun y
  inv' : ∀ x, to_fun x⁻¹ = to_fun x
#align group_seminorm GroupSeminorm
#align add_group_seminorm AddGroupSeminorm

/-- A nonarchimedean seminorm on an additive group `G` is a function `f : G → ℝ` that preserves
zero, is nonarchimedean and such that `f (-x) = f x` for all `x`. -/
@[protect_proj]
structure NonarchAddGroupSeminorm (G : Type _) [AddGroup G] extends ZeroHom G ℝ where
  add_le_max' : ∀ r s, to_fun (r + s) ≤ max (to_fun r) (to_fun s)
  neg' : ∀ r, to_fun (-r) = to_fun r
#align nonarch_add_group_seminorm NonarchAddGroupSeminorm

/-! NOTE: We do not define `nonarch_add_group_seminorm` as an extension of `add_group_seminorm`
  to avoid having a superfluous `add_le'` field in the resulting structure. The same applies to
  `nonarch_add_group_norm` below. -/


/-- A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
@[protect_proj]
structure AddGroupNorm (G : Type _) [AddGroup G] extends AddGroupSeminorm G where
  eq_zero_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 0
#align add_group_norm AddGroupNorm

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[protect_proj, to_additive]
structure GroupNorm (G : Type _) [Group G] extends GroupSeminorm G where
  eq_one_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 1
#align group_norm GroupNorm
#align add_group_norm AddGroupNorm

/-- A nonarchimedean norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
nonarchimedean and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
@[protect_proj]
structure NonarchAddGroupNorm (G : Type _) [AddGroup G] extends NonarchAddGroupSeminorm G where
  eq_zero_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 0
#align nonarch_add_group_norm NonarchAddGroupNorm

attribute [nolint doc_blame]
  AddGroupSeminorm.toZeroHom AddGroupNorm.toAddGroupSeminorm GroupNorm.toGroupSeminorm NonarchAddGroupSeminorm.toZeroHom NonarchAddGroupNorm.toNonarchAddGroupSeminorm

attribute [to_additive] GroupNorm.toGroupSeminorm

/-- `nonarch_add_group_seminorm_class F α` states that `F` is a type of nonarchimedean seminorms on
the additive group `α`.

You should extend this class when you extend `nonarch_add_group_seminorm`. -/
@[protect_proj]
class NonarchAddGroupSeminormClass (F : Type _) (α : outParam <| Type _) [AddGroup α] extends
  NonarchimedeanHomClass F α ℝ where
  map_zero (f : F) : f 0 = 0
  map_neg_eq_map' (f : F) (a : α) : f (-a) = f a
#align nonarch_add_group_seminorm_class NonarchAddGroupSeminormClass

/-- `nonarch_add_group_norm_class F α` states that `F` is a type of nonarchimedean norms on the
additive group `α`.

You should extend this class when you extend `nonarch_add_group_norm`. -/
@[protect_proj]
class NonarchAddGroupNormClass (F : Type _) (α : outParam <| Type _) [AddGroup α] extends
  NonarchAddGroupSeminormClass F α where
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0
#align nonarch_add_group_norm_class NonarchAddGroupNormClass

section NonarchAddGroupSeminormClass

variable [AddGroup E] [NonarchAddGroupSeminormClass F E] (f : F) (x y : E)

include E

theorem map_sub_le_max : f (x - y) ≤ max (f x) (f y) :=
  by
  rw [sub_eq_add_neg, ← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _
#align map_sub_le_max map_sub_le_max

end NonarchAddGroupSeminormClass

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupSeminormClass.toAddGroupSeminormClass [AddGroup E]
    [NonarchAddGroupSeminormClass F E] : AddGroupSeminormClass F E ℝ :=
  {
    ‹NonarchAddGroupSeminormClass F
        E› with
    map_add_le_add := fun f x y =>
      haveI h_nonneg : ∀ a, 0 ≤ f a := by
        intro a
        rw [← NonarchAddGroupSeminormClass.map_zero f, ← sub_self a]
        exact le_trans (map_sub_le_max _ _ _) (by rw [max_self (f a)])
      le_trans (map_add_le_max _ _ _)
        (max_le (le_add_of_nonneg_right (h_nonneg _)) (le_add_of_nonneg_left (h_nonneg _)))
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }
#align nonarch_add_group_seminorm_class.to_add_group_seminorm_class NonarchAddGroupSeminormClass.toAddGroupSeminormClass

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupNormClass.toAddGroupNormClass [AddGroup E]
    [NonarchAddGroupNormClass F E] : AddGroupNormClass F E ℝ :=
  {
    ‹NonarchAddGroupNormClass F
        E› with
    map_add_le_add := map_add_le_add
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }
#align nonarch_add_group_norm_class.to_add_group_norm_class NonarchAddGroupNormClass.toAddGroupNormClass

/-! ### Seminorms -/


namespace GroupSeminorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupSeminorm E}

@[to_additive]
instance groupSeminormClass : GroupSeminormClass (GroupSeminorm E) E ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
#align group_seminorm.group_seminorm_class GroupSeminorm.groupSeminormClass
#align add_group_seminorm.add_group_seminorm_class AddGroupSeminorm.add_group_seminorm_class

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun`. "]
instance : CoeFun (GroupSeminorm E) fun _ => E → ℝ :=
  ⟨GroupSeminorm.toFun⟩

@[simp, to_additive]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align group_seminorm.to_fun_eq_coe GroupSeminorm.toFun_eq_coe
#align add_group_seminorm.to_fun_eq_coe AddGroupSeminorm.toFun_eq_coe

@[ext, to_additive]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align group_seminorm.ext GroupSeminorm.ext
#align add_group_seminorm.ext AddGroupSeminorm.ext

@[to_additive]
instance : PartialOrder (GroupSeminorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

@[to_additive]
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_seminorm.le_def GroupSeminorm.le_def
#align add_group_seminorm.le_def AddGroupSeminorm.le_def

@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_seminorm.lt_def GroupSeminorm.lt_def
#align add_group_seminorm.lt_def AddGroupSeminorm.lt_def

@[simp, to_additive, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_seminorm.coe_le_coe GroupSeminorm.coe_le_coe
#align add_group_seminorm.coe_le_coe AddGroupSeminorm.coe_le_coe

@[simp, to_additive, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_seminorm.coe_lt_coe GroupSeminorm.coe_lt_coe
#align add_group_seminorm.coe_lt_coe AddGroupSeminorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance : Zero (GroupSeminorm E) :=
  ⟨{  toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun x => rfl }⟩

@[simp, to_additive, norm_cast]
theorem coe_zero : ⇑(0 : GroupSeminorm E) = 0 :=
  rfl
#align group_seminorm.coe_zero GroupSeminorm.coe_zero
#align add_group_seminorm.coe_zero AddGroupSeminorm.coe_zero

@[simp, to_additive]
theorem zero_apply (x : E) : (0 : GroupSeminorm E) x = 0 :=
  rfl
#align group_seminorm.zero_apply GroupSeminorm.zero_apply
#align add_group_seminorm.zero_apply AddGroupSeminorm.zero_apply

@[to_additive]
instance : Inhabited (GroupSeminorm E) :=
  ⟨0⟩

@[to_additive]
instance : Add (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
        (add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq <|
          add_add_add_comm _ _ _ _
      inv' := fun x => by rw [map_inv_eq_map p, map_inv_eq_map q] }⟩

@[simp, to_additive]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_seminorm.coe_add GroupSeminorm.coe_add
#align add_group_seminorm.coe_add AddGroupSeminorm.coe_add

@[simp, to_additive]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_seminorm.add_apply GroupSeminorm.add_apply
#align add_group_seminorm.add_apply AddGroupSeminorm.add_apply

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive]
instance : HasSup (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply, ← map_one_eq_zero p, sup_eq_left, map_one_eq_zero p, map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_mul_le_add q x y).trans <| add_le_add le_sup_right le_sup_right)
      inv' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩

@[simp, to_additive, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align group_seminorm.coe_sup GroupSeminorm.coe_sup
#align add_group_seminorm.coe_sup AddGroupSeminorm.coe_sup

@[simp, to_additive]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_seminorm.sup_apply GroupSeminorm.sup_apply
#align add_group_seminorm.sup_apply AddGroupSeminorm.sup_apply

@[to_additive]
instance : SemilatticeSup (GroupSeminorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive
      "Composition of an additive group seminorm with an additive monoid homomorphism as an\nadditive group seminorm."]
def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F
    where
  toFun x := p (f x)
  map_one' := by rw [f.map_one, map_one_eq_zero p]
  mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le <| map_mul_le_add p _ _
  inv' x := by rw [map_inv, map_inv_eq_map p]
#align group_seminorm.comp GroupSeminorm.comp
#align add_group_seminorm.comp AddGroupSeminorm.comp

@[simp, to_additive]
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl
#align group_seminorm.coe_comp GroupSeminorm.coe_comp
#align add_group_seminorm.coe_comp AddGroupSeminorm.coe_comp

@[simp, to_additive]
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl
#align group_seminorm.comp_apply GroupSeminorm.comp_apply
#align add_group_seminorm.comp_apply AddGroupSeminorm.comp_apply

@[simp, to_additive]
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl
#align group_seminorm.comp_id GroupSeminorm.comp_id
#align add_group_seminorm.comp_id AddGroupSeminorm.comp_id

@[simp, to_additive]
theorem comp_zero : p.comp (1 : F →* E) = 0 :=
  ext fun _ => map_one_eq_zero p
#align group_seminorm.comp_zero GroupSeminorm.comp_zero
#align add_group_seminorm.comp_zero AddGroupSeminorm.comp_zero

@[simp, to_additive]
theorem zero_comp : (0 : GroupSeminorm E).comp f = 0 :=
  ext fun _ => rfl
#align group_seminorm.zero_comp GroupSeminorm.zero_comp
#align add_group_seminorm.zero_comp AddGroupSeminorm.zero_comp

@[to_additive]
theorem comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl
#align group_seminorm.comp_assoc GroupSeminorm.comp_assoc
#align add_group_seminorm.comp_assoc AddGroupSeminorm.comp_assoc

@[to_additive]
theorem add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl
#align group_seminorm.add_comp GroupSeminorm.add_comp
#align add_group_seminorm.add_comp AddGroupSeminorm.add_comp

variable {p q}

@[to_additive]
theorem comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ => hp _
#align group_seminorm.comp_mono GroupSeminorm.comp_mono
#align add_group_seminorm.comp_mono AddGroupSeminorm.comp_mono

end Group

section CommGroup

variable [CommGroup E] [CommGroup F] (p q : GroupSeminorm E) (x y : E)

@[to_additive]
theorem comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g := fun _ =>
  map_mul_le_add p _ _
#align group_seminorm.comp_mul_le GroupSeminorm.comp_mul_le
#align add_group_seminorm.comp_add_le AddGroupSeminorm.comp_add_le

@[to_additive]
theorem mul_bddBelow_range_add {p q : GroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x / y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
#align group_seminorm.mul_bdd_below_range_add GroupSeminorm.mul_bddBelow_range_add
#align add_group_seminorm.add_bdd_below_range_add AddGroupSeminorm.add_bddBelow_range_add

@[to_additive]
noncomputable instance : HasInf (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt (fun x => by positivity) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
      mul_le' := fun x y =>
        le_cinfᵢ_add_cinfᵢ fun u v =>
          by
          refine' cinfᵢ_le_of_le mul_bdd_below_range_add (u * v) _
          rw [mul_div_mul_comm, add_add_add_comm]
          exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _)
      inv' := fun x =>
        (inv_surjective.infᵢ_comp _).symm.trans <| by
          simp_rw [map_inv_eq_map p, ← inv_div', map_inv_eq_map q] }⟩

@[simp, to_additive]
theorem inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) :=
  rfl
#align group_seminorm.inf_apply GroupSeminorm.inf_apply
#align add_group_seminorm.inf_apply AddGroupSeminorm.inf_apply

@[to_additive]
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      cinfᵢ_le_of_le mul_bddBelow_range_add x <| by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
      cinfᵢ_le_of_le mul_bddBelow_range_add (1 : E) <| by
        simp only [div_one, map_one_eq_zero p, zero_add]
    le_inf := fun a b c hb hc x =>
      le_cinfᵢ fun u => (le_map_add_map_div a _ _).trans <| add_le_add (hb _) (hc _) }

end CommGroup

end GroupSeminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `has_smul R ℝ` should be fixed because `ℝ` is fixed. -/
namespace AddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (p : AddGroupSeminorm E)

instance [DecidableEq E] : One (AddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
theorem apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_seminorm.apply_one AddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance : SMul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
      add_le' := fun _ _ =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        exact
          (mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) <| NNReal.coe_nonneg _).trans_eq
            (mul_add _ _ _)
      neg' := fun x => by rw [map_neg_eq_map] }⟩

@[simp, norm_cast]
theorem coe_smul (r : R) (p : AddGroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smul

@[simp]
theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align add_group_seminorm.smul_apply AddGroupSeminorm.smul_apply

instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (AddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a (p x)⟩

theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align add_group_seminorm.smul_sup AddGroupSeminorm.smul_sup

end AddGroupSeminorm

namespace NonarchAddGroupSeminorm

section AddGroup

variable [AddGroup E] [AddGroup F] [AddGroup G] {p q : NonarchAddGroupSeminorm E}

instance nonarchAddGroupSeminormClass : NonarchAddGroupSeminormClass (NonarchAddGroupSeminorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
#align nonarch_add_group_seminorm.nonarch_add_group_seminorm_class NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (NonarchAddGroupSeminorm E) fun _ => E → ℝ :=
  ⟨NonarchAddGroupSeminorm.toFun⟩

@[simp]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align nonarch_add_group_seminorm.to_fun_eq_coe NonarchAddGroupSeminorm.toFun_eq_coe

@[ext]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align nonarch_add_group_seminorm.ext NonarchAddGroupSeminorm.ext

noncomputable instance : PartialOrder (NonarchAddGroupSeminorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_seminorm.le_def NonarchAddGroupSeminorm.le_def

theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_seminorm.lt_def NonarchAddGroupSeminorm.lt_def

@[simp, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nonarch_add_group_seminorm.coe_le_coe NonarchAddGroupSeminorm.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align nonarch_add_group_seminorm.coe_lt_coe NonarchAddGroupSeminorm.coe_lt_coe

variable (p q) (f : F →+ E)

instance : Zero (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply, max_eq_right]
      neg' := fun x => rfl }⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : NonarchAddGroupSeminorm E) = 0 :=
  rfl
#align nonarch_add_group_seminorm.coe_zero NonarchAddGroupSeminorm.coe_zero

@[simp]
theorem zero_apply (x : E) : (0 : NonarchAddGroupSeminorm E) x = 0 :=
  rfl
#align nonarch_add_group_seminorm.zero_apply NonarchAddGroupSeminorm.zero_apply

instance : Inhabited (NonarchAddGroupSeminorm E) :=
  ⟨0⟩

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
instance : HasSup (NonarchAddGroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup_right le_sup_right)
      neg' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_neg_eq_map p, map_neg_eq_map q] }⟩

@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align nonarch_add_group_seminorm.coe_sup NonarchAddGroupSeminorm.coe_sup

@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_seminorm.sup_apply NonarchAddGroupSeminorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupSeminorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

end AddGroup

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] (p q : NonarchAddGroupSeminorm E) (x y : E)

theorem add_bddBelow_range_add {p q : NonarchAddGroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x - y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
#align nonarch_add_group_seminorm.add_bdd_below_range_add NonarchAddGroupSeminorm.add_bddBelow_range_add

end AddCommGroup

end NonarchAddGroupSeminorm

namespace GroupSeminorm

variable [Group E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

@[to_additive AddGroupSeminorm.hasOne]
instance [DecidableEq E] : One (GroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
      inv' := fun x => by simp_rw [inv_eq_one] }⟩

@[simp, to_additive AddGroupSeminorm.apply_one]
theorem apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_seminorm.apply_one GroupSeminorm.apply_one
#align add_group_seminorm.apply_one AddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
@[to_additive AddGroupSeminorm.hasSmul]
instance : SMul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        exact
          (mul_le_mul_of_nonneg_left (map_mul_le_add p _ _) <| NNReal.coe_nonneg _).trans_eq
            (mul_add _ _ _)
      inv' := fun x => by rw [map_inv_eq_map p] }⟩

@[to_additive AddGroupSeminorm.isScalarTower]
instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (GroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

@[simp, to_additive AddGroupSeminorm.coe_smul, norm_cast]
theorem coe_smul (r : R) (p : GroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align group_seminorm.coe_smul GroupSeminorm.coe_smul
#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smul

@[simp, to_additive AddGroupSeminorm.smul_apply]
theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align group_seminorm.smul_apply GroupSeminorm.smul_apply
#align add_group_seminorm.smul_apply AddGroupSeminorm.smul_apply

@[to_additive AddGroupSeminorm.smul_sup]
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align group_seminorm.smul_sup GroupSeminorm.smul_sup
#align add_group_seminorm.smul_sup AddGroupSeminorm.smul_sup

end GroupSeminorm

namespace NonarchAddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

instance [DecidableEq E] : One (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · rw [if_neg hx]
          split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_seminorm.apply_one NonarchAddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a `nonarch_add_group_seminorm`. -/
instance : SMul R (NonarchAddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←
          mul_max_of_nonneg _ _ NNReal.zero_le_coe]
        exact mul_le_mul_of_nonneg_left (map_add_le_max p _ _) NNReal.zero_le_coe
      neg' := fun x => by rw [map_neg_eq_map p] }⟩

instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (NonarchAddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

@[simp, norm_cast]
theorem coe_smul (r : R) (p : NonarchAddGroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align nonarch_add_group_seminorm.coe_smul NonarchAddGroupSeminorm.coe_smul

@[simp]
theorem smul_apply (r : R) (p : NonarchAddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align nonarch_add_group_seminorm.smul_apply NonarchAddGroupSeminorm.smul_apply

theorem smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align nonarch_add_group_seminorm.smul_sup NonarchAddGroupSeminorm.smul_sup

end NonarchAddGroupSeminorm

/-! ### Norms -/


namespace GroupNorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupNorm E}

@[to_additive]
instance groupNormClass : GroupNormClass (GroupNorm E) E ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero'
#align group_norm.group_norm_class GroupNorm.groupNormClass
#align add_group_norm.add_group_norm_class AddGroupNorm.add_group_norm_class

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun` directly. "]
instance : CoeFun (GroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

@[simp, to_additive]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align group_norm.to_fun_eq_coe GroupNorm.toFun_eq_coe
#align add_group_norm.to_fun_eq_coe AddGroupNorm.toFun_eq_coe

@[ext, to_additive]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align group_norm.ext GroupNorm.ext
#align add_group_norm.ext AddGroupNorm.ext

@[to_additive]
instance : PartialOrder (GroupNorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

@[to_additive]
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_norm.le_def GroupNorm.le_def
#align add_group_norm.le_def AddGroupNorm.le_def

@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_norm.lt_def GroupNorm.lt_def
#align add_group_norm.lt_def AddGroupNorm.lt_def

@[simp, to_additive, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_norm.coe_le_coe GroupNorm.coe_le_coe
#align add_group_norm.coe_le_coe AddGroupNorm.coe_le_coe

@[simp, to_additive, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_norm.coe_lt_coe GroupNorm.coe_lt_coe
#align add_group_norm.coe_lt_coe AddGroupNorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance : Add (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[simp, to_additive]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_norm.coe_add GroupNorm.coe_add
#align add_group_norm.coe_add AddGroupNorm.coe_add

@[simp, to_additive]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_norm.add_apply GroupNorm.add_apply
#align add_group_norm.add_apply AddGroupNorm.add_apply

-- TODO: define `has_Sup`
@[to_additive]
instance : HasSup (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_one p h }⟩

@[simp, to_additive, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align group_norm.coe_sup GroupNorm.coe_sup
#align add_group_norm.coe_sup AddGroupNorm.coe_sup

@[simp, to_additive]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_norm.sup_apply GroupNorm.sup_apply
#align add_group_norm.sup_apply AddGroupNorm.sup_apply

@[to_additive]
instance : SemilatticeSup (GroupNorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

end Group

end GroupNorm

namespace AddGroupNorm

variable [AddGroup E] [DecidableEq E]

instance : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
theorem apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_norm.apply_one AddGroupNorm.apply_one

instance : Inhabited (AddGroupNorm E) :=
  ⟨1⟩

end AddGroupNorm

namespace GroupNorm

variable [Group E] [DecidableEq E]

@[to_additive AddGroupNorm.hasOne]
instance : One (GroupNorm E) :=
  ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp, to_additive AddGroupNorm.apply_one]
theorem apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_norm.apply_one GroupNorm.apply_one
#align add_group_norm.apply_one AddGroupNorm.apply_one

@[to_additive]
instance : Inhabited (GroupNorm E) :=
  ⟨1⟩

end GroupNorm

namespace NonarchAddGroupNorm

section AddGroup

variable [AddGroup E] [AddGroup F] {p q : NonarchAddGroupNorm E}

instance nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero'
#align nonarch_add_group_norm.nonarch_add_group_norm_class NonarchAddGroupNorm.nonarchAddGroupNormClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
noncomputable instance : CoeFun (NonarchAddGroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align nonarch_add_group_norm.to_fun_eq_coe NonarchAddGroupNorm.toFun_eq_coe

@[ext]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align nonarch_add_group_norm.ext NonarchAddGroupNorm.ext

noncomputable instance : PartialOrder (NonarchAddGroupNorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_norm.le_def NonarchAddGroupNorm.le_def

theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_norm.lt_def NonarchAddGroupNorm.lt_def

@[simp, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nonarch_add_group_norm.coe_le_coe NonarchAddGroupNorm.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align nonarch_add_group_norm.coe_lt_coe NonarchAddGroupNorm.coe_lt_coe

variable (p q) (f : F →+ E)

instance : HasSup (NonarchAddGroupNorm E) :=
  ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align nonarch_add_group_norm.coe_sup NonarchAddGroupNorm.coe_sup

@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_norm.sup_apply NonarchAddGroupNorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupNorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

instance [DecidableEq E] : One (NonarchAddGroupNorm E) :=
  ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_norm.apply_one NonarchAddGroupNorm.apply_one

instance [DecidableEq E] : Inhabited (NonarchAddGroupNorm E) :=
  ⟨1⟩

end AddGroup

end NonarchAddGroupNorm

