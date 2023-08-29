/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.NNReal
import Mathlib.Tactic.GCongr

#align_import analysis.normed.group.seminorm from "leanprover-community/mathlib"@"09079525fd01b3dda35e96adaa08d2f943e1648c"

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `AddGroupSeminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `NonarchAddGroupSeminorm`: A function `f` from an additive group `G` to the reals that
  preserves zero, takes nonnegative values, is nonarchimedean and such that `f (-x) = f x`
  for all `x`.
* `GroupSeminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `AddGroupNorm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `NonarchAddGroupNorm`: A nonarchimedean seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `GroupNorm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## Notes

The corresponding hom classes are defined in `Analysis.Order.Hom.Basic` to be used by absolute
values.

We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm` to avoid
having a superfluous `add_le'` field in the resulting structure. The same applies to
`NonarchAddGroupNorm`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
-/


open Set

open NNReal

variable {ι R R' E F G : Type*}

/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
structure AddGroupSeminorm (G : Type*) [AddGroup G] where
  -- porting note: can't extend `ZeroHom G ℝ` because otherwise `to_additive` won't work since
  -- we aren't using old structures
  /-- The bare function of an `AddGroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of zero is zero. -/
  protected map_zero' : toFun 0 = 0
  /-- The seminorm is subadditive. -/
  protected add_le' : ∀ r s, toFun (r + s) ≤ toFun r + toFun s
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r
#align add_group_seminorm AddGroupSeminorm

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive]
structure GroupSeminorm (G : Type*) [Group G] where
  /-- The bare function of a `GroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of one is zero. -/
  protected map_one' : toFun 1 = 0
  /-- The seminorm applied to a product is dominated by the sum of the seminorm applied to the
  factors. -/
  protected mul_le' : ∀ x y, toFun (x * y) ≤ toFun x + toFun y
  /-- The seminorm is invariant under inversion. -/
  protected inv' : ∀ x, toFun x⁻¹ = toFun x
#align group_seminorm GroupSeminorm

/-- A nonarchimedean seminorm on an additive group `G` is a function `f : G → ℝ` that preserves
zero, is nonarchimedean and such that `f (-x) = f x` for all `x`. -/
structure NonarchAddGroupSeminorm (G : Type*) [AddGroup G] extends ZeroHom G ℝ where
  /-- The seminorm applied to a sum is dominated by the maximum of the function applied to the
  addends. -/
  protected add_le_max' : ∀ r s, toFun (r + s) ≤ max (toFun r) (toFun s)
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r
#align nonarch_add_group_seminorm NonarchAddGroupSeminorm

/-! NOTE: We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm`
  to avoid having a superfluous `add_le'` field in the resulting structure. The same applies to
  `NonarchAddGroupNorm` below. -/


/-- A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
structure AddGroupNorm (G : Type*) [AddGroup G] extends AddGroupSeminorm G where
  /-- If the image under the seminorm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
#align add_group_norm AddGroupNorm

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[to_additive]
structure GroupNorm (G : Type*) [Group G] extends GroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is one. -/
  protected eq_one_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 1
#align group_norm GroupNorm

/-- A nonarchimedean norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
nonarchimedean and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
structure NonarchAddGroupNorm (G : Type*) [AddGroup G] extends NonarchAddGroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0
#align nonarch_add_group_norm NonarchAddGroupNorm

/-- `NonarchAddGroupSeminormClass F α` states that `F` is a type of nonarchimedean seminorms on
the additive group `α`.

You should extend this class when you extend `NonarchAddGroupSeminorm`. -/
class NonarchAddGroupSeminormClass (F : Type*) (α : outParam <| Type*) [AddGroup α] extends
  NonarchimedeanHomClass F α ℝ where
  /-- The image of zero is zero. -/
  protected map_zero (f : F) : f 0 = 0
  /-- The seminorm is invariant under negation. -/
  protected map_neg_eq_map' (f : F) (a : α) : f (-a) = f a
#align nonarch_add_group_seminorm_class NonarchAddGroupSeminormClass

/-- `NonarchAddGroupNormClass F α` states that `F` is a type of nonarchimedean norms on the
additive group `α`.

You should extend this class when you extend `NonarchAddGroupNorm`. -/
class NonarchAddGroupNormClass (F : Type*) (α : outParam <| Type*) [AddGroup α] extends
  NonarchAddGroupSeminormClass F α where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0
#align nonarch_add_group_norm_class NonarchAddGroupNormClass

section NonarchAddGroupSeminormClass

variable [AddGroup E] [NonarchAddGroupSeminormClass F E] (f : F) (x y : E)

theorem map_sub_le_max : f (x - y) ≤ max (f x) (f y) := by
  rw [sub_eq_add_neg, ← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  -- ⊢ ↑f (x + -y) ≤ max (↑f x) (↑f (-y))
  exact map_add_le_max _ _ _
  -- 🎉 no goals
#align map_sub_le_max map_sub_le_max

end NonarchAddGroupSeminormClass

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupSeminormClass.toAddGroupSeminormClass [AddGroup E]
    [NonarchAddGroupSeminormClass F E] : AddGroupSeminormClass F E ℝ :=
  { ‹NonarchAddGroupSeminormClass F E› with
    map_add_le_add := fun f x y =>
      haveI h_nonneg : ∀ a, 0 ≤ f a := by
        intro a
        -- ⊢ 0 ≤ ↑f a
        rw [← NonarchAddGroupSeminormClass.map_zero f, ← sub_self a]
        -- ⊢ ↑f (a - a) ≤ ↑f a
        exact le_trans (map_sub_le_max _ _ _) (by rw [max_self (f a)])
        -- 🎉 no goals
      le_trans (map_add_le_max _ _ _)
        (max_le (le_add_of_nonneg_right (h_nonneg _)) (le_add_of_nonneg_left (h_nonneg _)))
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }
#align nonarch_add_group_seminorm_class.to_add_group_seminorm_class NonarchAddGroupSeminormClass.toAddGroupSeminormClass

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupNormClass.toAddGroupNormClass [AddGroup E]
    [NonarchAddGroupNormClass F E] : AddGroupNormClass F E ℝ :=
  { ‹NonarchAddGroupNormClass F E› with
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
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, map_one' := map_one'✝, mul_le' := mul_le'✝, inv' := inv'✝ …
                                      -- ⊢ { toFun := toFun✝¹, map_one' := map_one'✝¹, mul_le' := mul_le'✝¹, inv' := in …
                                               -- 🎉 no goals
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
#align group_seminorm.group_seminorm_class GroupSeminorm.groupSeminormClass
#align add_group_seminorm.add_group_seminorm_class AddGroupSeminorm.addGroupSeminormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`FunLike.hasCoeToFun`. "]
instance : CoeFun (GroupSeminorm E) fun _ => E → ℝ :=
  ⟨FunLike.coe⟩

@[to_additive (attr := simp)]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align group_seminorm.to_fun_eq_coe GroupSeminorm.toFun_eq_coe
#align add_group_seminorm.to_fun_eq_coe AddGroupSeminorm.toFun_eq_coe

@[to_additive (attr := ext)]
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

@[to_additive (attr := simp, norm_cast)]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_seminorm.coe_le_coe GroupSeminorm.coe_le_coe
#align add_group_seminorm.coe_le_coe AddGroupSeminorm.coe_le_coe

@[to_additive (attr := simp, norm_cast)]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_seminorm.coe_lt_coe GroupSeminorm.coe_lt_coe
#align add_group_seminorm.coe_lt_coe AddGroupSeminorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance instZeroGroupSeminorm : Zero (GroupSeminorm E) :=
  ⟨{  toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun _ => rfl }⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_zero : ⇑(0 : GroupSeminorm E) = 0 :=
  rfl
#align group_seminorm.coe_zero GroupSeminorm.coe_zero
#align add_group_seminorm.coe_zero AddGroupSeminorm.coe_zero

@[to_additive (attr := simp)]
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
      map_one' := by simp_rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
                     -- 🎉 no goals
      mul_le' := fun _ _ =>
        (add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq <|
          add_add_add_comm _ _ _ _
      inv' := fun x => by simp_rw [map_inv_eq_map p, map_inv_eq_map q] }⟩
                          -- 🎉 no goals

@[to_additive (attr := simp)]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_seminorm.coe_add GroupSeminorm.coe_add
#align add_group_seminorm.coe_add AddGroupSeminorm.coe_add

@[to_additive (attr := simp)]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_seminorm.add_apply GroupSeminorm.add_apply
#align add_group_seminorm.add_apply AddGroupSeminorm.add_apply

-- TODO: define `SupSet` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive]
instance : Sup (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply, ← map_one_eq_zero p, sup_eq_left, map_one_eq_zero p, map_one_eq_zero q]
        -- 🎉 no goals
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_mul_le_add q x y).trans <| add_le_add le_sup_right le_sup_right)
      inv' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩
                          -- 🎉 no goals

@[to_additive (attr := simp, norm_cast)]
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl
#align group_seminorm.coe_sup GroupSeminorm.coe_sup
#align add_group_seminorm.coe_sup AddGroupSeminorm.coe_sup

@[to_additive (attr := simp)]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_seminorm.sup_apply GroupSeminorm.sup_apply
#align add_group_seminorm.sup_apply AddGroupSeminorm.sup_apply

@[to_additive]
instance semilatticeSup : SemilatticeSup (GroupSeminorm E) :=
  FunLike.coe_injective.semilatticeSup _ coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive "Composition of an additive group seminorm with an additive monoid homomorphism as an
additive group seminorm."]
def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F
    where
  toFun x := p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
                 -- 🎉 no goals
  mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le <| map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]
               -- 🎉 no goals
#align group_seminorm.comp GroupSeminorm.comp
#align add_group_seminorm.comp AddGroupSeminorm.comp

@[to_additive (attr := simp)]
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl
#align group_seminorm.coe_comp GroupSeminorm.coe_comp
#align add_group_seminorm.coe_comp AddGroupSeminorm.coe_comp

@[to_additive (attr := simp)]
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl
#align group_seminorm.comp_apply GroupSeminorm.comp_apply
#align add_group_seminorm.comp_apply AddGroupSeminorm.comp_apply

@[to_additive (attr := simp)]
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl
#align group_seminorm.comp_id GroupSeminorm.comp_id
#align add_group_seminorm.comp_id AddGroupSeminorm.comp_id

@[to_additive (attr := simp)]
theorem comp_zero : p.comp (1 : F →* E) = 0 :=
  ext fun _ => map_one_eq_zero p
#align group_seminorm.comp_zero GroupSeminorm.comp_zero
#align add_group_seminorm.comp_zero AddGroupSeminorm.comp_zero

@[to_additive (attr := simp)]
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
    -- ⊢ 0 ≤ (fun y => ↑p y + ↑q (x✝ / y)) x
    dsimp
    -- ⊢ 0 ≤ ↑p x + ↑q (x✝ / x)
    positivity⟩
    -- 🎉 no goals
#align group_seminorm.mul_bdd_below_range_add GroupSeminorm.mul_bddBelow_range_add
#align add_group_seminorm.add_bdd_below_range_add AddGroupSeminorm.add_bddBelow_range_add

@[to_additive]
noncomputable instance : Inf (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
          -- porting note: replace `add_nonneg` with `positivity` once we have the extension
          (fun x => add_nonneg (map_nonneg _ _) (map_nonneg _ _)) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
                 -- 🎉 no goals
      mul_le' := fun x y =>
        le_ciInf_add_ciInf fun u v => by
          refine' ciInf_le_of_le mul_bddBelow_range_add (u * v) _
          -- ⊢ ↑p (u * v) + ↑q (x * y / (u * v)) ≤ ↑p u + ↑q (x / u) + (↑p v + ↑q (y / v))
          rw [mul_div_mul_comm, add_add_add_comm]
          -- ⊢ ↑p (u * v) + ↑q (x / u * (y / v)) ≤ ↑p u + ↑p v + (↑q (x / u) + ↑q (y / v))
          exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _)
          -- 🎉 no goals
      inv' := fun x =>
        (inv_surjective.iInf_comp _).symm.trans <| by
          simp_rw [map_inv_eq_map p, ← inv_div', map_inv_eq_map q] }⟩
          -- 🎉 no goals

@[to_additive (attr := simp)]
theorem inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) :=
  rfl
#align group_seminorm.inf_apply GroupSeminorm.inf_apply
#align add_group_seminorm.inf_apply AddGroupSeminorm.inf_apply

@[to_additive]
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      ciInf_le_of_le mul_bddBelow_range_add x <| by rw [div_self', map_one_eq_zero q, add_zero]
                                                    -- 🎉 no goals
    inf_le_right := fun p q x =>
      ciInf_le_of_le mul_bddBelow_range_add (1 : E) <| by
        simpa only [div_one x, map_one_eq_zero p, zero_add (q x)] using le_rfl
        -- 🎉 no goals
    le_inf := fun a b c hb hc x =>
      le_ciInf fun u => (le_map_add_map_div a _ _).trans <| add_le_add (hb _) (hc _) }

end CommGroup

end GroupSeminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `SMul R ℝ` should be fixed because `ℝ` is fixed. -/
namespace AddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (p : AddGroupSeminorm E)

instance toOne [DecidableEq E] : One (AddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        -- ⊢ (fun x => if x = 0 then 0 else 1) (x + y) ≤ (fun x => if x = 0 then 0 else 1 …
        · simp only
          -- ⊢ (if x + y = 0 then 0 else 1) ≤ (if x = 0 then 0 else 1) + if y = 0 then 0 el …
          rw [if_pos hx, hx, zero_add, zero_add]
          -- 🎉 no goals
        · simp only
          -- ⊢ (if x + y = 0 then 0 else 1) ≤ (if x = 0 then 0 else 1) + if y = 0 then 0 el …
          rw [if_neg hx]
          -- ⊢ (if x + y = 0 then 0 else 1) ≤ 1 + if y = 0 then 0 else 1
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
          -- ⊢ (if x + y = 0 then 0 else 1) ≤ 1
                                                 -- ⊢ 0 ≤ 1
                                                 -- ⊢ 0 ≤ 0
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩
                          -- 🎉 no goals

@[simp]
theorem apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_seminorm.apply_one AddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`. -/
instance toSMul : SMul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
        -- 🎉 no goals
      add_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ← mul_add]
        -- ⊢ ↑(r • 1) * ↑p (x✝¹ + x✝) ≤ ↑(r • 1) * (↑p x✝¹ + ↑p x✝)
        gcongr
        -- ⊢ ↑p (x✝¹ + x✝) ≤ ↑p x✝¹ + ↑p x✝
        apply map_add_le_add
        -- 🎉 no goals
      neg' := fun x => by simp_rw [map_neg_eq_map] }⟩
                          -- 🎉 no goals

@[simp, norm_cast]
theorem coe_smul (r : R) (p : AddGroupSeminorm E) : ⇑(r • p) = r • ⇑p :=
  rfl
#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smul

@[simp]
theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align add_group_seminorm.smul_apply AddGroupSeminorm.smul_apply

instance isScalarTower [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R']
    [IsScalarTower R R' ℝ] : IsScalarTower R R' (AddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a (p x)⟩

theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun x => Real.smul_max _ _
#align add_group_seminorm.smul_sup AddGroupSeminorm.smul_sup

end AddGroupSeminorm

namespace NonarchAddGroupSeminorm

section AddGroup

variable [AddGroup E] [AddGroup F] [AddGroup G] {p q : NonarchAddGroupSeminorm E}

instance nonarchAddGroupSeminormClass : NonarchAddGroupSeminormClass (NonarchAddGroupSeminorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _, _⟩ := f; cases g; congr
                             -- ⊢ { toZeroHom := { toFun := toFun✝, map_zero' := map_zero'✝ }, add_le_max' :=  …
                                                         -- ⊢ { toZeroHom := { toFun := toFun✝, map_zero' := map_zero'✝ }, add_le_max' :=  …
                                                                  -- 🎉 no goals
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
#align nonarch_add_group_seminorm.nonarch_add_group_seminorm_class NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
instance : CoeFun (NonarchAddGroupSeminorm E) fun _ => E → ℝ :=
  ⟨FunLike.coe⟩

-- porting note: `simpNF` said the left hand side simplified to this
@[simp]
theorem toZeroHom_eq_coe : ⇑p.toZeroHom = p := by
  rfl
  -- 🎉 no goals
#align nonarch_add_group_seminorm.to_fun_eq_coe NonarchAddGroupSeminorm.toZeroHom_eq_coe

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
      add_le_max' := fun r s => by simp only [Pi.zero_apply]; rw [max_eq_right]; rfl
                                   -- ⊢ 0 ≤ max 0 0
                                                              -- ⊢ 0 ≤ 0
                                                                                 -- 🎉 no goals
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

-- TODO: define `SupSet` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
instance : Sup (NonarchAddGroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
                      -- 🎉 no goals
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup_right le_sup_right)
      neg' := fun x => by simp_rw [Pi.sup_apply, map_neg_eq_map p, map_neg_eq_map q]}⟩
                          -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl
#align nonarch_add_group_seminorm.coe_sup NonarchAddGroupSeminorm.coe_sup

@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_seminorm.sup_apply NonarchAddGroupSeminorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupSeminorm E) :=
  FunLike.coe_injective.semilatticeSup _ coe_sup

end AddGroup

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] (p q : NonarchAddGroupSeminorm E) (x y : E)

theorem add_bddBelow_range_add {p q : NonarchAddGroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x - y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    -- ⊢ 0 ≤ (fun y => ↑p y + ↑q (x✝ - y)) x
    dsimp
    -- ⊢ 0 ≤ ↑p x + ↑q (x✝ - x)
    positivity⟩
    -- 🎉 no goals
#align nonarch_add_group_seminorm.add_bdd_below_range_add NonarchAddGroupSeminorm.add_bddBelow_range_add

end AddCommGroup

end NonarchAddGroupSeminorm

namespace GroupSeminorm

variable [Group E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

@[to_additive existing AddGroupSeminorm.toOne]
instance toOne [DecidableEq E] : One (GroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        -- ⊢ (fun x => if x = 1 then 0 else 1) (x * y) ≤ (fun x => if x = 1 then 0 else 1 …
        · simp only
          -- ⊢ (if x * y = 1 then 0 else 1) ≤ (if x = 1 then 0 else 1) + if y = 1 then 0 el …
          rw [if_pos hx, hx, one_mul, zero_add]
          -- 🎉 no goals
        · simp only
          -- ⊢ (if x * y = 1 then 0 else 1) ≤ (if x = 1 then 0 else 1) + if y = 1 then 0 el …
          rw [if_neg hx]
          -- ⊢ (if x * y = 1 then 0 else 1) ≤ 1 + if y = 1 then 0 else 1
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
          -- ⊢ (if x * y = 1 then 0 else 1) ≤ 1
                                                 -- ⊢ 0 ≤ 1
                                                 -- ⊢ 0 ≤ 0
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
      inv' := fun x => by simp_rw [inv_eq_one] }⟩
                          -- 🎉 no goals

@[to_additive (attr := simp) existing AddGroupSeminorm.apply_one]
theorem apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_seminorm.apply_one GroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`. -/
@[to_additive existing AddGroupSeminorm.toSMul]
instance : SMul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←mul_add]
        -- ⊢ ↑(r • 1) * ↑p (x✝¹ * x✝) ≤ ↑(r • 1) * (↑p x✝¹ + ↑p x✝)
        gcongr
        -- ⊢ ↑p (x✝¹ * x✝) ≤ ↑p x✝¹ + ↑p x✝
        apply map_mul_le_add
        -- 🎉 no goals
      inv' := fun x => by simp_rw [map_inv_eq_map p] }⟩
                          -- 🎉 no goals

@[to_additive existing AddGroupSeminorm.isScalarTower]
instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (GroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

@[to_additive (attr := simp, norm_cast) existing AddGroupSeminorm.coe_smul]
theorem coe_smul (r : R) (p : GroupSeminorm E) : ⇑(r • p) = r • ⇑p :=
  rfl
#align group_seminorm.coe_smul GroupSeminorm.coe_smul

@[to_additive (attr := simp) existing AddGroupSeminorm.smul_apply]
theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align group_seminorm.smul_apply GroupSeminorm.smul_apply

@[to_additive existing AddGroupSeminorm.smul_sup]
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun x => Real.smul_max _ _
#align group_seminorm.smul_sup GroupSeminorm.smul_sup

end GroupSeminorm

namespace NonarchAddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

instance [DecidableEq E] : One (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        -- ⊢ ZeroHom.toFun { toFun := fun x => if x = 0 then 0 else 1, map_zero' := (_ :  …
        · simp_rw [if_pos hx, hx, zero_add]
          -- ⊢ (if y = 0 then 0 else 1) ≤ max 0 (if y = 0 then 0 else 1)
          exact le_max_of_le_right (le_refl _)
          -- 🎉 no goals
        · simp_rw [if_neg hx]
          -- ⊢ (if x + y = 0 then 0 else 1) ≤ max 1 (if y = 0 then 0 else 1)
          split_ifs <;> norm_num
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩
                          -- 🎉 no goals

@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_seminorm.apply_one NonarchAddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a `NonarchAddGroupSeminorm`. -/
instance : SMul R (NonarchAddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←
          mul_max_of_nonneg _ _ NNReal.zero_le_coe]
        gcongr
        -- ⊢ ↑p (x + y) ≤ max (↑p x) (↑p y)
        apply map_add_le_max
        -- 🎉 no goals
      neg' := fun x => by simp_rw [map_neg_eq_map p] }⟩
                          -- 🎉 no goals

instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (NonarchAddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

@[simp, norm_cast]
theorem coe_smul (r : R) (p : NonarchAddGroupSeminorm E) : ⇑(r • p) = r • ⇑p :=
  rfl
#align nonarch_add_group_seminorm.coe_smul NonarchAddGroupSeminorm.coe_smul

@[simp]
theorem smul_apply (r : R) (p : NonarchAddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align nonarch_add_group_seminorm.smul_apply NonarchAddGroupSeminorm.smul_apply

theorem smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun x => Real.smul_max _ _
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
  coe_injective' f g h := by obtain ⟨⟨_, _, _, _⟩, _⟩ := f; cases g; congr
                             -- ⊢ { toGroupSeminorm := { toFun := toFun✝, map_one' := map_one'✝, mul_le' := mu …
                                                            -- ⊢ { toGroupSeminorm := { toFun := toFun✝, map_one' := map_one'✝, mul_le' := mu …
                                                                     -- 🎉 no goals
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero' _
#align group_norm.group_norm_class GroupNorm.groupNormClass
#align add_group_norm.add_group_norm_class AddGroupNorm.addGroupNormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`
directly. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`FunLike.hasCoeToFun` directly. "]
instance : CoeFun (GroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

-- porting note: `simpNF` told me the left-hand side simplified to this
@[to_additive (attr := simp)]
theorem toGroupSeminorm_eq_coe : ⇑p.toGroupSeminorm = p :=
  rfl
#align group_norm.to_fun_eq_coe GroupNorm.toGroupSeminorm_eq_coe
#align add_group_norm.to_fun_eq_coe AddGroupNorm.toAddGroupSeminorm_eq_coe

@[to_additive (attr := ext)]
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

@[to_additive (attr := simp, norm_cast)]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_norm.coe_le_coe GroupNorm.coe_le_coe
#align add_group_norm.coe_le_coe AddGroupNorm.coe_le_coe

@[to_additive (attr := simp, norm_cast)]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_norm.coe_lt_coe GroupNorm.coe_lt_coe
#align add_group_norm.coe_lt_coe AddGroupNorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance : Add (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[to_additive (attr := simp)]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_norm.coe_add GroupNorm.coe_add
#align add_group_norm.coe_add AddGroupNorm.coe_add

@[to_additive (attr := simp)]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_norm.add_apply GroupNorm.add_apply
#align add_group_norm.add_apply AddGroupNorm.add_apply

-- TODO: define `SupSet`
@[to_additive]
instance : Sup (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_one p h }⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl
#align group_norm.coe_sup GroupNorm.coe_sup
#align add_group_norm.coe_sup AddGroupNorm.coe_sup

@[to_additive (attr := simp)]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_norm.sup_apply GroupNorm.sup_apply
#align add_group_norm.sup_apply AddGroupNorm.sup_apply

@[to_additive]
instance : SemilatticeSup (GroupNorm E) :=
  FunLike.coe_injective.semilatticeSup _ coe_sup

end Group

end GroupNorm

namespace AddGroupNorm

variable [AddGroup E] [DecidableEq E]

instance : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
theorem apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_norm.apply_one AddGroupNorm.apply_one

instance : Inhabited (AddGroupNorm E) :=
  ⟨1⟩

end AddGroupNorm

namespace GroupNorm

instance _root_.AddGroupNorm.toOne [AddGroup E] [DecidableEq E] : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
    eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

variable [Group E] [DecidableEq E]

@[to_additive existing AddGroupNorm.toOne]
instance toOne : One (GroupNorm E) :=
  ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[to_additive (attr := simp) existing AddGroupNorm.apply_one]
theorem apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_norm.apply_one GroupNorm.apply_one

@[to_additive existing]
instance : Inhabited (GroupNorm E) :=
  ⟨1⟩

end GroupNorm

namespace NonarchAddGroupNorm

section AddGroup

variable [AddGroup E] [AddGroup F] {p q : NonarchAddGroupNorm E}

instance nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := f; cases g; congr
                             -- ⊢ { toNonarchAddGroupSeminorm := { toZeroHom := { toFun := toFun✝, map_zero' : …
                                                              -- ⊢ { toNonarchAddGroupSeminorm := { toZeroHom := { toFun := toFun✝, map_zero' : …
                                                                       -- 🎉 no goals
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _
#align nonarch_add_group_norm.nonarch_add_group_norm_class NonarchAddGroupNorm.nonarchAddGroupNormClass

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun`. -/
noncomputable instance : CoeFun (NonarchAddGroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

-- porting note: `simpNF` told me the left-hand side simplified to this
@[simp]
theorem toNonarchAddGroupSeminorm_eq_coe : ⇑p.toNonarchAddGroupSeminorm = p :=
  rfl
#align nonarch_add_group_norm.to_fun_eq_coe NonarchAddGroupNorm.toNonarchAddGroupSeminorm_eq_coe

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

instance : Sup (NonarchAddGroupNorm E) :=
  ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl
#align nonarch_add_group_norm.coe_sup NonarchAddGroupNorm.coe_sup

@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_norm.sup_apply NonarchAddGroupNorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupNorm E) :=
  FunLike.coe_injective.semilatticeSup _ coe_sup

instance [DecidableEq E] : One (NonarchAddGroupNorm E) :=
  ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_norm.apply_one NonarchAddGroupNorm.apply_one

instance [DecidableEq E] : Inhabited (NonarchAddGroupNorm E) :=
  ⟨1⟩

end AddGroup

end NonarchAddGroupNorm
