/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Data.SetLike.Pointwise
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Module.Submodule.Range

/-! # Pointwise instances on `Submodule`s

This file provides:

* `Submodule.pointwiseNeg`

and the actions

* `Submodule.pointwiseDistribMulAction`
* `Submodule.pointwiseMulActionWithZero`

which matches the action of `Set.mulActionSet`.

This file also provides:
* `Submodule.pointwiseSetSMulSubmodule`: for `R`-module `M`, a `s : Set R` can act on
  `N : Submodule R M` by defining `s • N` to be the smallest submodule containing all `a • n`
  where `a ∈ s` and `n ∈ N`.

These actions are available in the `Pointwise` locale.

## Implementation notes

For an `R`-module `M`, the action of a subset of `R` acting on a submodule of `M` introduced in
section `set_acting_on_submodules` does not have a counterpart in the files
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean` and
`Mathlib/Algebra/GroupWithZero/Submonoid/Pointwise.lean`.

Other than section `DistribMulAction`, most of the lemmas in this file are direct copies of
lemmas from the file `Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.
-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {R : Type*} {M : Type*}

open scoped Pointwise

namespace Submodule

section Neg

section Semiring

variable [Semiring R] [AddCommGroup M] [Module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `Submodule.neg_eq_self`.

Recall that when `R` is the semiring corresponding to the nonnegative elements of `R'`,
`Submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `Pointwise` locale. -/
instance : IsConcreteNeg (Submodule R M) M where
  neg p := { -p.toAddSubmonoid with
    smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }
  coe_set_neg' p := by simp

set_option linter.missingDocs false in
@[instance_reducible, deprecated SetLike.pointwiseNeg (since := "2026-04-30")]
protected def pointwiseNeg : Neg (Submodule R M) where
  neg p :=
    { -p.toAddSubmonoid with
      smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }

open scoped Pointwise

@[deprecated SetLike.coe_set_neg (since := "2026-04-30")]
theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) :=
  rfl

@[simp]
theorem neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid :=
  rfl

@[deprecated SetLike.mem_neg (since := "2026-04-30")]
theorem mem_neg {g : M} {S : Submodule R M} : g ∈ -S ↔ -g ∈ S :=
  Iff.rfl

/-- `Submodule.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible, deprecated SetLike.involutivePointwiseNeg (since := "2026-04-30")]
protected def involutivePointwiseNeg : InvolutiveNeg (Submodule R M) where
  neg_neg _S := SetLike.coe_injective <| neg_neg _

@[deprecated SetLike.neg_le_neg (since := "2026-04-30")]
theorem neg_le_neg {S T : Submodule R M} : -S ≤ -T ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

@[deprecated SetLike.neg_le (since := "2026-04-30")]
theorem neg_le {S T : Submodule R M} : -S ≤ T ↔ S ≤ -T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset

@[deprecated SetLike.neg_eq_self_iff_neg_le (since := "2026-04-30")]
theorem neg_eq_self_iff_neg_le {S : Submodule R M} : -S = S ↔ -S ≤ S :=
  ⟨le_of_eq, fun h => antisymm h <| SetLike.neg_le.mp h⟩

/-- `Submodule.pointwiseNeg` as an order isomorphism. -/
@[deprecated SetLike.negOrderIso (since := "2026-04-30")]
def negOrderIso : Submodule R M ≃o Submodule R M where
  toEquiv := Equiv.neg _
  map_rel_iff' := SetLike.neg_le_neg ..

@[simp]
theorem neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T := rfl

@[simp]
theorem neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T :=
  (SetLike.negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]
theorem neg_bot : -(⊥ : Submodule R M) = ⊥ :=
  SetLike.coe_injective <| (Set.neg_singleton 0).trans <| congr_arg _ neg_zero

@[simp]
theorem neg_top : -(⊤ : Submodule R M) = ⊤ :=
  SetLike.coe_injective <| Set.neg_univ

@[simp]
theorem neg_iInf {ι : Sort*} (S : ι → Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i :=
  (SetLike.negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _

@[simp]
theorem neg_iSup {ι : Sort*} (S : ι → Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i :=
  (SetLike.negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

variable {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]

@[simp] theorem neg_restrictScalars (p : Submodule R M) :
  -(restrictScalars S p) = restrictScalars S (-p) := by ext; simp

end Semiring

open scoped Pointwise

@[simp]
theorem neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -p = p :=
  ext fun _ => p.neg_mem_iff

end Neg

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance pointwiseZero : Zero (Submodule R M) where
  zero := ⊥

instance pointwiseAdd : Add (Submodule R M) where
  add := (· ⊔ ·)

instance pointwiseAddCommMonoid : AddCommMonoid (Submodule R M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

@[simp]
theorem add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

instance : IsOrderedAddMonoid (Submodule R M) where
  add_le_add_left _ _ := sup_le_sup_right

instance : CanonicallyOrderedAdd (Submodule R M) where
  exists_add_of_le {_a b} h := ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add := fun _a _b => le_sup_left

section

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M) where
  smul a S := S.map (DistribSMul.toLinearMap R M a : M →ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
  smul_zero _a := map_bot _
  smul_add _a _S₁ _S₂ := map_sup _ _ _

scoped[Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

theorem pointwise_smul_def {a : α} {S : Submodule R M} :
    a • S = S.map (DistribSMul.toLinearMap R M a) := rfl

open scoped Pointwise

@[simp, norm_cast]
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl

@[simp]
theorem pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

@[simp]
theorem pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
    [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submodule R M) :
    m ∈ a • S ↔ ∃ b ∈ S, a • b = m :=
  Set.mem_smul_set

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

instance : CovariantClass α (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

/-- See also `Submodule.smul_bot`. -/
@[simp]
theorem smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥ :=
  map_bot _

/-- See also `Submodule.smul_sup`. -/
theorem smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/-- See also `Submodule.smul_iSup`. -/
theorem smul_iSup' (a : α) {ι : Sort*} (f : ι → Submodule R M) :
    a • ⨆ i, f i = ⨆ i, a • f i :=
  map_iSup _ _

instance pointwiseCentralScalar [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
    [IsCentralScalar α M] : IsCentralScalar α (Submodule R M) :=
  ⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) <| LinearMap.ext <| op_smul_eq_smul _⟩

@[simp]
theorem smul_le_self_of_tower {α : Type*} [Monoid α] [SMul α R] [DistribMulAction α M]
    [SMulCommClass α R M] [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

end

section

variable [Semiring α] [Module α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. Note that `add_smul` does
not hold so this cannot be stated as a `Module`. -/
@[instance_reducible]
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

/-!
### Sets acting on Submodules

Let `R` be a (semi)ring and `M` an `R`-module. Let `S` be a monoid which acts on `M` distributively,
then subsets of `S` can act on submodules of `M`.
For subset `s ⊆ S` and submodule `N ≤ M`, we define `s • N` to be the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.

#### Results
For arbitrary monoids `S` acting distributively on `M`, there is an induction principle for `s • N`:
To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`

#### Notes
- If we assume the addition on subsets of `R` is the `⊔` and subtraction `⊓` i.e. use `SetSemiring`,
  then this action actually gives a module structure on submodules of `M` over subsets of `R`.
- If we generalize so that `r • N` makes sense for all `r : S`, then `Submodule.singleton_set_smul`
  and `Submodule.singleton_set_smul` can be generalized as well.
-/

section DistribMulAction

variable {S : Type*} [Monoid S]
variable [DistribMulAction S M]

/--
Let `s ⊆ R` be a set and `N ≤ M` be a submodule, then `s • N` is the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.
-/
@[instance_reducible]
protected def pointwiseSetSMul : SMul (Set S) (Submodule R M) where
  smul s N := sInf { p | ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMul

variable (sR : Set R) (s : Set S) (N : Submodule R M)

lemma mem_set_smul_def (x : M) :
    x ∈ s • N ↔
    x ∈ sInf { p : Submodule R M | ∀ ⦃r : S⦄ {n : M}, r ∈ s → n ∈ N → r • n ∈ p } := Iff.rfl

variable {s N} in
@[aesop safe]
lemma mem_set_smul_of_mem_mem {r : S} {m : M} (mem1 : r ∈ s) (mem2 : m ∈ N) :
    r • m ∈ s • N := by
  rw [mem_set_smul_def, mem_sInf]
  exact fun _ h => h mem1 mem2

lemma set_smul_le (p : Submodule R M)
    (closed_under_smul : ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p) :
    s • N ≤ p :=
  sInf_le closed_under_smul

lemma set_smul_le_iff (p : Submodule R M) :
    s • N ≤ p ↔
    ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p := by
  fconstructor
  · intro h r n hr hn
    exact h <| mem_set_smul_of_mem_mem hr hn
  · apply set_smul_le

lemma set_smul_eq_of_le (p : Submodule R M)
    (closed_under_smul : ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p)
    (le : p ≤ s • N) :
    s • N = p :=
  le_antisymm (set_smul_le s N p closed_under_smul) le

instance : CovariantClass (Set S) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ le => set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := hr)
    (mem2 := le hm)⟩

lemma set_smul_mono_left {s t : Set S} (le : s ≤ t) :
    s • N ≤ t • N :=
  set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)

lemma set_smul_le_of_le_le {s t : Set S} {p q : Submodule R M}
    (le_set : s ≤ t) (le_submodule : p ≤ q) : s • p ≤ t • q :=
  le_trans (set_smul_mono_left _ le_set) <| smul_mono_right _ le_submodule

lemma set_smul_eq_iSup [SMulCommClass S R M] (s : Set S) (N : Submodule R M) :
    s • N = ⨆ (a ∈ s), a • N := by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

variable {s N} in
/--
Induction principle for set acting on submodules. To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`
-/
@[elab_as_elim]
lemma set_smul_inductionOn {motive : (x : M) → (_ : x ∈ s • N) → Prop}
    (x : M)
    (hx : x ∈ s • N)
    (smul₀ : ∀ ⦃r : S⦄ ⦃n : M⦄ (mem₁ : r ∈ s) (mem₂ : n ∈ N),
      motive (r • n) (mem_set_smul_of_mem_mem mem₁ mem₂))
    (smul₁ : ∀ (r : R) ⦃m : M⦄ (mem : m ∈ s • N),
      motive m mem → motive (r • m) (Submodule.smul_mem _ r mem)) --
    (add : ∀ ⦃m₁ m₂ : M⦄ (mem₁ : m₁ ∈ s • N) (mem₂ : m₂ ∈ s • N),
      motive m₁ mem₁ → motive m₂ mem₂ → motive (m₁ + m₂) (Submodule.add_mem _ mem₁ mem₂))
    (zero : motive 0 (Submodule.zero_mem _)) :
    motive x hx :=
  let ⟨_, h⟩ := set_smul_le s N
    { carrier := { m | ∃ (mem : m ∈ s • N), motive m mem },
      zero_mem' := ⟨Submodule.zero_mem _, zero⟩
      add_mem' := fun ⟨mem, h⟩ ⟨mem', h'⟩ ↦ ⟨_, add mem mem' h h'⟩
      smul_mem' := fun r _ ⟨mem, h⟩ ↦ ⟨_, smul₁ r mem h⟩ }
    (fun _ _ mem mem' ↦ ⟨mem_set_smul_of_mem_mem mem mem', smul₀ mem mem'⟩) hx
  h

@[simp] lemma empty_set_smul : (∅ : Set S) • N = ⊥ := by
  ext
  fconstructor
  · intro hx
    rw [mem_set_smul_def, Submodule.mem_sInf] at hx
    exact hx ⊥ (fun r _ hr ↦ hr.elim)
  · rintro rfl; exact Submodule.zero_mem _

@[simp] lemma set_smul_bot : s • (⊥ : Submodule R M) = ⊥ :=
  eq_bot_iff.mpr fun x hx ↦ by induction x, hx using set_smul_inductionOn <;> aesop

lemma singleton_set_smul [SMulCommClass S R M] (r : S) : ({r} : Set S) • N = r • N := by
  apply set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_def, Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm

lemma mem_singleton_set_smul [SMulCommClass R S M] (r : S) (x : M) :
    x ∈ ({r} : Set S) • N ↔ ∃ (m : M), m ∈ N ∧ x = r • m := by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ with ⟨m₂, h₂, rfl⟩
      exact ⟨m₁ + m₂, Submodule.add_mem _ h₁ h₂, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  · aesop

lemma smul_inductionOn_pointwise [SMulCommClass S R M] {a : S} {p : (x : M) → x ∈ a • N → Prop}
    (smul₀ : ∀ (s : M) (hs : s ∈ N), p (a • s) (Submodule.smul_mem_pointwise_smul _ _ _ hs))
    (smul₁ : ∀ (r : R) (m : M) (mem : m ∈ a • N), p m mem → p (r • m) (Submodule.smul_mem _ _ mem))
    (add : ∀ (x y : M) (hx : x ∈ a • N) (hy : y ∈ a • N),
      p x hx → p y hy → p (x + y) (Submodule.add_mem _ hx hy))
    (zero : p 0 (Submodule.zero_mem _)) {x : M} (hx : x ∈ a • N) :
    p x hx := by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x ∈ ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn ↦ ?_) smul₁ add zero
  · push _ ∈ _ at hr
    subst hr
    exact smul₀ n hn

lemma sup_set_smul (s t : Set S) :
    (s ⊔ t) • N = s • N ⊔ t • N :=
  set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (mem_set_smul_of_mem_mem hr hn))
    (sup_le (set_smul_mono_left _ le_sup_left) (set_smul_mono_left _ le_sup_right))

end DistribMulAction

section Group

variable {R G M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    {S : Submodule R M}

open MulAction

lemma stabilizer_coe :
    stabilizer G S = stabilizer G (S : Set M) := by
  ext
  rw [mem_stabilizer_iff, SetLike.ext'_iff, coe_pointwise_smul,
    ← mem_stabilizer_iff]

theorem mem_stabilizer_submodule_iff_map_eq {e : G} :
    e ∈ stabilizer G S ↔ S.map (DistribSMul.toLinearMap R M e) = S := by
  rfl

end Group

end Submodule
