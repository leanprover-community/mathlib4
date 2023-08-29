/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Init.Align
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

#align_import data.real.cau_seq from "leanprover-community/mathlib"@"9116dd6709f303dcf781632e15fdef382b0fc579"

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.
There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `IsCauSeq`: a predicate that says `f : ℕ → β` is Cauchy.
* `CauSeq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

set_option autoImplicit true

open IsAbsoluteValue

theorem exists_forall_ge_and {α} [LinearOrder α] {P Q : α → Prop} :
    (∃ i, ∀ j ≥ i, P j) → (∃ i, ∀ j ≥ i, Q j) → ∃ i, ∀ j ≥ i, P j ∧ Q j
  | ⟨a, h₁⟩, ⟨b, h₂⟩ =>
    let ⟨c, ac, bc⟩ := exists_ge_of_linear a b
    ⟨c, fun _ hj => ⟨h₁ _ (le_trans ac hj), h₂ _ (le_trans bc hj)⟩⟩
#align exists_forall_ge_and exists_forall_ge_and

section

variable [LinearOrderedField α] [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ →
      abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    simpa [add_halves, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      lt_of_le_of_lt (abv_add abv _ _) (add_lt_add h₁ h₂)⟩
#align rat_add_continuous_lemma rat_add_continuous_lemma

theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ →
      abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁)  …
  have εK := div_pos (half_pos ε0) K0
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁)  …
  refine' ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => _⟩
  -- ⊢ abv (a₁ * a₂ - b₁ * b₂) < ε
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  -- ⊢ abv (a₁ * a₂ - b₁ * b₂) < ε
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  -- ⊢ abv (a₁ * a₂ - b₁ * b₂) < ε
  set M := max 1 (max K₁ K₂)
  -- ⊢ abv (a₁ * a₂ - b₁ * b₂) < ε
  have : abv (a₁ - b₁) * abv b₂ + abv (a₂ - b₂) * abv a₁ < ε / 2 / M * M + ε / 2 / M * M
  -- ⊢ abv (a₁ - b₁) * abv b₂ + abv (a₂ - b₂) * abv a₁ < ε / 2 / M * M + ε / 2 / M  …
  · gcongr
    -- 🎉 no goals
  rw [← abv_mul abv, mul_comm, div_mul_cancel _ (ne_of_gt K0), ← abv_mul abv, add_halves] at this
  -- ⊢ abv (a₁ * a₂ - b₁ * b₂) < ε
  simpa [sub_eq_add_neg, mul_add, add_mul, add_left_comm] using
    lt_of_le_of_lt (abv_add abv _ _) this
#align rat_mul_continuous_lemma rat_mul_continuous_lemma

theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by
  refine' ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => _⟩
  -- ⊢ abv (a⁻¹ - b⁻¹) < ε
  have a0 := K0.trans_le ha
  -- ⊢ abv (a⁻¹ - b⁻¹) < ε
  have b0 := K0.trans_le hb
  -- ⊢ abv (a⁻¹ - b⁻¹) < ε
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv, abv_inv abv,
    abv_inv abv, abv_sub abv]
  refine' lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right _ b0.le) a0.le
  -- ⊢ abv a * ((abv a)⁻¹ * abv (a - b) * (abv b)⁻¹) * abv b < abv a * ε * abv b
  rw [mul_assoc, inv_mul_cancel_right₀ b0.ne', ← mul_assoc, mul_inv_cancel a0.ne', one_mul]
  -- ⊢ abv (a - b) < abv a * ε * abv b
  refine' h.trans_le _
  -- ⊢ K * ε * K ≤ abv a * ε * abv b
  gcongr
  -- 🎉 no goals
#align rat_inv_continuous_lemma rat_inv_continuous_lemma

end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def IsCauSeq {α : Type*} [LinearOrderedField α] {β : Type*} [Ring β] (abv : β → α) (f : ℕ → β) :
    Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε
#align is_cau_seq IsCauSeq

namespace IsCauSeq

variable [LinearOrderedField α] [Ring β] {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

-- see Note [nolint_ge]
--@[nolint ge_or_gt] -- Porting note: restore attribute
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := by
  refine' (hf _ (half_pos ε0)).imp fun i hi j ij k ik => _
  -- ⊢ abv (f j - f k) < ε
  rw [← add_halves ε]
  -- ⊢ abv (f j - f k) < ε / 2 + ε / 2
  refine' lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _)
  -- ⊢ abv (f i - f k) < ε / 2
  rw [abv_sub abv]; exact hi _ ik
  -- ⊢ abv (f k - f i) < ε / 2
                    -- 🎉 no goals
#align is_cau_seq.cauchy₂ IsCauSeq.cauchy₂

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩
#align is_cau_seq.cauchy₃ IsCauSeq.cauchy₃

theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩
#align is_cau_seq.add IsCauSeq.add

end IsCauSeq

/-- `CauSeq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def CauSeq {α : Type*} [LinearOrderedField α] (β : Type*) [Ring β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }
#align cau_seq CauSeq

namespace CauSeq

variable [LinearOrderedField α]

section Ring

variable [Ring β] {abv : β → α}

instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

-- Porting note: Remove coeFn theorem
/-@[simp]
theorem mk_to_fun (f) (hf : IsCauSeq abv f) : @coeFn (CauSeq β abv) _ _ ⟨f, hf⟩ = f :=
  rfl -/
#noalign cau_seq.mk_to_fun

theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g :=
  Subtype.eq (funext h)
#align cau_seq.ext CauSeq.ext

theorem isCauSeq (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2
#align cau_seq.is_cau CauSeq.isCauSeq

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε := @f.2
#align cau_seq.cauchy CauSeq.cauchy

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩
                  -- ⊢ ε > 0 → ∃ i, ∀ (j : ℕ), j ≥ i → abv (↑f j - ↑f i) < ε
                                                        -- 🎉 no goals
#align cau_seq.of_eq CauSeq.ofEq

variable [IsAbsoluteValue abv]

-- see Note [nolint_ge]
-- @[nolint ge_or_gt] -- Porting note: restore attribute
theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε → ∃ i, ∀ (j) (_ : j ≥ i) (k) (_ : k ≥ i), abv (f j - f k) < ε :=
  f.2.cauchy₂
#align cau_seq.cauchy₂ CauSeq.cauchy₂

theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  f.2.cauchy₃
#align cau_seq.cauchy₃ CauSeq.cauchy₃

theorem bounded (f : CauSeq β abv) : ∃ r, ∀ i, abv (f i) < r := by
  cases' f.cauchy zero_lt_one with i h
  -- ⊢ ∃ r, ∀ (i : ℕ), abv (↑f i) < r
  set R : ℕ → α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  -- ⊢ ∃ r, ∀ (i : ℕ), abv (↑f i) < r
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i := by
    refine' Nat.rec (by simp [hR]) _
    rintro i hi j (rfl | hj)
    · simp
    exact (hi j hj).trans (le_max_left _ _)
  refine' ⟨R i + 1, fun j => _⟩
  -- ⊢ abv (↑f j) < R i + 1
  cases' lt_or_le j i with ij ij
  -- ⊢ abv (↑f j) < R i + 1
  · exact lt_of_le_of_lt (this i _ (le_of_lt ij)) (lt_add_one _)
    -- 🎉 no goals
  · have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ ij))
    -- ⊢ abv (↑f j) < R i + 1
    rw [add_sub, add_comm] at this
    -- ⊢ abv (↑f j) < R i + 1
    simpa using this
    -- 🎉 no goals
#align cau_seq.bounded CauSeq.bounded

theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := f.bounded
  ⟨max r (x + 1), lt_of_lt_of_le (lt_add_one _) (le_max_right _ _), fun i =>
    lt_of_lt_of_le (h i) (le_max_left _ _)⟩
#align cau_seq.bounded' CauSeq.bounded'

instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]
theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : ℕ → β) + g :=
  rfl
#align cau_seq.coe_add CauSeq.coe_add

@[simp, norm_cast]
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
  rfl
#align cau_seq.add_apply CauSeq.add_apply

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv :=
  ⟨fun _ => x, fun ε ε0 => ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩⟩
                                             -- 🎉 no goals
#align cau_seq.const CauSeq.const

variable {abv}

/-- The constant Cauchy sequence -/
local notation "const" => const abv

@[simp, norm_cast]
theorem coe_const (x : β) : (const x : ℕ → β) = Function.const ℕ x :=
  rfl
#align cau_seq.coe_const CauSeq.coe_const

@[simp, norm_cast]
theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x :=
  rfl
#align cau_seq.const_apply CauSeq.const_apply

theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : ℕ → β) 0) h, congr_arg _⟩
#align cau_seq.const_inj CauSeq.const_inj

instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩

instance : One (CauSeq β abv) :=
  ⟨const 1⟩

instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : CauSeq β abv) = 0 :=
  rfl
#align cau_seq.coe_zero CauSeq.coe_zero

@[simp, norm_cast]
theorem coe_one : ⇑(1 : CauSeq β abv) = 1 :=
  rfl
#align cau_seq.coe_one CauSeq.coe_one

@[simp, norm_cast]
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl
#align cau_seq.zero_apply CauSeq.zero_apply

@[simp, norm_cast]
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  rfl
#align cau_seq.one_apply CauSeq.one_apply

@[simp]
theorem const_zero : const 0 = 0 :=
  rfl
#align cau_seq.const_zero CauSeq.const_zero

@[simp]
theorem const_one : const 1 = 1 :=
  rfl
#align cau_seq.const_one CauSeq.const_one

theorem const_add (x y : β) : const (x + y) = const x + const y :=
  rfl
#align cau_seq.const_add CauSeq.const_add

instance : Mul (CauSeq β abv) :=
  ⟨fun f g =>
    ⟨f * g, fun _ ε0 =>
      let ⟨_, _, hF⟩ := f.bounded' 0
      let ⟨_, _, hG⟩ := g.bounded' 0
      let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
      let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
      ⟨i, fun j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp, norm_cast]
theorem coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : ℕ → β) * g :=
  rfl
#align cau_seq.coe_mul CauSeq.coe_mul

@[simp, norm_cast]
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
  rfl
#align cau_seq.mul_apply CauSeq.mul_apply

theorem const_mul (x y : β) : const (x * y) = const x * const y :=
  rfl
#align cau_seq.const_mul CauSeq.const_mul

instance : Neg (CauSeq β abv) :=
  ⟨fun f => ofEq (const (-1) * f) (fun x => -f x) fun i => by simp⟩
                                                              -- 🎉 no goals

@[simp, norm_cast]
theorem coe_neg (f : CauSeq β abv) : ⇑(-f) = -f :=
  rfl
#align cau_seq.coe_neg CauSeq.coe_neg

@[simp, norm_cast]
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl
#align cau_seq.neg_apply CauSeq.neg_apply

theorem const_neg (x : β) : const (-x) = -const x :=
  rfl
#align cau_seq.const_neg CauSeq.const_neg

instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩
                                                             -- 🎉 no goals

@[simp, norm_cast]
theorem coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : ℕ → β) - g :=
  rfl
#align cau_seq.coe_sub CauSeq.coe_sub

@[simp, norm_cast]
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl
#align cau_seq.sub_apply CauSeq.sub_apply

theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  rfl
#align cau_seq.const_sub CauSeq.const_sub

section SMul

variable [SMul G β] [IsScalarTower G β β]

instance : SMul G (CauSeq β abv) :=
  ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : ℕ → β))) fun _ => smul_one_mul _ _⟩

@[simp, norm_cast]
theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : ℕ → β) :=
  rfl
#align cau_seq.coe_smul CauSeq.coe_smul

@[simp, norm_cast]
theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
  rfl
#align cau_seq.smul_apply CauSeq.smul_apply

theorem const_smul (a : G) (x : β) : const (a • x) = a • const x :=
  rfl
#align cau_seq.const_smul CauSeq.const_smul

instance : IsScalarTower G (CauSeq β abv) (CauSeq β abv) :=
  ⟨fun a f g => Subtype.ext <| smul_assoc a (f : ℕ → β) (g : ℕ → β)⟩

end SMul

instance addGroup : AddGroup (CauSeq β abv) :=
  Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance instNatCast : NatCast (CauSeq β abv) := ⟨fun n => const n⟩

instance instIntCast : IntCast (CauSeq β abv) := ⟨fun n => const n⟩

instance addGroupWithOne : AddGroupWithOne (CauSeq β abv) :=
  Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
      -- ⊢ ↑(n✝ • x✝) = n✝ • ↑x✝
              -- 🎉 no goals
  (by intros; rfl)
      -- ⊢ ↑(n✝ • x✝) = n✝ • ↑x✝
              -- 🎉 no goals
  (by intros; rfl)
      -- ⊢ ↑↑n✝ = ↑n✝
              -- 🎉 no goals
  (by intros; rfl)
      -- ⊢ ↑↑n✝ = ↑n✝
              -- 🎉 no goals

instance : Pow (CauSeq β abv) ℕ :=
  ⟨fun f n =>
    (ofEq (npowRec n f) fun i => f i ^ n) <| by induction n <;> simp [*, npowRec, pow_succ]⟩
                                                -- ⊢ ∀ (i : ℕ), ↑(npowRec Nat.zero f) i = ↑f i ^ Nat.zero
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals

@[simp, norm_cast]
theorem coe_pow (f : CauSeq β abv) (n : ℕ) : ⇑(f ^ n) = (f : ℕ → β) ^ n :=
  rfl
#align cau_seq.coe_pow CauSeq.coe_pow

@[simp, norm_cast]
theorem pow_apply (f : CauSeq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n :=
  rfl
#align cau_seq.pow_apply CauSeq.pow_apply

theorem const_pow (x : β) (n : ℕ) : const (x ^ n) = const x ^ n :=
  rfl
#align cau_seq.const_pow CauSeq.const_pow

instance ring : Ring (CauSeq β abv) :=
  Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl

instance {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv] : CommRing (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm := fun a b => ext $ fun n => by simp [mul_left_comm, mul_comm] }
                                             -- 🎉 no goals

/-- `LimZero f` holds when `f` approaches 0. -/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε
#align cau_seq.lim_zero CauSeq.LimZero

theorem add_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun i H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      -- ⊢ abv (↑(f + g) j) < ε
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)
      -- 🎉 no goals
#align cau_seq.add_lim_zero CauSeq.add_limZero

theorem mul_limZero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun i H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      -- ⊢ abv (↑(f * g) j) < ε
      rwa [mul_comm F, div_mul_cancel _ (ne_of_gt F0), ← abv_mul] at this
      -- 🎉 no goals
#align cau_seq.mul_lim_zero_right CauSeq.mul_limZero_right

theorem mul_limZero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun i H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      -- ⊢ abv (↑(f * g) j) < ε
      rwa [div_mul_cancel _ (ne_of_gt G0), ← abv_mul] at this
      -- 🎉 no goals
#align cau_seq.mul_lim_zero_left CauSeq.mul_limZero_left

theorem neg_limZero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul f]
  -- ⊢ LimZero (-1 * f)
  exact mul_limZero_right _ hf
  -- 🎉 no goals
#align cau_seq.neg_lim_zero CauSeq.neg_limZero

theorem sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by
  simpa only [sub_eq_add_neg] using add_limZero hf (neg_limZero hg)
  -- 🎉 no goals
#align cau_seq.sub_lim_zero CauSeq.sub_limZero

theorem limZero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by
  simpa using neg_limZero hfg
  -- 🎉 no goals
#align cau_seq.lim_zero_sub_rev CauSeq.limZero_sub_rev

theorem zero_limZero : LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j _ => by simpa [abv_zero abv] using ε0⟩
                               -- 🎉 no goals
#align cau_seq.zero_lim_zero CauSeq.zero_limZero

theorem const_limZero {x : β} : LimZero (const x) ↔ x = 0 :=
  ⟨fun H =>
    (abv_eq_zero abv).1 <|
      (eq_of_le_of_forall_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
        le_of_lt <| hi _ le_rfl,
    fun e => e.symm ▸ zero_limZero⟩
#align cau_seq.const_lim_zero CauSeq.const_limZero

instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
                 -- 🎉 no goals
    fun f ε hε => by simpa using neg_limZero f ε hε,
                     -- 🎉 no goals
    fun fg gh => by simpa using add_limZero fg gh⟩⟩
                    -- 🎉 no goals
#align cau_seq.equiv CauSeq.equiv

theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 + g1 ≈ f2 + g2 := by simpa only [← add_sub_add_comm] using add_limZero hf hg
                            -- 🎉 no goals
#align cau_seq.add_equiv_add CauSeq.add_equiv_add

theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  simpa only [neg_sub'] using neg_limZero hf
  -- 🎉 no goals
#align cau_seq.neg_equiv_neg CauSeq.neg_equiv_neg

theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)
                            -- 🎉 no goals
#align cau_seq.sub_equiv_sub CauSeq.sub_equiv_sub

theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε :=
  (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun i H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    -- ⊢ abv (↑f k - ↑g j) < ε
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    -- ⊢ abv (↑f k - ↑g j) < ε
    rwa [sub_add_sub_cancel', add_halves] at this
    -- 🎉 no goals
#align cau_seq.equiv_def₃ CauSeq.equiv_def₃

theorem limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  ⟨fun l => by simpa using add_limZero (Setoid.symm h) l, fun l => by simpa using add_limZero h l⟩
               -- 🎉 no goals
                                                                      -- 🎉 no goals
#align cau_seq.lim_zero_congr CauSeq.limZero_congr

theorem abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) := by
  haveI := Classical.propDecidable
  -- ⊢ ∃ K, K > 0 ∧ ∃ i, ∀ (j : ℕ), j ≥ i → K ≤ abv (↑f j)
  by_contra nk
  -- ⊢ False
  refine' hf fun ε ε0 => _
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → abv (↑f j) < ε
  simp [not_forall] at nk
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → abv (↑f j) < ε
  cases' f.cauchy₃ (half_pos ε0) with i hi
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → abv (↑f j) < ε
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → abv (↑f j) < ε
  refine' ⟨j, fun k jk => _⟩
  -- ⊢ abv (↑f k) < ε
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  -- ⊢ abv (↑f k) < ε
  rwa [sub_add_cancel, add_halves] at this
  -- 🎉 no goals
#align cau_seq.abv_pos_of_not_lim_zero CauSeq.abv_pos_of_not_limZero

theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      cases' hi _ le_rfl with h₁ h₂; rw [abv_sub abv] at h₁
      -- ⊢ abv (f j - f i) < ε
                                     -- ⊢ abv (f j - f i) < ε
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      -- ⊢ abv (f j - f i) < ε
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      -- ⊢ abv (f j - f i) < ε
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩
      -- 🎉 no goals
#align cau_seq.of_near CauSeq.of_near

theorem not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f := by
  intro h
  -- ⊢ False
  have : LimZero (f - 0) := by simp [h]
  -- ⊢ False
  exact hf this
  -- 🎉 no goals
#align cau_seq.not_lim_zero_of_not_congr_zero CauSeq.not_limZero_of_not_congr_zero

theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (g * f) := mul_limZero_right _ <| by simpa
                                                      -- 🎉 no goals
  show LimZero (g * f - 0) by simpa
                              -- 🎉 no goals
#align cau_seq.mul_equiv_zero CauSeq.mul_equiv_zero

theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (f * g) := mul_limZero_left _ <| by simpa
                                                     -- 🎉 no goals
  show LimZero (f * g - 0) by simpa
                              -- 🎉 no goals
#align cau_seq.mul_equiv_zero' CauSeq.mul_equiv_zero'

theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  fun (this : LimZero (f * g - 0)) => by
  have hlz : LimZero (f * g) := by simpa
  -- ⊢ False
  have hf' : ¬LimZero f := by simpa using show ¬LimZero (f - 0) from hf
  -- ⊢ False
  have hg' : ¬LimZero g := by simpa using show ¬LimZero (g - 0) from hg
  -- ⊢ False
  rcases abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  -- ⊢ False
  rcases abv_pos_of_not_limZero hg' with ⟨a2, ha2, N2, hN2⟩
  -- ⊢ False
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  -- ⊢ False
  cases' hlz _ this with N hN
  -- ⊢ False
  let i := max N (max N1 N2)
  -- ⊢ False
  have hN' := hN i (le_max_left _ _)
  -- ⊢ False
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))
  -- ⊢ False
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))
  -- ⊢ False
  apply not_le_of_lt hN'
  -- ⊢ a1 * a2 ≤ abv (↑(f * g) i)
  change _ ≤ abv (_ * _)
  -- ⊢ a1 * a2 ≤ abv (↑f i * ↑g i)
  rw [abv_mul abv]
  -- ⊢ a1 * a2 ≤ abv (↑f i) * abv (↑g i)
  gcongr
  -- 🎉 no goals
#align cau_seq.mul_not_equiv_zero CauSeq.mul_not_equiv_zero

theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  show LimZero _ ↔ _ by rw [← const_sub, const_limZero, sub_eq_zero]
                        -- 🎉 no goals
#align cau_seq.const_equiv CauSeq.const_equiv

theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by
  change LimZero (f1 * g1 - f2 * g2)
  -- ⊢ LimZero (f1 * g1 - f2 * g2)
  convert add_limZero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg) using 1
  -- ⊢ f1 * g1 - f2 * g2 = (f1 - f2) * g1 + f2 * (g1 - g2)
  rw [mul_sub, sub_mul]
  -- ⊢ f1 * g1 - f2 * g2 = f1 * g1 - f2 * g1 + (f2 * g1 - f2 * g2)
  -- Porting note: doesn't work with `rw`, but did in Lean 3
  exact (sub_add_sub_cancel (f1*g1) (f2*g1) (f2*g2)).symm
  -- 🎉 no goals
  -- Porting note: was
  /-
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel] using
    add_lim_zero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg)
  -/
#align cau_seq.mul_equiv_mul CauSeq.mul_equiv_mul

theorem smul_equiv_smul [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf
#align cau_seq.smul_equiv_smul CauSeq.smul_equiv_smul

theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : ℕ) : f1 ^ n ≈ f2 ^ n := by
  induction' n with n ih
  -- ⊢ f1 ^ Nat.zero ≈ f2 ^ Nat.zero
  · simp only [Nat.zero_eq, pow_zero, Setoid.refl]
    -- 🎉 no goals
  · simpa only [pow_succ] using mul_equiv_mul hf ih
    -- 🎉 no goals
#align cau_seq.pow_equiv_pow CauSeq.pow_equiv_pow

end Ring

section IsDomain

variable [Ring β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := fun h =>
  have : ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h
  have h1 : abv 1 ≤ 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
      (Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) <| by simpa using hi _ le_rfl
                                                                    -- 🎉 no goals
  have h2 : 0 ≤ abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_antisymm h1 h2
  have : (1 : β) = 0 := (abv_eq_zero abv).mp this
  absurd this one_ne_zero
#align cau_seq.one_not_equiv_zero CauSeq.one_not_equiv_zero

end IsDomain

section DivisionRing

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩
#align cau_seq.inv_aux CauSeq.inv_aux

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩
#align cau_seq.inv CauSeq.inv

@[simp, norm_cast]
theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = (f : ℕ → β)⁻¹ :=
  rfl
#align cau_seq.coe_inv CauSeq.coe_inv

@[simp, norm_cast]
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  rfl
#align cau_seq.inv_apply CauSeq.inv_apply

theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
                     -- 🎉 no goals
#align cau_seq.inv_mul_cancel CauSeq.inv_mul_cancel

theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
                     -- 🎉 no goals
#align cau_seq.mul_inv_cancel CauSeq.mul_inv_cancel

theorem const_inv {x : β} (hx : x ≠ 0) :
    const abv x⁻¹ = inv (const abv x) (by rwa [const_limZero]) :=
                                          -- 🎉 no goals
  rfl
#align cau_seq.const_inv CauSeq.const_inv

end DivisionRing

section Abs

/-- The constant Cauchy sequence -/
local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j
#align cau_seq.pos CauSeq.Pos

theorem not_limZero_of_pos {f : CauSeq α abs} : Pos f → ¬LimZero f
  | ⟨_, F0, hF⟩, H =>
    let ⟨_, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_le h₁ (abs_lt.1 h₂).2
#align cau_seq.not_lim_zero_of_pos CauSeq.not_limZero_of_pos

theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩
#align cau_seq.const_pos CauSeq.const_pos

theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f + g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩
#align cau_seq.add_pos CauSeq.add_pos

theorem pos_add_limZero {f g : CauSeq α abs} : Pos f → LimZero g → Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      cases' h j ij with h₁ h₂
      -- ⊢ F / 2 ≤ ↑(f + g) j
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      -- ⊢ F / 2 ≤ ↑(f + g) j
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩
      -- 🎉 no goals
#align cau_seq.pos_add_lim_zero CauSeq.pos_add_limZero

protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f * g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩
#align cau_seq.mul_pos CauSeq.mul_pos

theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  cases' Classical.em (LimZero f) with h h <;> simp [*]
  -- ⊢ Pos f ∨ LimZero f ∨ Pos (-f)
                                               -- 🎉 no goals
                                               -- ⊢ Pos f ∨ Pos (-f)
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  -- ⊢ Pos f ∨ Pos (-f)
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  -- ⊢ Pos f ∨ Pos (-f)
  refine' (le_total 0 (f i)).imp _ _ <;>
  -- ⊢ 0 ≤ ↑f i → Pos f
    refine' fun h => ⟨K, K0, i, fun j ij => _⟩ <;>
    -- ⊢ K ≤ ↑f j
    -- ⊢ K ≤ ↑(-f) j
    have := (hi _ ij).1 <;>
    -- ⊢ K ≤ ↑f j
    -- ⊢ K ≤ ↑(-f) j
    cases' hi _ le_rfl with h₁ h₂
    -- ⊢ K ≤ ↑f j
    -- ⊢ K ≤ ↑(-f) j
  · rwa [abs_of_nonneg] at this
    -- ⊢ 0 ≤ ↑f j
    rw [abs_of_nonneg h] at h₁
    -- ⊢ 0 ≤ ↑f j
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    -- ⊢ ↑f j ≤ 0
    rw [abs_of_nonpos h] at h₁
    -- ⊢ ↑f j ≤ 0
    rw [← sub_le_sub_iff_right, zero_sub]
    -- ⊢ ↑f j - ?inr.intro.intro.intro.refine'_2.intro ≤ -?inr.intro.intro.intro.refi …
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁
    -- 🎉 no goals
#align cau_seq.trichotomy CauSeq.trichotomy

instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f) by
    convert pos_add_limZero fg (neg_limZero gh) using 1
    -- ⊢ h - f = g - f + -(g - h)
    simp
    -- 🎉 no goals
#align cau_seq.lt_of_lt_of_eq CauSeq.lt_of_lt_of_eq

theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_limZero gh (neg_limZero fg)
  -- ⊢ f < h
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this
  -- 🎉 no goals
#align cau_seq.lt_of_eq_of_lt CauSeq.lt_of_eq_of_lt

theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f) by
    convert add_pos fg gh using 1
    -- ⊢ h - f = g - f + (h - g)
    simp
    -- 🎉 no goals
#align cau_seq.lt_trans CauSeq.lt_trans

theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => not_limZero_of_pos h (by simp [zero_limZero])
                                  -- 🎉 no goals
#align cau_seq.lt_irrefl CauSeq.lt_irrefl

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)
#align cau_seq.le_of_eq_of_le CauSeq.le_of_eq_of_le

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)
#align cau_seq.le_of_le_of_eq CauSeq.le_of_le_of_eq

instance : Preorder (CauSeq α abs) where
  lt := (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
    | Or.inl fg, Or.inl gh => Or.inl <| lt_trans fg gh
    | Or.inl fg, Or.inr gh => Or.inl <| lt_of_lt_of_eq fg gh
    | Or.inr fg, Or.inl gh => Or.inl <| lt_of_eq_of_lt fg gh
    | Or.inr fg, Or.inr gh => Or.inr <| Setoid.trans fg gh
  lt_iff_le_not_le _ _ :=
    ⟨fun h => ⟨Or.inl h, not_or_of_not (mt (lt_trans h) lt_irrefl) (not_limZero_of_pos h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoid.symm h)) h₂)⟩

theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_le gf)
#align cau_seq.le_antisymm CauSeq.le_antisymm

theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h
                                               -- 🎉 no goals
#align cau_seq.lt_total CauSeq.lt_total

theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  (or_assoc.2 (lt_total f g)).imp_right Or.inl
#align cau_seq.le_total CauSeq.le_total

theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  show Pos _ ↔ _ by rw [← const_sub, const_pos, sub_pos]
                    -- 🎉 no goals
#align cau_seq.const_lt CauSeq.const_lt

theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y := by
  rw [le_iff_lt_or_eq]; exact or_congr const_lt const_equiv
  -- ⊢ const x ≤ const y ↔ x < y ∨ x = y
                        -- 🎉 no goals
#align cau_seq.const_le CauSeq.const_le

theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g :=
  let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))
#align cau_seq.le_of_exists CauSeq.le_of_exists

theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < const a :=
  let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right]
    -- ⊢ ↑f i ≤ K
    exact le_of_lt (abs_lt.1 (H _)).2⟩
    -- 🎉 no goals
#align cau_seq.exists_gt CauSeq.exists_gt

theorem exists_lt (f : CauSeq α abs) : ∃ a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩
                     -- 🎉 no goals
#align cau_seq.exists_lt CauSeq.exists_lt

-- so named to match `rat_add_continuous_lemma`
theorem rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε := fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
#align rat_sup_continuous_lemma CauSeq.rat_sup_continuous_lemma

-- so named to match `rat_add_continuous_lemma`
theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
#align rat_inf_continuous_lemma CauSeq.rat_inf_continuous_lemma

instance : Sup (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

instance : Inf (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]
theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : ℕ → α) ⊔ g :=
  rfl
#align cau_seq.coe_sup CauSeq.coe_sup

@[simp, norm_cast]
theorem coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = (f : ℕ → α) ⊓ g :=
  rfl
#align cau_seq.coe_inf CauSeq.coe_inf

theorem sup_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊔ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun i H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      -- ⊢ |↑(f ⊔ g) j| < ε
      rw [abs_lt] at H₁ H₂ ⊢
      -- ⊢ -ε < ↑(f ⊔ g) j ∧ ↑(f ⊔ g) j < ε
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩
      -- 🎉 no goals
#align cau_seq.sup_lim_zero CauSeq.sup_limZero

theorem inf_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun i H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      -- ⊢ |↑(f ⊓ g) j| < ε
      rw [abs_lt] at H₁ H₂ ⊢
      -- ⊢ -ε < ↑(f ⊓ g) j ∧ ↑(f ⊓ g) j < ε
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩
      -- 🎉 no goals
#align cau_seq.inf_lim_zero CauSeq.inf_limZero

theorem sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := by
  intro ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊔ b₁ - a₂ ⊔ b₂) j| < ε
  obtain ⟨ai, hai⟩ := ha ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊔ b₁ - a₂ ⊔ b₂) j| < ε
  obtain ⟨bi, hbi⟩ := hb ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊔ b₁ - a₂ ⊔ b₂) j| < ε
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
#align cau_seq.sup_equiv_sup CauSeq.sup_equiv_sup

theorem inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ := by
  intro ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊓ b₁ - a₂ ⊓ b₂) j| < ε
  obtain ⟨ai, hai⟩ := ha ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊓ b₁ - a₂ ⊓ b₂) j| < ε
  obtain ⟨bi, hbi⟩ := hb ε ε0
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a₁ ⊓ b₁ - a₂ ⊓ b₂) j| < ε
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
#align cau_seq.inf_equiv_inf CauSeq.inf_equiv_inf

protected theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c := by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  -- ⊢ a ⊔ b < c
  refine' ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => _⟩
  -- ⊢ εa ⊓ εb ≤ ↑(c - a ⊔ b) i
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  -- ⊢ εa ⊓ εb ≤ ↑(c - a ⊔ b) i
  exact this.trans_eq (min_sub_sub_left _ _ _)
  -- 🎉 no goals
#align cau_seq.sup_lt CauSeq.sup_lt

protected theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c := by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  -- ⊢ a < b ⊓ c
  refine' ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => _⟩
  -- ⊢ εb ⊓ εc ≤ ↑(b ⊓ c - a) i
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  -- ⊢ εb ⊓ εc ≤ ↑(b ⊓ c - a) i
  exact this.trans_eq (min_sub_sub_right _ _ _)
  -- 🎉 no goals
#align cau_seq.lt_inf CauSeq.lt_inf

@[simp]
protected theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a :=
  Subtype.ext sup_idem
#align cau_seq.sup_idem CauSeq.sup_idem

@[simp]
protected theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a :=
  Subtype.ext inf_idem
#align cau_seq.inf_idem CauSeq.inf_idem

protected theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a :=
  Subtype.ext sup_comm
#align cau_seq.sup_comm CauSeq.sup_comm

protected theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a :=
  Subtype.ext inf_comm
#align cau_seq.inf_comm CauSeq.inf_comm

protected theorem sup_eq_right {a b : CauSeq α abs} (h : a ≤ b) : a ⊔ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  -- ⊢ a ⊔ b ≈ b
  · intro _ _
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a ⊔ b - b) j| < ε✝
    refine' ⟨i, fun j hj => _⟩
    -- ⊢ |↑(a ⊔ b - b) j| < ε✝
    dsimp
    -- ⊢ |↑a j ⊔ ↑b j - ↑b j| < ε✝
    erw [← max_sub_sub_right]
    -- ⊢ |max (↑a j - ↑b j) (↑b j - ↑b j)| < ε✝
    rwa [sub_self, max_eq_right, abs_zero]
    -- ⊢ ↑a j - ↑b j ≤ 0
    rw [sub_nonpos, ← sub_nonneg]
    -- ⊢ 0 ≤ ↑b j - ↑a j
    exact ε0.le.trans (h _ hj)
    -- 🎉 no goals
  · refine' Setoid.trans (sup_equiv_sup h (Setoid.refl _)) _
    -- ⊢ b ⊔ b ≈ b
    rw [CauSeq.sup_idem]
    -- 🎉 no goals
#align cau_seq.sup_eq_right CauSeq.sup_eq_right

protected theorem inf_eq_right {a b : CauSeq α abs} (h : b ≤ a) : a ⊓ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  -- ⊢ a ⊓ b ≈ b
  · intro _ _
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → |↑(a ⊓ b - b) j| < ε✝
    refine' ⟨i, fun j hj => _⟩
    -- ⊢ |↑(a ⊓ b - b) j| < ε✝
    dsimp
    -- ⊢ |↑a j ⊓ ↑b j - ↑b j| < ε✝
    erw [← min_sub_sub_right]
    -- ⊢ |min (↑a j - ↑b j) (↑b j - ↑b j)| < ε✝
    rwa [sub_self, min_eq_right, abs_zero]
    -- ⊢ 0 ≤ ↑a j - ↑b j
    exact ε0.le.trans (h _ hj)
    -- 🎉 no goals
  · refine' Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) _
    -- ⊢ b ⊓ b ≈ b
    rw [CauSeq.inf_idem]
    -- 🎉 no goals
#align cau_seq.inf_eq_right CauSeq.inf_eq_right

protected theorem sup_eq_left {a b : CauSeq α abs} (h : b ≤ a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h
  -- 🎉 no goals
#align cau_seq.sup_eq_left CauSeq.sup_eq_left

protected theorem inf_eq_left {a b : CauSeq α abs} (h : a ≤ b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h
  -- 🎉 no goals
#align cau_seq.inf_eq_left CauSeq.inf_eq_left

protected theorem le_sup_left {a b : CauSeq α abs} : a ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_left⟩
#align cau_seq.le_sup_left CauSeq.le_sup_left

protected theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b ≤ a :=
  le_of_exists ⟨0, fun _ _ => inf_le_left⟩
#align cau_seq.inf_le_left CauSeq.inf_le_left

protected theorem le_sup_right {a b : CauSeq α abs} : b ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_right⟩
#align cau_seq.le_sup_right CauSeq.le_sup_right

protected theorem inf_le_right {a b : CauSeq α abs} : a ⊓ b ≤ b :=
  le_of_exists ⟨0, fun _ _ => inf_le_right⟩
#align cau_seq.inf_le_right CauSeq.inf_le_right

protected theorem sup_le {a b c : CauSeq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c := by
  cases' ha with ha ha
  -- ⊢ a ⊔ b ≤ c
  · cases' hb with hb hb
    -- ⊢ a ⊔ b ≤ c
    · exact Or.inl (CauSeq.sup_lt ha hb)
      -- 🎉 no goals
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      -- ⊢ a ⊔ b ≤ c
      refine' le_of_le_of_eq (Or.inr _) hb
      -- ⊢ a ⊔ b ≈ b
      exact CauSeq.sup_eq_right ha
      -- 🎉 no goals
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    -- ⊢ a ⊔ b ≤ c
    refine' le_of_le_of_eq (Or.inr _) ha
    -- ⊢ a ⊔ b ≈ a
    exact CauSeq.sup_eq_left hb
    -- 🎉 no goals
#align cau_seq.sup_le CauSeq.sup_le

protected theorem le_inf {a b c : CauSeq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c := by
  cases' hb with hb hb
  -- ⊢ a ≤ b ⊓ c
  · cases' hc with hc hc
    -- ⊢ a ≤ b ⊓ c
    · exact Or.inl (CauSeq.lt_inf hb hc)
      -- 🎉 no goals
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      -- ⊢ a ≤ b ⊓ c
      refine' le_of_eq_of_le hc (Or.inr _)
      -- ⊢ c ≈ b ⊓ c
      exact Setoid.symm (CauSeq.inf_eq_right hb)
      -- 🎉 no goals
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    -- ⊢ a ≤ b ⊓ c
    refine' le_of_eq_of_le hb (Or.inr _)
    -- ⊢ b ≈ b ⊓ c
    exact Setoid.symm (CauSeq.inf_eq_left hc)
    -- 🎉 no goals
#align cau_seq.le_inf CauSeq.le_inf

/-! Note that `DistribLattice (CauSeq α abs)` is not true because there is no `PartialOrder`. -/


protected theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  Subtype.ext <| funext fun _ => max_min_distrib_left
#align cau_seq.sup_inf_distrib_left CauSeq.sup_inf_distrib_left

protected theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
  Subtype.ext <| funext fun _ => max_min_distrib_right
#align cau_seq.sup_inf_distrib_right CauSeq.sup_inf_distrib_right

end Abs

end CauSeq
