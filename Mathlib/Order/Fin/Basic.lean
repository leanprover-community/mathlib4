/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Hom.Basic

/-!
# `Fin n` forms a bounded linear order

This file contains the linear ordered instance on `Fin n`.

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `Fin.orderIsoSubtype` : coercion to `{i // i < n}` as an `OrderIso`;
* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.valOrderEmb` : coercion to natural numbers as an `OrderEmbedding`;
* `Fin.succOrderEmb` : `Fin.succ` as an `OrderEmbedding`;
* `Fin.castLEOrderEmb h` : `Fin.castLE` as an `OrderEmbedding`, embed `Fin n` into `Fin m` when
  `h : n ≤ m`;
* `Fin.castOrderIso` : `Fin.cast` as an `OrderIso`, order isomorphism between `Fin n` and `Fin m`
  provided that `n = m`, see also `Equiv.finCongr`;
* `Fin.castAddOrderEmb m` : `Fin.castAdd` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccOrderEmb` : `Fin.castSucc` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatOrderEmb m i` : `Fin.addNat` as an `OrderEmbedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddOrderEmb n i` : `Fin.natAdd` as an `OrderEmbedding`, adds `n` on `i` on the left;
* `Fin.revOrderIso`: `Fin.rev` as an `OrderIso`, the antitone involution given by `i ↦ n-(i+1)`
-/

assert_not_exists Monoid

open Function Nat Set

namespace Fin
variable {m n : ℕ}

/-! ### Instances -/

instance : Max (Fin n) where max x y := ⟨max x y, max_rec' (· < n) x.2 y.2⟩
instance : Min (Fin n) where min x y := ⟨min x y, min_rec' (· < n) x.2 y.2⟩

@[simp, norm_cast]
theorem coe_max (a b : Fin n) : ↑(max a b) = (max a b : ℕ) := rfl

@[simp, norm_cast]
theorem coe_min (a b : Fin n) : ↑(min a b) = (min a b : ℕ) := rfl

theorem compare_eq_compare_val (a b : Fin n) : compare a b = compare a.val b.val := rfl

@[deprecated (since := "2025-03-01")] alias coe_sup := coe_max
@[deprecated (since := "2025-03-01")] alias coe_inf := coe_min

instance instLinearOrder : LinearOrder (Fin n) :=
  Fin.val_injective.linearOrder _
    Fin.le_iff_val_le_val Fin.lt_def coe_min coe_max compare_eq_compare_val

instance instBoundedOrder [NeZero n] : BoundedOrder (Fin n) where
  top := rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le

instance instBiheytingAlgebra [NeZero n] : BiheytingAlgebra (Fin n) :=
  LinearOrder.toBiheytingAlgebra (Fin n)


/- There is a slight asymmetry here, in the sense that `0` is of type `Fin n` when we have
`[NeZero n]` whereas `last n` is of type `Fin (n + 1)`. To address this properly would
require a change to std4, defining `NeZero n` and thus re-defining `last n`
(and possibly make its argument implicit) as `rev 0`, of type `Fin n`. As we can see from these
lemmas, this would be equivalent to the existing definition. -/

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instPartialOrder : PartialOrder (Fin n) := inferInstance
instance instLattice : Lattice (Fin n) := inferInstance
instance instHeytingAlgebra [NeZero n] : HeytingAlgebra (Fin n) := inferInstance
instance instCoheytingAlgebra [NeZero n] : CoheytingAlgebra (Fin n) := inferInstance

/-! ### Miscellaneous lemmas -/

lemma top_eq_last (n : ℕ) : ⊤ = Fin.last n := rfl

lemma bot_eq_zero (n : ℕ) [NeZero n] : ⊥ = (0 : Fin n) := rfl

@[simp] theorem rev_bot [NeZero n] : rev (⊥ : Fin n) = ⊤ := rfl
@[simp] theorem rev_top [NeZero n] : rev (⊤ : Fin n) = ⊥ := rev_rev _

theorem rev_zero_eq_top (n : ℕ) [NeZero n] : rev (0 : Fin n) = ⊤ := rfl
theorem rev_last_eq_bot (n : ℕ) : rev (last n) = ⊥ := by rw [rev_last, bot_eq_zero]

@[simp]
theorem succ_top (n : ℕ) [NeZero n] : (⊤ : Fin n).succ = ⊤ := by
  rw [← rev_zero_eq_top, ← rev_zero_eq_top, ← rev_castSucc, castSucc_zero']

@[simp]
theorem val_top (n : ℕ) [NeZero n] : ((⊤ : Fin n) : ℕ) = n - 1 := rfl

@[simp]
theorem zero_eq_top {n : ℕ} [NeZero n] : (0 : Fin n) = ⊤ ↔ n = 1 := by
  rw [← bot_eq_zero, subsingleton_iff_bot_eq_top, subsingleton_iff_le_one,
    le_one_iff_eq_zero_or_eq_one, or_iff_right (NeZero.ne n)]

@[simp]
theorem top_eq_zero {n : ℕ} [NeZero n] : (⊤ : Fin n) = 0 ↔ n = 1 :=
  eq_comm.trans zero_eq_top

@[simp]
theorem cast_top {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) : (⊤ : Fin m).cast h = ⊤ := by
  simp [← val_inj, h]

section ToFin
variable {α : Type*} [Preorder α] {f : α → Fin (n + 1)}

lemma strictMono_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : StrictMono f) :
    StrictMono (fun a => pred (f a) (hf a)) := fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)

lemma monotone_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : Monotone f) :
    Monotone (fun a => pred (f a) (hf a)) := fun _ _ h => pred_le_pred_iff.2 (hf₂ h)

lemma strictMono_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : StrictMono f) :
    StrictMono (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)

lemma monotone_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : Monotone f) :
    Monotone (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

end ToFin

section FromFin
variable {α : Type*} [Preorder α] {f : Fin (n + 1) → α}

/-- A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
lemma strictMono_iff_lt_succ : StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)

/-- A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
lemma monotone_iff_le_succ : Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)

/-- A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
lemma strictAnti_iff_succ_lt : StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)

/-- A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
lemma antitone_iff_succ_le : Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)

lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
    Function.Injective f ↔ ∀ (i : Fin n), f i.castSucc ≠ f i.succ := by
  constructor
  · intro hf i hi
    have := hf hi
    simp [Fin.ext_iff] at this
  · intro hf
    refine (strictMono_iff_lt_succ (f := f).2 fun i ↦ ?_).injective
    exact lt_of_le_of_ne (f.monotone (Fin.castSucc_le_succ i)) (hf i)

end FromFin

/-! #### Monotonicity -/

lemma val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ ↦ id
lemma cast_strictMono {k l : ℕ} (h : k = l) : StrictMono (Fin.cast h) := fun {_ _} h ↦ h

lemma strictMono_succ : StrictMono (succ : Fin n → Fin (n + 1)) := fun _ _ ↦ succ_lt_succ
lemma strictMono_castLE (h : n ≤ m) : StrictMono (castLE h : Fin n → Fin m) := fun _ _ ↦ id
lemma strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) := strictMono_castLE _
lemma strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) := strictMono_castAdd _
lemma strictMono_natAdd (n) : StrictMono (natAdd n : Fin m → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_left (show i.val < j.val from h) _
lemma strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_right (show i.val < j.val from h) _

lemma strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun _ => castSucc_lt_succ.le

variable {p : Fin (n + 1)} {i j : Fin n}

@[simp]
lemma succAbove_inj : succAbove p i = succAbove p j ↔ i = j :=
  (strictMono_succAbove p).injective.eq_iff

@[simp]
lemma succAbove_le_succAbove_iff : succAbove p i ≤ succAbove p j ↔ i ≤ j :=
  (strictMono_succAbove p).le_iff_le

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.succAbove_le_succAbove⟩ := succAbove_le_succAbove_iff

@[simp]
lemma succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j :=
  (strictMono_succAbove p).lt_iff_lt

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.succAbove_lt_succAbove⟩ := succAbove_lt_succAbove_iff

@[simp]
theorem natAdd_inj (m) {i j : Fin n} : natAdd m i = natAdd m j ↔ i = j :=
  (strictMono_natAdd _).injective.eq_iff

theorem natAdd_injective (m n : ℕ) :
    Function.Injective (Fin.natAdd n : Fin m → _) :=
  (strictMono_natAdd _).injective

@[simp]
theorem natAdd_le_natAdd_iff (m) {i j : Fin n} : natAdd m i ≤ natAdd m j ↔ i ≤ j :=
  (strictMono_natAdd _).le_iff_le

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.natAdd_le_natAdd⟩ := natAdd_le_natAdd_iff

@[simp]
theorem natAdd_lt_natAdd_iff (m) {i j : Fin n} : natAdd m i < natAdd m j ↔ i < j :=
  (strictMono_natAdd _).lt_iff_lt

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.natAdd_lt_natAdd⟩ := natAdd_lt_natAdd_iff

@[simp]
theorem addNat_inj (m) {i j : Fin n} : i.addNat m = j.addNat m ↔ i = j :=
  (strictMono_addNat _).injective.eq_iff

@[simp]
theorem addNat_le_addNat_iff (m) {i j : Fin n} : i.addNat m ≤ j.addNat m ↔ i ≤ j :=
  (strictMono_addNat _).le_iff_le

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.addNat_le_addNat⟩ := addNat_le_addNat_iff

@[simp]
theorem addNat_lt_addNat_iff (m) {i j : Fin n} : i.addNat m < j.addNat m ↔ i < j :=
  (strictMono_addNat _).lt_iff_lt

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.addNat_lt_addNat⟩ := addNat_lt_addNat_iff

@[simp]
theorem castLE_le_castLE_iff {i j : Fin n} (h : n ≤ m) : i.castLE h ≤ j.castLE h ↔ i ≤ j := .rfl

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.castLE_le_castLE⟩ := castLE_le_castLE_iff

@[simp]
theorem castLE_lt_castLE_iff {i j : Fin n} (h : n ≤ m) : i.castLE h < j.castLE h ↔ i < j := .rfl

@[gcongr]
alias ⟨_, _root_.GCongr.Fin.castLE_lt_castLE⟩ := castLE_lt_castLE_iff

lemma predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H

lemma predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p ↦ predAbove p i := fun a b H ↦ by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_ge
  · rfl

@[gcongr]
lemma predAbove_le_predAbove {p q : Fin n} (hpq : p ≤ q) {i j : Fin (n + 1)} (hij : i ≤ j) :
    p.predAbove i ≤ q.predAbove j :=
  (predAbove_right_monotone p hij).trans (predAbove_left_monotone j hpq)

/-- `Fin.predAbove p` as an `OrderHom`. -/
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩

/-- `predAbove` is injective at the pivot -/
lemma predAbove_left_injective : Injective (@predAbove n) := by
  intro i j hij
  obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.2 i.size_positive
  wlog h : i < j generalizing i j
  · simp only [not_lt] at h
    obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  replace hij := congr_fun hij i.succ
  rw [predAbove_succ_self, Fin.predAbove_of_le_castSucc _ _ (by simpa),
    ← Fin.castSucc_inj, castSucc_castPred] at hij
  exact (i.castSucc_lt_succ.ne hij).elim

/-- `predAbove` is injective at the pivot -/
@[simp] lemma predAbove_left_inj {x y : Fin n} : x.predAbove = y.predAbove ↔ x = y :=
  predAbove_left_injective.eq_iff

/-! #### Order isomorphisms -/

/-- The equivalence `Fin n ≃ {i // i < n}` is an order isomorphism. -/
@[simps! apply symm_apply]
def orderIsoSubtype : Fin n ≃o {i // i < n} :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

/-- `Fin.cast` as an `OrderIso`.

`castOrderIso eq i` embeds `i` into an equal `Fin` type. -/
@[simps]
def castOrderIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨Fin.cast eq, Fin.cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq

@[simp]
lemma symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm := by subst h; rfl

@[simp]
lemma castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; simp

/-- While in many cases `Fin.castOrderIso` is better than `Equiv.cast`/`cast`, sometimes we want to
apply a generic lemma about `cast`. -/
lemma castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; rfl

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
def revOrderIso : (Fin n)ᵒᵈ ≃o Fin n := ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩

@[simp]
lemma revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) := rfl

lemma rev_strictAnti : StrictAnti (@rev n) := fun _ _ ↦ rev_lt_rev.mpr

lemma rev_anti : Antitone (@rev n) := rev_strictAnti.antitone

/-! #### Order embeddings -/

/-- The inclusion map `Fin n → ℕ` is an order embedding. -/
@[simps! apply]
def valOrderEmb (n) : Fin n ↪o ℕ := ⟨valEmbedding, Iff.rfl⟩

namespace OrderEmbedding

@[simps]
instance : Inhabited (Fin n ↪o ℕ) where
  default := Fin.valOrderEmb n

end OrderEmbedding

/-- The ordering on `Fin n` is a well order. -/
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) := (valOrderEmb n).isWellOrder

/-- `Fin.succ` as an `OrderEmbedding` -/
def succOrderEmb (n : ℕ) : Fin n ↪o Fin (n + 1) := .ofStrictMono succ strictMono_succ

@[simp, norm_cast] lemma coe_succOrderEmb : ⇑(succOrderEmb n) = Fin.succ := rfl

@[simp] lemma succOrderEmb_toEmbedding : (succOrderEmb n).toEmbedding = succEmb n := rfl

/-- `Fin.castLE` as an `OrderEmbedding`.

`castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps! apply toEmbedding]
def castLEOrderEmb (h : n ≤ m) : Fin n ↪o Fin m := .ofStrictMono (castLE h) (strictMono_castLE h)

/-- `Fin.castAdd` as an `OrderEmbedding`.

`castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (castAdd m) (strictMono_castAdd m)

/-- `Fin.castSucc` as an `OrderEmbedding`.

`castSuccOrderEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
def castSuccOrderEmb : Fin n ↪o Fin (n + 1) := .ofStrictMono castSucc strictMono_castSucc

/-- `Fin.addNat` as an `OrderEmbedding`.

`addNatOrderEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply toEmbedding]
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (addNat · m) (strictMono_addNat m)

/-- `Fin.natAdd` as an `OrderEmbedding`.

`natAddOrderEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply toEmbedding]
def natAddOrderEmb (n) : Fin m ↪o Fin (n + m) := .ofStrictMono (natAdd n) (strictMono_natAdd n)

/-- `Fin.succAbove p` as an `OrderEmbedding`. -/
@[simps! apply toEmbedding]
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)

/-! ### Uniqueness of order isomorphisms -/

variable {α : Type*} [Preorder α]

/-- If `e` is an `orderIso` between `Fin n` and `Fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : Fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp] lemma coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction i using Nat.strong_induction_on with | _ i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_symm_apply.1 (mk_lt_of_lt_val hj)
    specialize h _ this (e.symm _).is_lt
    simp only [Fin.eta, OrderIso.apply_symm_apply] at h
    rwa [h]
  · rwa [← h j hj (hj.trans hi), ← lt_def, e.lt_iff_lt]

end Fin
