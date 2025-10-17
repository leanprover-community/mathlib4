/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Fintype.Option
import Mathlib.Order.InitialSeg
import Mathlib.Order.Nat
import Mathlib.Order.SuccPred.CompleteLinearOrder
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Order on cardinal numbers

We define the order on cardinal numbers and show its basic properties, including the ordered
semiring structure.

## Main definitions

* The order `c₁ ≤ c₂` is defined by `Cardinal.le_def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.
* `Order.IsSuccLimit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `Cardinal.IsStrongLimit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.

## Main instances

* Cardinals form a `CanonicallyOrderedAdd` `OrderedCommSemiring` with the aforementioned sum and
  product.
* Cardinals form a `SuccOrder`. Use `Order.succ c` for the smallest cardinal greater than `c`.
* The less-than relation on cardinals forms a well-order.
* Cardinals form a `ConditionallyCompleteLinearOrderBot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `Cardinal.bddAbove_iff_small`. One can use `sSup` for the cardinal supremum,
  and `sInf` for the minimum of a set of cardinals.

## Main statements

* Cantor's theorem: `Cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `Cardinal.sum_lt_prod`

## Implementation notes

The current setup interweaves the order structure and the algebraic structure on `Cardinal` tightly.
For example, we need to know what a ring is in order to show that `0` is the smallest cardinality.
That is reflected in this file containing both the order and algebra structure.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Field

open List Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Order on cardinals -/

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : LE Cardinal.{u} :=
  ⟨fun q₁ q₂ =>
    Quotient.liftOn₂ q₁ q₂ (fun α β => Nonempty <| α ↪ β) fun _ _ _ _ ⟨e₁⟩ ⟨e₂⟩ =>
      propext ⟨fun ⟨e⟩ => ⟨e.congr e₁ e₂⟩, fun ⟨e⟩ => ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance partialOrder : PartialOrder Cardinal.{u} where
  le := (· ≤ ·)
  le_refl := by
    rintro ⟨α⟩
    exact ⟨Embedding.refl _⟩
  le_trans := by
    rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
  le_antisymm := by
    rintro ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩
    exact Quotient.sound (e₁.antisymm e₂)

instance linearOrder : LinearOrder Cardinal.{u} :=
  { Cardinal.partialOrder with
    le_total := by
      rintro ⟨α⟩ ⟨β⟩
      apply Embedding.total
    toDecidableLE := Classical.decRel _ }

theorem le_def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β) :=
  Iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=
  ⟨⟨f, hf⟩⟩

theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β :=
  ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : #β ≤ #α :=
  ⟨Embedding.ofSurjective f hf⟩

theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ #α ↔ ∃ p : Set α, #p = c :=
  ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(Subtype p) ≤ #α :=
  ⟨Embedding.subtype p⟩

theorem mk_set_le (s : Set α) : #s ≤ #α :=
  mk_subtype_le s

theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]

theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α ≤ lift.{max u v} #β ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

/-- A variant of `Cardinal.lift_mk_le` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{0}

/-! ### `lift` sends `Cardinal.{u}` to an initial segment of `Cardinal.{max u v}`. -/

/-- `Cardinal.lift` as an `InitialSeg`. -/
@[simps!]
def liftInitialSeg : Cardinal.{u} ≤i Cardinal.{max u v} := by
  refine ⟨(OrderEmbedding.ofMapLEIff lift ?_).ltEmbedding, ?_⟩ <;> intro a b
  · refine inductionOn₂ a b fun _ _ ↦ ?_
    rw [← lift_umax, lift_mk_le.{v, u, u}, le_def]
  · refine inductionOn₂ a b fun α β h ↦ ?_
    obtain ⟨e⟩ := h.le
    replace e := e.congr (Equiv.refl β) Equiv.ulift
    refine ⟨#(range e), mk_congr (Equiv.ulift.trans <| Equiv.symm ?_)⟩
    apply (e.codRestrict _ mem_range_self).equivOfSurjective
    rintro ⟨a, ⟨b, rfl⟩⟩
    exact ⟨b, rfl⟩

theorem mem_range_lift_of_le {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a → b ∈ Set.range lift.{v, u} :=
  liftInitialSeg.mem_range_of_le

theorem lift_injective : Injective lift.{u, v} :=
  liftInitialSeg.injective

@[simp]
theorem lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.{v, u} b ↔ a = b :=
  lift_injective.eq_iff

@[simp]
theorem lift_le {a b : Cardinal.{v}} : lift.{u} a ≤ lift.{u} b ↔ a ≤ b :=
  liftInitialSeg.le_iff_le

@[simp]
theorem lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v, u} b ↔ a < b :=
  liftInitialSeg.lt_iff_lt

theorem lift_strictMono : StrictMono lift := fun _ _ => lift_lt.2

theorem lift_monotone : Monotone lift :=
  lift_strictMono.monotone

@[simp]
theorem lift_min {a b : Cardinal} : lift.{u, v} (min a b) = min (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_min

@[simp]
theorem lift_max {a b : Cardinal} : lift.{u, v} (max a b) = max (lift.{u, v} a) (lift.{u, v} b) :=
  lift_monotone.map_max

-- This cannot be a `@[simp]` lemma because `simp` can't figure out the universes.
theorem lift_umax_eq {a : Cardinal.{u}} {b : Cardinal.{v}} :
    lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b := by
  rw [← lift_lift.{v, w, u}, ← lift_lift.{u, w, v}, lift_inj]

theorem le_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b ≤ lift.{v, u} a ↔ ∃ a' ≤ a, lift.{v, u} a' = b :=
  liftInitialSeg.le_apply_iff

theorem lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max u v}} :
    b < lift.{v, u} a ↔ ∃ a' < a, lift.{v, u} a' = b :=
  liftInitialSeg.lt_apply_iff

/-! ### Basic cardinals -/

@[simp]
theorem lift_eq_zero {a : Cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
  lift_injective.eq_iff' lift_zero

@[simp]
theorem mk_fintype (α : Type u) [h : Fintype α] : #α = Fintype.card α :=
  mk_congr (Fintype.equivOfCardEq (by simp))

private theorem cast_succ (n : ℕ) : ((n + 1 : ℕ) : Cardinal.{u}) = n + 1 := by
  change #(ULift.{u} _) = #(ULift.{u} _) + 1
  rw [← mk_option]
  simp

instance commSemiring : CommSemiring Cardinal.{u} where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  zero_add a := inductionOn a fun α => mk_congr <| Equiv.emptySum _ α
  add_zero a := inductionOn a fun α => mk_congr <| Equiv.sumEmpty α _
  add_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumAssoc α β γ
  add_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.sumComm α β
  zero_mul a := inductionOn a fun _ => mk_eq_zero _
  mul_zero a := inductionOn a fun _ => mk_eq_zero _
  one_mul a := inductionOn a fun α => mk_congr <| Equiv.uniqueProd α _
  mul_one a := inductionOn a fun α => mk_congr <| Equiv.prodUnique α _
  mul_assoc a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodAssoc α β γ
  mul_comm a b := inductionOn₂ a b fun α β => mk_congr <| Equiv.prodComm α β
  left_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.prodSumDistrib α β γ
  right_distrib a b c := inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumProdDistrib α β γ
  nsmul := nsmulRec
  npow n c := c ^ (n : Cardinal)
  npow_zero := power_zero
  npow_succ n c := by rw [cast_succ, power_add, power_one]
  natCast n := lift #(Fin n)
  natCast_zero := rfl
  natCast_succ n := cast_succ n

theorem mk_bool : #Bool = 2 := by simp

theorem mk_Prop : #Prop = 2 := by simp

theorem power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b) ^ c := by
  rw [mul_comm b c]
  exact inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.curry γ β α

@[simp, norm_cast]
theorem power_natCast (a : Cardinal.{u}) (n : ℕ) : a ^ (↑n : Cardinal.{u}) = a ^ n :=
  rfl

@[simp]
theorem lift_eq_one {a : Cardinal.{v}} : lift.{u} a = 1 ↔ a = 1 :=
  lift_injective.eq_iff' lift_one

@[simp]
theorem lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = lift.{v} a * lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.prodCongr Equiv.ulift Equiv.ulift).symm

theorem lift_two : lift.{u, v} 2 = 2 := by simp [← one_add_one_eq_two]

@[simp]
theorem mk_set {α : Type u} : #(Set α) = 2 ^ #α := by simp [← one_add_one_eq_two, Set]

/-- A variant of `Cardinal.mk_set` expressed in terms of a `Set` instead of a `Type`. -/
@[simp]
theorem mk_powerset {α : Type u} (s : Set α) : #(↥(𝒫 s)) = 2 ^ #(↥s) :=
  (mk_congr (Equiv.Set.powerset s)).trans mk_set

theorem lift_two_power (a : Cardinal) : lift.{v} (2 ^ a) = 2 ^ lift.{v} a := by
  simp [← one_add_one_eq_two]

/-! ### Order properties -/

protected theorem zero_le : ∀ a : Cardinal, 0 ≤ a := by
  rintro ⟨α⟩
  exact ⟨Embedding.ofIsEmpty⟩

private theorem add_le_add' : ∀ {a b c d : Cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sumMap e₂⟩

instance addLeftMono : AddLeftMono Cardinal :=
  ⟨fun _ _ _ => add_le_add' le_rfl⟩

instance addRightMono : AddRightMono Cardinal :=
  ⟨fun _ _ _ h => add_le_add' h le_rfl⟩

instance canonicallyOrderedAdd : CanonicallyOrderedAdd Cardinal.{u} where
  exists_add_of_le {a b} :=
    inductionOn₂ a b fun α β ⟨⟨f, hf⟩⟩ =>
      have : α ⊕ ((range f)ᶜ : Set β) ≃ β := by
        classical
        exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans <|
          Equiv.Set.sumCompl (range f)
      ⟨#(↥(range f)ᶜ), mk_congr this.symm⟩
  le_self_add a b := (add_zero a).ge.trans <| by grw [Cardinal.zero_le b]
  le_add_self a _ := (zero_add a).ge.trans <| by grw [Cardinal.zero_le]

instance isOrderedRing : IsOrderedRing Cardinal.{u} :=
  CanonicallyOrderedAdd.toIsOrderedRing

instance orderBot : OrderBot Cardinal.{u} where
  bot := 0
  bot_le := zero_le

instance noZeroDivisors : NoZeroDivisors Cardinal.{u} where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} =>
    inductionOn₂ a b fun α β => by
      simpa only [mul_def, mk_eq_zero_iff, isEmpty_prod] using id

instance : LinearOrderedCommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring,
    Cardinal.linearOrder with
    bot_le _ := bot_le
    mul_le_mul_left := @mul_le_mul_left' _ _ _ _
    zero_le_one := zero_le _ }

-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoidWithZero Cardinal.{u} :=
  { Cardinal.commSemiring with }

-- Computable instance to prevent a non-computable one being found via the one above
instance : CommMonoid Cardinal.{u} :=
  { Cardinal.commSemiring with }

theorem zero_power_le (c : Cardinal.{u}) : (0 : Cardinal.{u}) ^ c ≤ 1 := by
  by_cases h : c = 0
  · rw [h, power_zero]
  · rw [zero_power h]
    apply zero_le

theorem power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c := by
  rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩
  let ⟨a⟩ := mk_ne_zero_iff.1 hα
  exact ⟨@Function.Embedding.arrowCongrLeft _ _ _ ⟨a⟩ e⟩

theorem self_le_power (a : Cardinal) {b : Cardinal} (hb : 1 ≤ b) : a ≤ a ^ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact zero_le _
  · convert power_le_power_left ha hb
    exact (power_one a).symm

/-- **Cantor's theorem** -/
theorem cantor (a : Cardinal.{u}) : a < 2 ^ a := by
  induction a using Cardinal.inductionOn with | _ α
  rw [← mk_set]
  refine ⟨⟨⟨singleton, fun a b => singleton_eq_singleton_iff.1⟩⟩, ?_⟩
  rintro ⟨⟨f, hf⟩⟩
  exact cantor_injective f hf

instance : NoMaxOrder Cardinal.{u} where exists_gt a := ⟨_, cantor a⟩

-- short-circuit type class inference
instance : DistribLattice Cardinal.{u} := inferInstance

theorem power_le_max_power_one {a b c : Cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 := by
  by_cases ha : a = 0
  · simp [ha, zero_power_le]
  · exact (power_le_power_left ha h).trans (le_max_left _ _)

theorem power_le_power_right {a b c : Cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
  inductionOn₃ a b c fun _ _ _ ⟨e⟩ => ⟨Embedding.arrowCongrRight e⟩

theorem power_pos {a : Cardinal} (b : Cardinal) (ha : 0 < a) : 0 < a ^ b :=
  (power_ne_zero _ ha.ne').bot_lt

protected theorem lt_wf : @WellFounded Cardinal.{u} (· < ·) :=
  ⟨fun a =>
    by_contradiction fun h => by
      let ι := { c : Cardinal // ¬Acc (· < ·) c }
      let f : ι → Cardinal := Subtype.val
      haveI hι : Nonempty ι := ⟨⟨_, h⟩⟩
      obtain ⟨⟨c : Cardinal, hc : ¬Acc (· < ·) c⟩, ⟨h_1 : ∀ j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
        Embedding.min_injective fun i => (f i).out
      refine hc (Acc.intro _ fun j h' => by_contradiction fun hj => h'.2 ?_)
      have : #_ ≤ #_ := ⟨h_1 ⟨j, hj⟩⟩
      simpa only [mk_out] using this⟩

instance : WellFoundedRelation Cardinal.{u} :=
  ⟨(· < ·), Cardinal.lt_wf⟩

instance : WellFoundedLT Cardinal.{u} :=
  ⟨Cardinal.lt_wf⟩

instance : ConditionallyCompleteLinearOrderBot Cardinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
theorem sInf_empty : sInf (∅ : Set Cardinal.{u}) = 0 :=
  dif_neg Set.not_nonempty_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : SuccOrder Cardinal := ConditionallyCompleteLinearOrder.toSuccOrder

theorem succ_def (c : Cardinal) : succ c = sInf { c' | c < c' } :=
  dif_neg <| not_isMax c

theorem succ_pos : ∀ c : Cardinal, 0 < succ c :=
  bot_lt_succ

theorem succ_ne_zero (c : Cardinal) : succ c ≠ 0 :=
  (succ_pos _).ne'

theorem add_one_le_succ (c : Cardinal.{u}) : c + 1 ≤ succ c := by
  have : Set.Nonempty { c' | c < c' } := exists_gt c
  simp_rw [succ_def, le_csInf_iff'' this, mem_setOf]
  intro b hlt
  rcases b, c with ⟨⟨β⟩, ⟨γ⟩⟩
  obtain ⟨f⟩ := le_of_lt hlt
  have : ¬Surjective f := fun hn => (not_le_of_gt hlt) (mk_le_of_surjective hn)
  simp only [Surjective, not_forall] at this
  rcases this with ⟨b, hb⟩
  calc
    #γ + 1 = #(Option γ) := mk_option.symm
    _ ≤ #β := (f.optionElim b hb).cardinal_le

@[simp]
theorem lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v, u} a) :=
  le_antisymm
    (le_of_not_gt fun h => by
      rcases lt_lift_iff.1 h with ⟨b, h, e⟩
      rw [lt_succ_iff, ← lift_le, e] at h
      exact h.not_gt (lt_succ _))
    (succ_le_of_lt <| lift_lt.2 <| lt_succ a)

/-! ### Limit cardinals -/

theorem ne_zero_of_isSuccLimit {c} (h : IsSuccLimit c) : c ≠ 0 :=
  h.ne_bot

theorem isSuccPrelimit_zero : IsSuccPrelimit (0 : Cardinal) :=
  isSuccPrelimit_bot

protected theorem isSuccLimit_iff {c : Cardinal} : IsSuccLimit c ↔ c ≠ 0 ∧ IsSuccPrelimit c :=
  isSuccLimit_iff

@[simp]
protected theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Cardinal) :=
  not_isSuccLimit_bot

/-- A cardinal is a strong limit if it is not zero and it is closed under powersets.
Note that `ℵ₀` is a strong limit by this definition. -/
structure IsStrongLimit (c : Cardinal) : Prop where
  ne_zero : c ≠ 0
  two_power_lt ⦃x⦄ : x < c → 2 ^ x < c

protected theorem IsStrongLimit.isSuccLimit {c} (H : IsStrongLimit c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨H.ne_zero, isSuccPrelimit_of_succ_lt fun x h ↦
    (succ_le_of_lt <| cantor x).trans_lt (H.two_power_lt h)⟩

protected theorem IsStrongLimit.isSuccPrelimit {c} (H : IsStrongLimit c) : IsSuccPrelimit c :=
  H.isSuccLimit.isSuccPrelimit

@[simp]
theorem not_isStrongLimit_zero : ¬ IsStrongLimit (0 : Cardinal) :=
  fun h ↦ h.ne_zero rfl

/-! ### Indexed cardinal `sum` -/

theorem le_sum {ι} (f : ι → Cardinal) (i) : f i ≤ sum f := by
  rw [← Quotient.out_eq (f i)]
  exact ⟨⟨fun a => ⟨i, a⟩, fun a b h => by injection h⟩⟩

theorem iSup_le_sum {ι} (f : ι → Cardinal) : iSup f ≤ sum f :=
  ciSup_le' <| le_sum _

@[simp]
theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
  have := mk_congr (Equiv.sigmaSumDistrib (Quotient.out ∘ f) (Quotient.out ∘ g))
  simp only [comp_apply, mk_sigma, mk_sum, mk_out, lift_id] at this
  exact this

@[simp]
theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
    (Cardinal.sum fun i => f i + g i) = sum f + sum g :=
  sum_add_distrib f g

@[gcongr]
theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
  ⟨(Embedding.refl _).sigmaMap fun i =>
      Classical.choice <| by have := H i; rwa [← Quot.out_eq (f i), ← Quot.out_eq (g i)] at this⟩

theorem mk_le_mk_mul_of_mk_preimage_le {c : Cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
    #α ≤ #β * c := by
  simpa only [← mk_congr (@Equiv.sigmaFiberEquiv α β f), mk_sigma, ← sum_const'] using
    sum_le_sum _ _ hf

theorem lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le {α : Type u} {β : Type v} {c : Cardinal}
    (f : α → β) (hf : ∀ b : β, lift.{v} #(f ⁻¹' {b}) ≤ c) : lift.{v} #α ≤ lift.{u} #β * c :=
  (mk_le_mk_mul_of_mk_preimage_le fun x : ULift.{v} α => ULift.up.{u} (f x.1)) <|
    ULift.forall.2 fun b =>
      (mk_congr <|
            (Equiv.ulift.image _).trans
              (Equiv.trans
                (by
                  rw [Equiv.image_eq_preimage]
                  simp only [preimage, mem_singleton_iff, ULift.up_inj, mem_setOf_eq, coe_setOf]
                  exact Equiv.refl _)
                Equiv.ulift.symm)).trans_le
        (hf b)

end Cardinal

/-! ### Well-ordering theorem -/

open Cardinal in
theorem nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : α → Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ sum g)⟩ := invFun_surjective hf (2 ^ sum g)
    have : g x ≤ sum g := le_sum.{u, u} g x
    not_le_of_gt (by rw [hx]; exact cantor _) this

/-- An embedding of any type to the set of cardinals in its universe. -/
def embeddingToCardinal : α ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : α → α → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)

instance WellOrderingRel.isWellOrder : IsWellOrder α WellOrderingRel :=
  (RelEmbedding.preimage _ _).isWellOrder

instance IsWellOrder.subtype_nonempty : Nonempty { r // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

variable (α) in
/-- The **well-ordering theorem** (or **Zermelo's theorem**): every type has a well-order -/
theorem exists_wellOrder : ∃ (_ : LinearOrder α), WellFoundedLT α := by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel, WellOrderingRel.isWellOrder.toIsWellFounded⟩

namespace Cardinal

/-! ### Bounds on suprema -/

lemma exists_eq_of_iSup_eq_of_not_isSuccPrelimit
    {ι : Type u} (f : ι → Cardinal.{v}) (ω : Cardinal.{v})
    (hω : ¬ IsSuccPrelimit ω)
    (h : ⨆ i : ι, f i = ω) : ∃ i, f i = ω := by
  subst h
  suffices BddAbove (range f) from (isLUB_csSup' this).mem_of_not_isSuccPrelimit hω
  contrapose! hω with hf
  rw [iSup, csSup_of_not_bddAbove hf, csSup_empty]
  exact isSuccPrelimit_bot

lemma exists_eq_of_iSup_eq_of_not_isSuccLimit
    {ι : Type u} [hι : Nonempty ι] (f : ι → Cardinal.{v}) (hf : BddAbove (range f))
    {c : Cardinal.{v}} (hc : ¬ IsSuccLimit c)
    (h : ⨆ i, f i = c) : ∃ i, f i = c := by
  rw [Cardinal.isSuccLimit_iff] at hc
  refine (not_and_or.mp hc).elim (fun e ↦ ⟨hι.some, ?_⟩)
    (Cardinal.exists_eq_of_iSup_eq_of_not_isSuccPrelimit.{u, v} f c · h)
  cases not_not.mp e
  rw [← le_zero_iff] at h ⊢
  exact (le_ciSup hf _).trans h

/-! ### Indexed cardinal `prod` -/

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
  lt_of_not_ge fun ⟨F⟩ => by
    have : Inhabited (∀ i : ι, (g i).out) := by
      refine ⟨fun i => Classical.choice <| mk_ne_zero_iff.1 ?_⟩
      rw [mk_out]
      exact (H i).ne_bot
    let G := invFun F
    have sG : Surjective G := invFun_surjective F.2
    choose C hc using
      show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b by
        intro i
        simp only [not_exists.symm, not_forall.symm]
        refine fun h => (H i).not_ge ?_
        rw [← mk_out (f i), ← mk_out (g i)]
        exact ⟨Embedding.ofSurjective _ h⟩
    let ⟨⟨i, a⟩, h⟩ := sG C
    exact hc i a (congr_fun h _)

theorem prod_le_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
  ⟨Embedding.piCongrRight fun i =>
      Classical.choice <| by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

/-! ### The first infinite cardinal `aleph0` -/

theorem aleph0_pos : 0 < ℵ₀ :=
  pos_iff_ne_zero.2 aleph0_ne_zero

@[simp]
theorem aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c := by
  simpa using lift_le (a := ℵ₀)

@[simp]
theorem lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ := by
  simpa using lift_le (b := ℵ₀)

@[simp]
theorem aleph0_lt_lift {c : Cardinal.{u}} : ℵ₀ < lift.{v} c ↔ ℵ₀ < c := by
  simpa using lift_lt (a := ℵ₀)

@[simp]
theorem lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c < ℵ₀ ↔ c < ℵ₀ := by
  simpa using lift_lt (b := ℵ₀)

@[simp]
theorem aleph0_eq_lift {c : Cardinal.{u}} : ℵ₀ = lift.{v} c ↔ ℵ₀ = c := by
  simpa using lift_inj (a := ℵ₀)

@[simp]
theorem lift_eq_aleph0 {c : Cardinal.{u}} : lift.{v} c = ℵ₀ ↔ c = ℵ₀ := by
  simpa using lift_inj (b := ℵ₀)

/-! ### Properties about the cast from `ℕ` -/

theorem mk_fin (n : ℕ) : #(Fin n) = n := by simp

@[simp]
theorem lift_natCast (n : ℕ) : lift.{u} (n : Cardinal.{v}) = n := by induction n <;> simp [*]

@[simp]
theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift.{u} (ofNat(n) : Cardinal.{v}) = OfNat.ofNat n :=
  lift_natCast n

@[simp]
theorem lift_eq_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
  lift_injective.eq_iff' (lift_natCast n)

@[simp]
theorem lift_eq_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a = ofNat(n) ↔ a = OfNat.ofNat n :=
  lift_eq_nat_iff

@[simp]
theorem nat_eq_lift_iff {n : ℕ} {a : Cardinal.{u}} :
    (n : Cardinal) = lift.{v} a ↔ (n : Cardinal) = a := by
  rw [← lift_natCast.{v,u} n, lift_inj]

@[simp]
theorem zero_eq_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) = lift.{v} a ↔ 0 = a := by
  simpa using nat_eq_lift_iff (n := 0)

@[simp]
theorem one_eq_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) = lift.{v} a ↔ 1 = a := by
  simpa using nat_eq_lift_iff (n := 1)

@[simp]
theorem ofNat_eq_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) = lift.{v} a ↔ (OfNat.ofNat n : Cardinal) = a :=
  nat_eq_lift_iff

@[simp]
theorem lift_le_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a ≤ n ↔ a ≤ n := by
  rw [← lift_natCast.{v,u}, lift_le]

@[simp]
theorem lift_le_one_iff {a : Cardinal.{u}} :
    lift.{v} a ≤ 1 ↔ a ≤ 1 := by
  simpa using lift_le_nat_iff (n := 1)

@[simp]
theorem lift_le_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a ≤ ofNat(n) ↔ a ≤ OfNat.ofNat n :=
  lift_le_nat_iff

@[simp]
theorem nat_le_lift_iff {n : ℕ} {a : Cardinal.{u}} : n ≤ lift.{v} a ↔ n ≤ a := by
  rw [← lift_natCast.{v,u}, lift_le]

@[simp]
theorem one_le_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) ≤ lift.{v} a ↔ 1 ≤ a := by
  simpa using nat_le_lift_iff (n := 1)

@[simp]
theorem ofNat_le_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) ≤ lift.{v} a ↔ (OfNat.ofNat n : Cardinal) ≤ a :=
  nat_le_lift_iff

@[simp]
theorem lift_lt_nat_iff {a : Cardinal.{u}} {n : ℕ} : lift.{v} a < n ↔ a < n := by
  rw [← lift_natCast.{v,u}, lift_lt]

@[simp]
theorem lift_lt_ofNat_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    lift.{v} a < ofNat(n) ↔ a < OfNat.ofNat n :=
  lift_lt_nat_iff

@[simp]
theorem nat_lt_lift_iff {n : ℕ} {a : Cardinal.{u}} : n < lift.{v} a ↔ n < a := by
  rw [← lift_natCast.{v,u}, lift_lt]

@[simp]
theorem zero_lt_lift_iff {a : Cardinal.{u}} :
    (0 : Cardinal) < lift.{v} a ↔ 0 < a := by
  simpa using nat_lt_lift_iff (n := 0)

@[simp]
theorem one_lt_lift_iff {a : Cardinal.{u}} :
    (1 : Cardinal) < lift.{v} a ↔ 1 < a := by
  simpa using nat_lt_lift_iff (n := 1)

@[simp]
theorem ofNat_lt_lift_iff {a : Cardinal.{u}} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < lift.{v} a ↔ (OfNat.ofNat n : Cardinal) < a :=
  nat_lt_lift_iff

theorem mk_coe_finset {α : Type u} {s : Finset α} : #s = ↑(Finset.card s) := by simp

theorem card_le_of_finset {α} (s : Finset α) : (s.card : Cardinal) ≤ #α :=
  @mk_coe_finset _ s ▸ mk_set_le _

instance : CharZero Cardinal := by
  refine ⟨fun a b h ↦ ?_⟩
  rwa [← lift_mk_fin, ← lift_mk_fin, lift_inj, Cardinal.eq, ← Fintype.card_eq,
    Fintype.card_fin, Fintype.card_fin] at h

end Cardinal
