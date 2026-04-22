/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-!
# Enumerating a cofinal set

We define a typeclass `IsRegularCardinalOrder` for well-ordered types, whose order type equals (the
initial ordinal of) their cofinality. This notion does not appear in the literature, but intends to
generalize the properties of intervals `Iio c.ord`, wherever `c` is a regular cardinal. Other
instances of this typeclass include `ℕ`, `Ordinal`, and `Cardinal`.

If `s` is a cofinal subset of a regular cardinal order `α`, there exists a unique order isomorphism
`α ≃o s`, which we call `Order.enum`. When `α = Ordinal`, this is referred to as the enumerator
function of the set. Note that if `α = ℕ`, then this definition matches `Nat.nth`.
-/

public section

universe u

open Cardinal Order Ordinal Set

variable {α : Type*}

/-- A typeclass which expresses that the order type of a well-order equals (the initial ordinal of)
its cofinality.

If `α` is infinite, this implies that `α` is order isomorphic to `Iio c.ord` for some regular
cardinal `c`. In the informal literature, one often says that `α` is a regular cardinal, by abuse
of notation. -/
class IsRegularCardinalOrder (α : Type*) [LinearOrder α] [WellFoundedLT α] where
  type_le_ord_cof : typeLT α ≤ (cof α).ord

instance : IsRegularCardinalOrder ℕ := ⟨by simp⟩

instance (priority := low) [LinearOrder α] [WellFoundedLT α] [Subsingleton α] :
    IsRegularCardinalOrder α where
  type_le_ord_cof := by
    cases isEmpty_or_nonempty α
    · simpa
    · cases nonempty_unique α
      have := BoundedOrder.ofUnique α
      simp

instance : IsRegularCardinalOrder Ordinal where
  type_le_ord_cof := by
    rw [type_lt_ordinal, ← ord_univ, ord_le_ord, le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s), ← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

namespace Order
variable [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

theorem ord_cof_eq_type_lt : (cof α).ord = typeLT α := by
  apply IsRegularCardinalOrder.type_le_ord_cof.antisymm'
  rw [ord_le, card_type]
  exact cof_le_cardinalMk α

@[simp]
theorem cof_eq_card : cof α = #α := by
  rw [← card_type LT.lt, ← ord_cof_eq_type_lt, card_ord]

@[simp]
theorem ord_cardinalMk : ord (#α) = typeLT α := by
  rw [← ord_cof_eq_type_lt, cof_eq_card]

@[simp]
theorem cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u + 1} := by
  simp [← Cardinal.univ_id]

theorem ordinalType_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : typeLT s = typeLT α := by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk, ord_le, card_type, ← cof_eq_card]
  exact cof_le hs

/-- Enumerate the elements of a cofinal subset of `α` by `α` itself. This is a generalization of
`Nat.nth`. -/
noncomputable def enum (s : Set α) (hs : IsCofinal s) : α ≃o s :=
  .ofRelIsoLT (type_eq.1 (ordinalType_eq_of_isCofinal hs).symm).some

theorem enum_le_of_forall_lt {a o : α} {s : Set α} {hs : IsCofinal s} (ho : o ∈ s)
    (H : ∀ b < a, enum s hs b < o) : enum s hs a ≤ o := by
  rw [← Subtype.coe_mk o ho, Subtype.coe_le_coe, ← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

theorem enum_succ_le_of_lt [SuccOrder α] {a o : α} {s : Set α} {hs : IsCofinal s} (ha : o ∈ s)
    (H : enum s hs a < o) : enum s hs (succ a) ≤ o := by
  refine enum_le_of_forall_lt ha fun b hb ↦ H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]
theorem enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩ := by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

end Order

-- TODO: Everything below can be subsumed by `Order.enum`.

namespace Ordinal

variable {o a b : Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals.

The definition is an implementation detail; this function is entirely characterized by being an
order isomorphism. See `enumOrdOrderIso`. -/
noncomputable def enumOrd (s : Set Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  sInf (s ∩ { b | ∀ c, c < o → enumOrd s c < b })
termination_by o

variable {s : Set Ordinal.{u}}

theorem enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  exact csInf_le' ⟨ha, H⟩

/-- The set in the definition of `enumOrd` is nonempty. -/
private theorem enumOrd_nonempty (hs : ¬ BddAbove s) (o : Ordinal) :
    (s ∩ { b | ∀ c, c < o → enumOrd s c < b }).Nonempty := by
  rw [not_bddAbove_iff] at hs
  obtain ⟨a, ha⟩ := bddAbove_of_small (s := enumOrd s '' Iio o)
  obtain ⟨b, hb, hba⟩ := hs a
  exact ⟨b, hb, fun c hc ↦ (ha (mem_image_of_mem _ hc)).trans_lt hba⟩

private theorem enumOrd_mem_aux (hs : ¬ BddAbove s) (o : Ordinal) :
    enumOrd s o ∈ s ∩ { b | ∀ c, c < o → enumOrd s c < b } := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

theorem enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enumOrd s o ∈ s :=
  (enumOrd_mem_aux hs o).1

theorem enumOrd_strictMono (hs : ¬ BddAbove s) : StrictMono (enumOrd s) :=
  fun a b ↦ (enumOrd_mem_aux hs b).2 a

theorem enumOrd_injective (hs : ¬ BddAbove s) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).injective

theorem enumOrd_inj (hs : ¬ BddAbove s) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b :=
  (enumOrd_injective hs).eq_iff

theorem enumOrd_le_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a ≤ enumOrd s b ↔ a ≤ b :=
  (enumOrd_strictMono hs).le_iff_le

theorem enumOrd_lt_enumOrd (hs : ¬ BddAbove s) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b :=
  (enumOrd_strictMono hs).lt_iff_lt

theorem id_le_enumOrd (hs : ¬ BddAbove s) : id ≤ enumOrd s :=
  (enumOrd_strictMono hs).id_le

theorem le_enumOrd_self (hs : ¬ BddAbove s) {a} : a ≤ enumOrd s a :=
  (enumOrd_strictMono hs).le_apply

theorem enumOrd_succ_le (hs : ¬ BddAbove s) (ha : a ∈ s) (hb : enumOrd s b < a) :
    enumOrd s (succ b) ≤ a := by
  apply enumOrd_le_of_forall_lt ha
  intro c hc
  rw [lt_succ_iff] at hc
  exact ((enumOrd_strictMono hs).monotone hc).trans_lt hb

theorem range_enumOrd (hs : ¬ BddAbove s) : range (enumOrd s) = s := by
  ext a
  let t := { b | a ≤ enumOrd s b }
  constructor
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, (enumOrd_le_of_forall_lt ha ?_).antisymm ?_⟩
    · intro b hb
      by_contra! hb'
      exact hb.not_ge (csInf_le' hb')
    · exact csInf_mem (s := t) ⟨a, (enumOrd_strictMono hs).id_le a⟩

theorem enumOrd_surjective (hs : ¬ BddAbove s) {b : Ordinal} (hb : b ∈ s) :
    ∃ a, enumOrd s a = b := by
  rwa [← range_enumOrd hs] at hb

theorem enumOrd_le_of_subset {t : Set Ordinal} (hs : ¬ BddAbove s) (hst : s ⊆ t) :
    enumOrd t ≤ enumOrd s := by
  intro a
  rw [enumOrd, enumOrd]
  gcongr with b c
  exacts [enumOrd_nonempty hs a, enumOrd_le_of_subset hs hst c]
termination_by a => a

/-- A characterization of `enumOrd`: it is the unique strict monotonic function with range `s`. -/
theorem eq_enumOrd (f : Ordinal → Ordinal) (hs : ¬ BddAbove s) :
    enumOrd s = f ↔ StrictMono f ∧ range f = s := by
  constructor
  · rintro rfl
    exact ⟨enumOrd_strictMono hs, range_enumOrd hs⟩
  · rintro ⟨h₁, h₂⟩
    rwa [← (enumOrd_strictMono hs).range_inj h₁, range_enumOrd hs, eq_comm]

theorem enumOrd_range {f : Ordinal → Ordinal} (hf : StrictMono f) : enumOrd (range f) = f :=
  (eq_enumOrd _ hf.not_bddAbove_range_of_wellFoundedLT).2 ⟨hf, rfl⟩

/-- If `s` is closed under nonempty suprema, then its enumerator function is normal.
See also `enumOrd_isNormal_iff_isClosed`. -/
theorem isNormal_enumOrd (H : ∀ t ⊆ s, t.Nonempty → BddAbove t → sSup t ∈ s) (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) := by
  refine isNormal_iff.2 ⟨enumOrd_strictMono hs, fun o ho a ha ↦ ?_⟩
  trans ⨆ b : Iio o, enumOrd s b
  · refine enumOrd_le_of_forall_lt ?_ (fun b hb ↦ (enumOrd_strictMono hs (lt_succ b)).trans_le ?_)
    · have : Nonempty (Iio o) := ⟨0, ho.bot_lt⟩
      apply H _ _ (range_nonempty _) bddAbove_of_small
      rintro _ ⟨c, rfl⟩
      exact enumOrd_mem hs c
    · exact Ordinal.le_iSup _ (⟨_, ho.succ_lt hb⟩ : Iio o)
  · exact Ordinal.iSup_le fun x ↦ ha _ x.2

@[simp]
theorem enumOrd_univ : enumOrd Set.univ = id := by
  rw [← range_id]
  exact enumOrd_range strictMono_id

@[simp] lemma enumOrd_zero : enumOrd s 0 = sInf s := by rw [enumOrd]; simp

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
@[expose]
noncomputable def enumOrdOrderIso (s : Set Ordinal) (hs : ¬ BddAbove s) : Ordinal ≃o s :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hs o⟩) (enumOrd_strictMono hs) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hs s.prop
    ⟨a, Subtype.ext ha⟩

end Ordinal
