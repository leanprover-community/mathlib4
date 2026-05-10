/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.SetTheory.Ordinal.Univ

/-!
# Enumerating a cofinal set

We define a typeclass `IsRegularCardinalOrder` for well-ordered types, whose order type equals (the
initial ordinal of) their cofinality. This notion does not appear in the literature, but intends to
generalize the properties of intervals `Iio c.ord`, wherever `c` is a regular cardinal. Other
instances of this typeclass include `ℕ`, `Ordinal`, and `Cardinal`.

If `s` is a cofinal subset of a regular cardinal order `α`, there exists a unique order isomorphism
`α ≃o s`, which we call `Order.enum`. When `α = Ordinal`, this is referred to as the enumerator
function of the set. Note that if `α = ℕ`, then this definition matches `Nat.nth`.

## Main results

- `Order.enum_eq_iff`: `Order.enum s _` is the unique strictly monotonic function with range `s`.
- `Order.isNormal_enum_iff`: club sets correspond one to one with normal functions.

## Todo

- Deprecate `Ordinal.enumOrd` in favor of `Order.enum`.
- Prove that `Order.enum` on the naturals coincides with `Nat.nth`.
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

variable {s : Set α} {hs : IsCofinal s}

theorem enum_le_of_forall_lt {a o : α} (ho : o ∈ s) (H : ∀ b < a, enum s hs b < o) :
    enum s hs a ≤ o := by
  rw [← Subtype.coe_mk o ho, Subtype.coe_le_coe, ← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

theorem enum_succ_le_of_lt [SuccOrder α] {a o : α} (ha : o ∈ s) (H : enum s hs a < o) :
    enum s hs (succ a) ≤ o := by
  refine enum_le_of_forall_lt ha fun b hb ↦ H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]
theorem enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩ := by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

theorem enum_anti {t : Set α} {x : α} (h : s ⊆ t) : enum t (hs.mono h) x ≤ (enum s hs x).1 := by
  induction x using WellFoundedLT.induction with | ind x IH
  exact enum_le_of_forall_lt (h (Subtype.prop _)) fun y hy ↦
    (IH y hy).trans_lt ((enum s hs).strictMono hy)

/-- A characterization of `Order.enum s _`: it is the unique strict monotonic function with range
`s`. -/
theorem enum_eq_iff {f : α → α} : Subtype.val ∘ enum s hs = f ↔ StrictMono f ∧ range f = s := by
  have H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  constructor
  · rintro rfl
    use (Subtype.strictMono_coe _).comp (enum s hs).strictMono
    simp
  · rintro ⟨hf, rfl⟩
    rw [← StrictMono.range_inj H hf]
    simp
    rfl

@[simp]
theorem enum_range {f : α → α} (hf : StrictMono f) :
    enum (range f) (isCofinal_range_of_strictMono hf) = hf.orderIso := by
  ext x
  apply congrFun (enum_eq_iff.2 ⟨?_, ?_⟩)
  · exact (Subtype.strictMono_coe _).comp (OrderIso.strictMono _)
  · simp

theorem enum_bot {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] {s : Set α} {hs : IsCofinal s} : enum s hs ⊥ = sInf s := by
  let : Bot s := ⟨⟨sInf s, csInf_mem hs.nonempty⟩⟩
  let : OrderBot s := .mk fun a ↦ csInf_le' a.2
  rw [OrderIso.map_bot]
  rfl

/-- Club sets correspond one to one with normal functions. -/
theorem isNormal_enum_iff {s : Set α} {hs : IsCofinal s} :
    IsNormal (Subtype.val ∘ enum s hs) ↔ DirSupClosed s := by
  let H := (Subtype.strictMono_coe _).comp (enum s hs).strictMono
  refine ⟨fun he ↦ by simpa using he.dirSupClosed_range, ?_⟩
  rw [isNormal_iff, dirSupClosed_iff_of_linearOrder]
  refine fun hs' ↦ ⟨H, fun a ha b hb ↦ ?_⟩
  have bdd : BddAbove (Subtype.val ∘ enum s hs '' Iio a) := by
    use enum s hs a
    simpa [upperBounds] using fun x hx ↦ hx.le
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  trans sSup ((Subtype.val ∘ enum s hs) '' Iio a)
  · refine enum_le_of_forall_lt (hs' ?_ ?_ (isLUB_csSup' bdd)) fun b hb ↦ ?_
    · grind
    · simpa using ha.ne_bot
    · obtain ⟨c, hca, hbc⟩ := ha.lt_iff_exists_lt.1 hb
      refine (H hbc).trans_le <| le_csSup bdd ⟨c, ?_⟩
      simpa
  · apply csSup_le'
    simpa [upperBounds]

end Order
