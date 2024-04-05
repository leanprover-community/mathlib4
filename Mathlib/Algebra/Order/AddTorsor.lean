/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.AddTorsor
import Mathlib.Order.WellFoundedSet

/-!
# Ordered AddTorsors

This file defines ordered vector addition and proves some properties.  A motivating example is given
by cosets `ℤ + α` of `ℤ` in a larger ring such as `ℂ`.  The order compatibility allows for a
treatment of the `R((z))`-module structure on `(z ^ α) V((z))` for an `R`-module `V`, using the
formalism of Hahn series.

## Definitions

* OrderedVAdd : inequalities are preserved by translation.
* CancelVAdd : the vector addition version of cancellative addition
* OrderedCancelVAdd : inequalities are preserved and reflected by translation.
* OrderedAddTorsor : An additive torsor over an additive commutative group with compatible order.

-/

open Function

variable {α β G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class OrderedVAdd (α β : Type*) [LE α] [LE β] extends VAdd α β where
  protected vadd_le_vadd_left : ∀ a b : β, a ≤ b → ∀ c : α, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : α, c ≤ d → ∀ a : β, c +ᵥ a ≤ d +ᵥ a

instance OrderedAddCommMonoid.toOrderedVAdd [OrderedAddCommMonoid α] : OrderedVAdd α α where
  vadd := (· + ·)
  vadd_le_vadd_left _ _ := add_le_add_left
  vadd_le_vadd_right _ _ h a := add_le_add_right h a

instance OrderedVAdd.toCovariantClassLeft [LE α] [LE β] [OrderedVAdd α β] :
    CovariantClass α β (· +ᵥ ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedVAdd.vadd_le_vadd_left _ _ bc a

-- lex prod instances? Pi instances?

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class CancelVAdd (α β : Type*) extends VAdd α β where
  protected left_cancel : ∀ (a : α) (b c : β), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : α) (c : β), a +ᵥ c = b +ᵥ c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class OrderedCancelVAdd (α β : Type*) [LE α] [LE β] extends
    OrderedVAdd α β where
  protected le_of_vadd_le_vadd_left : ∀ (a : α) (b c : β), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : α) (c : β), a +ᵥ c ≤ b +ᵥ c → a ≤ b

instance OrderedCancelVAdd.toCancelVAdd [PartialOrder α] [PartialOrder β] [OrderedCancelVAdd α β] :
    CancelVAdd α β where
  left_cancel a b c h := (OrderedCancelVAdd.le_of_vadd_le_vadd_left a b c h.le).antisymm
    (OrderedCancelVAdd.le_of_vadd_le_vadd_left a c b h.ge)
  right_cancel a b c h := by
    refine (OrderedCancelVAdd.le_of_vadd_le_vadd_right a b c h.le).antisymm ?_
    exact (OrderedCancelVAdd.le_of_vadd_le_vadd_right b a c h.ge)

instance OrderedCancelAddCommMonoid.toOrderedCancelVAdd [OrderedCancelAddCommMonoid α] :
    OrderedCancelVAdd α α where
  le_of_vadd_le_vadd_left _ _ _ := le_of_add_le_add_left
  le_of_vadd_le_vadd_right _ _ _ := le_of_add_le_add_right

namespace VAdd

theorem vAdd_lt_vAdd_of_le_of_lt [LE α] [Preorder β] [OrderedCancelVAdd α β]
    {a b : α} {c d : β} (h₁ : a ≤ b) (h₂ : c < d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_right a b h₁ c) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := OrderedCancelVAdd.le_of_vadd_le_vadd_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

theorem vAdd_lt_vAdd_of_lt_of_le [Preorder α] [Preorder β] [OrderedCancelVAdd α β]
    {a b : α} {c d : β} (h₁ : a < b) (h₂ : c ≤ d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_left c d h₂ a) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := OrderedCancelVAdd.le_of_vadd_le_vadd_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

end VAdd

instance (priority := 200) OrderedCancelVAdd.toContravariantClassLeLeft [LE α]
    [LE β] [OrderedCancelVAdd α β] : ContravariantClass α β (· +ᵥ ·) (· ≤ ·) :=
  ⟨OrderedCancelVAdd.le_of_vadd_le_vadd_left⟩

class OrderedAddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| OrderedAddCommGroup G] [LE P]
    extends AddTorsor G P where
  protected le_of_vadd_left_iff : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c ↔ b ≤ c
  protected vadd_le_vadd_right_iff : ∀ (c d : G) (a : P), c ≤ d ↔ c +ᵥ a ≤ d +ᵥ a

instance instOrderedAddTorsor.toOrderedCancelVAdd {G : outParam (Type*)} {P : Type*}
    [outParam <| OrderedAddCommGroup G] [LE P] [OrderedAddTorsor G P] : OrderedCancelVAdd G P where
  vadd_le_vadd_left x y h g := (OrderedAddTorsor.le_of_vadd_left_iff g x y).mpr h
  vadd_le_vadd_right g g' h a := (OrderedAddTorsor.vadd_le_vadd_right_iff g g' a).mp h
  le_of_vadd_le_vadd_left g x y h := (OrderedAddTorsor.le_of_vadd_left_iff g x y).mp h
  le_of_vadd_le_vadd_right g g' a h := (OrderedAddTorsor.vadd_le_vadd_right_iff g g' a).mpr h

namespace VAdd

variable [VAdd α β] {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : β} {x : α × β}

/-- `VAdd.antidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`.-/
def antidiagonal (s : Set α) (t : Set β) (a : β) : Set (α × β) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 +ᵥ x.2 = a }

@[simp]
theorem mem_Antidiagonal : x ∈ antidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 +ᵥ x.2 = a :=
  Iff.rfl

theorem antidiagonal_mono_left (h : s₁ ⊆ s₂) :
    antidiagonal s₁ t a ⊆ antidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

theorem antidiagonal_mono_right (h : t₁ ⊆ t₂) :
    antidiagonal s t₁ a ⊆ antidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end VAdd

namespace vAddAntidiagonal

open VAdd

variable {s : Set α} {t : Set β} {a : β}

theorem  fst_eq_fst_iff_snd_eq_snd [CancelVAdd α β] {x y : antidiagonal s t a} :
    (x : α × β).1 = (y : α × β).1 ↔ (x : α × β).2 = (y : α × β).2 :=
  ⟨fun h =>
    CancelVAdd.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    CancelVAdd.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

variable [PartialOrder α] [PartialOrder β] [OrderedCancelVAdd α β]
  {x y : antidiagonal s t a}

theorem eq_of_fst_eq_fst (h : (x : α × β).fst = (y : α × β).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

theorem eq_of_snd_eq_snd (h : (x : α × β).snd = (y : α × β).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × β).1 ≤ (y : α × β).1)
    (h₂ : (x : α × β).2 ≤ (y : α × β).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (vAdd_lt_vAdd_of_lt_of_le hlt h₂).ne <|
        (mem_Antidiagonal.1 x.2).2.2.trans (mem_Antidiagonal.1 y.2).2.2.symm

theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (antidiagonal s t a).Finite := by
  refine' Set.not_infinite.1 fun h => _
  have h1 : (antidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_Antidiagonal.1 (hf n)).1
  have h2 : (antidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_Antidiagonal.1 (hf n)).2.1
  have isrfl : IsRefl (α × β) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
    refine { refl := ?refl }
    simp_all only [Order.Preimage, le_refl, Prod.forall, implies_true]
  have istrns : IsTrans (α × β) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
    refine { trans := ?trans }
    simp_all only [Order.Preimage, Prod.forall]
    exact fun a _ a_1 _ a_2 _ a_3 a_4 ↦ Preorder.le_trans a a_1 a_2 a_3 a_4
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq (fun n => h.natEmbedding _ n) fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.natEmbedding _) (g x)) fun n => (h.natEmbedding _ _).2
  refine' mn.ne (g.injective <| (h.natEmbedding _).injective _)
  exact eq_of_fst_le_fst_of_snd_le_snd (hg _ _ mn.le) h2'

end vAddAntidiagonal

/-- The vector sum of two monotone functions is monotone. -/
theorem Monotone.vAdd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ] [OrderedVAdd α β]
    {f : γ → α} {g : γ → β} (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x +ᵥ g x :=
  fun _ _ hab => (OrderedVAdd.vadd_le_vadd_left _ _ (hg hab) _).trans
    (OrderedVAdd.vadd_le_vadd_right _ _ (hf hab) _)

theorem Set.IsPWO.vAdd [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P] {s : Set G} {t : Set P}
    (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO ((fun x ↦ x.1 +ᵥ x.2) '' s ×ˢ t) := by
  exact (hs.prod ht).image_of_monotone (monotone_fst.vAdd monotone_snd)

namespace Finset

section

variable [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P] {s : Set G} {t : Set P}
    (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P} {hv : v.IsPWO}
    {x : G × P}

/-- `Finset.vAddAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose vector addition yields `a`, but its construction requires proofs that `s` and
`t` are well-ordered. -/
noncomputable def vAddAntidiagonal [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) : Finset (G × P) :=
  (vAddAntidiagonal.finite_of_isPWO hs ht a).toFinset

theorem mem_vAddAntidiagonal :
    x ∈ vAddAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 +ᵥ x.2 = a := by
  simp only [vAddAntidiagonal, Set.Finite.mem_toFinset, VAdd.antidiagonal]
  exact Set.mem_sep_iff

theorem vAddAntidiagonal_mono_left (h : u ⊆ s) : vAddAntidiagonal hu ht a ⊆ vAddAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| VAdd.antidiagonal_mono_left h

theorem vAddAntidiagonal_mono_right (h : v ⊆ t) :
    vAddAntidiagonal hs hv a ⊆ vAddAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| VAdd.antidiagonal_mono_right h

theorem support_vAddAntidiagonal_subset_vAdd :
    { a | (vAddAntidiagonal hs ht a).Nonempty } ⊆ ((fun x ↦ x.1 +ᵥ x.2) '' s ×ˢ t) :=
  fun a ⟨b, hb⟩ => by
  rw [mem_vAddAntidiagonal] at hb
  refine (Set.mem_image (fun x ↦ x.1 +ᵥ x.2) (s ×ˢ t) a).mpr (Exists.intro b ?_)
  exact { left := { left := hb.1, right := hb.2.1}, right := hb.2.2 }

theorem isPWO_support_vAddAntidiagonal : { a | (vAddAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.vAdd ht).mono (support_vAddAntidiagonal_subset_vAdd hs ht)

end

theorem vAddAntidiagonal_min_vAdd_min [LinearOrder G] [LinearOrder P]  [OrderedCancelVAdd G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty) (hnt : t.Nonempty) :
    vAddAntidiagonal hs.isPWO ht.isPWO (hs.min hns +ᵥ ht.min hnt) =
      {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_vAddAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (VAdd.vAdd_lt_vAdd_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, CancelVAdd.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
