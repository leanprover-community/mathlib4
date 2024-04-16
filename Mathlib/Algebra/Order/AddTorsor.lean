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
by cosets `ℤ + s` of `ℤ` in a larger ring such as `ℂ`.  The order compatibility allows for a
treatment of the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the
formalism of Hahn series.

## Definitions

* OrderedVAdd : inequalities are preserved by translation.
* CancelVAdd : the vector addition version of cancellative addition
* OrderedCancelVAdd : inequalities are preserved and reflected by translation.
* OrderedAddTorsor : An additive torsor over an additive commutative group with compatible order.

-/

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class OrderedVAdd (G P : Type*) [LE G] [LE P] extends VAdd G P where
  protected vadd_le_vadd_left : ∀ c d : P, c ≤ d → ∀ a : G, a +ᵥ c ≤ a +ᵥ d
  protected vadd_le_vadd_right : ∀ a b : G, a ≤ b → ∀ c : P, a +ᵥ c ≤ b +ᵥ c

instance OrderedAddCommMonoid.toOrderedVAdd [OrderedAddCommMonoid G] : OrderedVAdd G G where
  vadd := (· + ·)
  vadd_le_vadd_left _ _ := add_le_add_left
  vadd_le_vadd_right _ _ h a := add_le_add_right h a

instance OrderedVAdd.toCovariantClassLeft [LE G] [LE P] [OrderedVAdd G P] :
    CovariantClass G P (· +ᵥ ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedVAdd.vadd_le_vadd_left _ _ bc a

theorem vAdd_le_vAdd' [Preorder G] [Preorder P] [OrderedVAdd G P] {a b : G} {c d : P} (hab : a ≤ b)
    (hcd : c ≤ d) : a +ᵥ c ≤ b +ᵥ d :=
  (OrderedVAdd.vadd_le_vadd_left _ _ hcd _).trans (OrderedVAdd.vadd_le_vadd_right _ _ hab _)

-- lex prod instances? Pi instances?

section WithTop

namespace WithTop

variable [LE G] [LE P] [OrderedVAdd G P] {g : WithTop G} {p : WithTop P}

instance VAdd : VAdd (WithTop G) (WithTop P) :=
  ⟨Option.map₂ (· +ᵥ ·)⟩

@[simp]
theorem coe_vAdd (g : G) (p : P) :
    ↑(g +ᵥ p) = ((g : WithTop G) +ᵥ (p : WithTop P)) :=
  rfl

@[simp]
theorem top_vAdd : (⊤ : WithTop G) +ᵥ p = ⊤ :=
  rfl

@[simp]
theorem vAdd_top : g +ᵥ (⊤ : WithTop P) = ⊤ := by cases g <;> rfl

@[simp]
theorem vAdd_eq_top : g +ᵥ p = ⊤ ↔ g = ⊤ ∨ p = ⊤ := by
  match g, p with
  | ⊤, _ => simp
  | _, ⊤ => simp
  | (g : G), (p : P) =>
    simp only [← coe_vAdd, coe_ne_top, or_self, iff_false, ne_eq]

theorem vAdd_ne_top : g +ᵥ p ≠ ⊤ ↔ g ≠ ⊤ ∧ p ≠ ⊤ :=
  vAdd_eq_top.not.trans not_or

theorem vAdd_lt_top [LT G] [LT P] : g +ᵥ p < ⊤ ↔ g < ⊤ ∧ p < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, vAdd_ne_top]

/-!
theorem vAdd_eq_coe : ∀ {g : WithTop G} {p : WithTop P} {q : P},
    g +ᵥ p = q ↔ ∃ (g' : G) (p' : P), ↑g' = g ∧ ↑p' = p ∧ g' +ᵥ p' = q
  | ⊤, p, q => by simp
  | some g, ⊤, q => by simp
  | some g, some p, q => by
      simp only [exists_and_left]
-/

theorem vAdd_coe_eq_top_iff {p : P} : g +ᵥ (p : WithTop P) = ⊤ ↔ g = ⊤ := by simp

theorem coe_vAdd_eq_top_iff {g : G} : (g : WithTop G) +ᵥ p = ⊤ ↔ p = ⊤ := by simp

instance instOrderedVAdd [LE G] [LE P] [OrderedVAdd G P] :
    OrderedVAdd (WithTop G) (WithTop P) where
  vadd_le_vadd_left := fun p p' hpp' g => by
    match g, p, p' with
    | ⊤, _, _ => simp
    | (g : G), _, ⊤ => simp
    | (g : G), ⊤, (p' : P) => exact (not_top_le_coe p' hpp').elim
    | (g : G), (p : P), (p' : P) =>
      simp_rw [← WithTop.coe_vAdd, WithTop.coe_le_coe] at *
      exact OrderedVAdd.vadd_le_vadd_left p p' hpp' g
  vadd_le_vadd_right := fun g g' hgg' p => by
    match g, g', p with
    | _, _, ⊤ => simp
    | _, ⊤, (p : P) => simp
    | ⊤, (g' : G), _ => exact (not_top_le_coe g' hgg').elim
    | (g : G), (g' : G), (p : P) =>
      simp_rw [← WithTop.coe_vAdd, WithTop.coe_le_coe] at *
      exact OrderedVAdd.vadd_le_vadd_right g g' hgg' p

end WithTop

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class CancelVAdd (G P : Type*) extends VAdd G P where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class OrderedCancelVAdd (G P : Type*) [LE G] [LE P] extends
    OrderedVAdd G P where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

instance OrderedCancelVAdd.toCancelVAdd [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P] :
    CancelVAdd G P where
  left_cancel a b c h := (OrderedCancelVAdd.le_of_vadd_le_vadd_left a b c h.le).antisymm
    (OrderedCancelVAdd.le_of_vadd_le_vadd_left a c b h.ge)
  right_cancel a b c h := by
    refine (OrderedCancelVAdd.le_of_vadd_le_vadd_right a b c h.le).antisymm ?_
    exact (OrderedCancelVAdd.le_of_vadd_le_vadd_right b a c h.ge)

/-- Vector addition for subsets. -/
protected def Set.vAdd [VAdd G P] : VAdd (Set G) (Set P) :=
  ⟨image2 (· +ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Set.vAdd

open Pointwise

theorem Set.mem_vAdd [VAdd G P] {s : Set G} {t : Set P} {b : P} :
    b ∈ s +ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x +ᵥ y = b :=
  Iff.rfl

theorem Set.vAdd_mem_vAdd [VAdd G P] {s : Set G} {t : Set P} {a : G} {b : P} :
    a ∈ s → b ∈ t → a +ᵥ b ∈ s +ᵥ t :=
  Set.mem_image2_of_mem

namespace VAdd

theorem vAdd_lt_vAdd_of_le_of_lt [LE G] [Preorder P] [OrderedCancelVAdd G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_right a b h₁ c) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := OrderedCancelVAdd.le_of_vadd_le_vadd_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

theorem vAdd_lt_vAdd_of_lt_of_le [Preorder G] [Preorder P] [OrderedCancelVAdd G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_left c d h₂ a) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := OrderedCancelVAdd.le_of_vadd_le_vadd_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

end VAdd

instance (priority := 200) OrderedCancelVAdd.toContravariantClassLeLeft [LE G]
    [LE P] [OrderedCancelVAdd G P] : ContravariantClass G P (· +ᵥ ·) (· ≤ ·) :=
  ⟨OrderedCancelVAdd.le_of_vadd_le_vadd_left⟩

/-- An add action is ordered and cancellative if the underlying vector addition is. -/
class OrderedCancelAddAction (G P : Type*) [OrderedAddCommMonoid G] [LE P] extends
    OrderedCancelVAdd G P where
  /-- Zero is a neutral element for `+ᵥ` -/
  protected zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  /-- Associativity of `+` and `+ᵥ` -/
  add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)

instance OrderedCancelAddCommMonoid.toOrderedCancelAddAction [OrderedCancelAddCommMonoid G] :
    OrderedCancelAddAction G G where
  le_of_vadd_le_vadd_left _ _ _ := le_of_add_le_add_left
  le_of_vadd_le_vadd_right _ _ _ := le_of_add_le_add_right
  zero_vadd p := by rw [zero_vadd]
  add_vadd g g' p := by rw [add_vadd]

instance OrderedCancelAddAction.toAddAction [OrderedAddCommMonoid G] [LE P]
    [OrderedCancelAddAction G P] : AddAction G P where
  zero_vadd := OrderedCancelAddAction.zero_vadd
  add_vadd := OrderedCancelAddAction.add_vadd

/-- An AddTorsor is ordered if vector addition preserves and reflects order. -/
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

variable [VAdd G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `VAdd.antidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`.-/
def antidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
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

variable {s : Set G} {t : Set P} {a : P}

theorem  fst_eq_fst_iff_snd_eq_snd [CancelVAdd G P] {x y : antidiagonal s t a} :
    (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × P).2 :=
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

variable [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P]
  {x y : antidiagonal s t a}

theorem eq_of_fst_eq_fst (h : (x : G × P).fst = (y : G × P).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

theorem eq_of_snd_eq_snd (h : (x : G × P).snd = (y : G × P).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 ≤ (y : G × P).1)
    (h₂ : (x : G × P).2 ≤ (y : G × P).2) : x = y :=
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
  have isrfl : IsRefl (G × P) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
    refine { refl := ?refl }
    simp_all only [Order.Preimage, le_refl, Prod.forall, implies_true]
  have istrns : IsTrans (G × P) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
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
theorem Monotone.vAdd {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [OrderedVAdd G P]
    {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x +ᵥ g x :=
  fun _ _ hab => (OrderedVAdd.vadd_le_vadd_left _ _ (hg hab) _).trans
    (OrderedVAdd.vadd_le_vadd_right _ _ (hf hab) _)


namespace Set

theorem Nonempty.vAdd [VAdd G P] {s : Set G} {t : Set P} :
    s.Nonempty → t.Nonempty → (s +ᵥ t).Nonempty :=
  Nonempty.image2

theorem IsPWO.vAdd [PartialOrder G] [PartialOrder P] [OrderedCancelVAdd G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s +ᵥ t) := by
  rw [← @vadd_image_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.vAdd monotone_snd)

theorem IsWF.vAdd [LinearOrder G] [LinearOrder P] [OrderedCancelVAdd G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s +ᵥ t) :=
  (hs.isPWO.vAdd ht.isPWO).isWF

theorem IsWF.min_vAdd [LinearOrder G] [LinearOrder P] [OrderedCancelVAdd G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.vAdd ht).min (hsn.vAdd htn) = hs.min hsn +ᵥ ht.min htn := by
  refine' le_antisymm (IsWF.min_le _ _ (mem_vAdd.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) _
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact vAdd_le_vAdd' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

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

@[simp]
theorem mem_vAddAntidiagonal :
    x ∈ vAddAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 +ᵥ x.2 = a := by
  simp only [vAddAntidiagonal, Set.Finite.mem_toFinset, VAdd.antidiagonal]
  exact Set.mem_sep_iff

theorem vAddAntidiagonal_mono_left {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : u ⊆ s) :
    vAddAntidiagonal hu ht a ⊆ vAddAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| VAdd.antidiagonal_mono_left h

theorem vAddAntidiagonal_mono_right {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : v ⊆ t) :
    vAddAntidiagonal hs hv a ⊆ vAddAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| VAdd.antidiagonal_mono_right h

theorem support_vAddAntidiagonal_subset_vAdd {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (vAddAntidiagonal hs ht a).Nonempty } ⊆ (s +ᵥ t) :=
  fun a ⟨b, hb⟩ => by
  rw [mem_vAddAntidiagonal] at hb
  rw [Set.mem_vAdd]
  use b.1
  refine { left := hb.1, right := ?_ }
  use b.2
  exact { left := hb.2.1, right := hb.2.2 }

theorem isPWO_support_vAddAntidiagonal {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (vAddAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.vAdd ht).mono (support_vAddAntidiagonal_subset_vAdd)

end

theorem vAddAntidiagonal_min_vAdd_min [LinearOrder G] [LinearOrder P] [OrderedCancelVAdd G P]
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
