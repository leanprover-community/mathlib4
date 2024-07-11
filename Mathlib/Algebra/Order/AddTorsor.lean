/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Order.WellFoundedSet

/-!
# Ordered vector addition
This file defines ordered vector addition and proves some properties.  A motivating example is given
by the additive action of `ℤ` on subsets of reals that are closed under integer translation.  The
order compatibility allows for a treatment of the `R((z))`-module structure on `(z ^ s) V((z))` for
an `R`-module `V`, using the formalism of Hahn series.

## Implementation notes
* Beause these classes mix the algebra and order hierarchies, we write them as `Prop`-valued mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class.  To implement them,
  combine `[AddTorsor G P]` with `[MonoVAddReflectLE G P]`

## Definitions
* MonoVAddMono : inequalities are preserved by translation.
* CancelVAdd : the vector addition version of cancellative addition
* MonoVAddReflectLE : inequalities are preserved and reflected by translation.
* VAdd.antidiagonal : Set-valued antidiagonal for VAdd.
* Finset.vAddAntidiagonal : Finset antidiagonal for PWO inputs.

## Instances
* OrderedAddCommMonoid.toMonoVAddMono
* MonoVAddMono.toCovariantClassLeft
* MonoVAddReflectLE.toCancelVAdd
* OrderedCancelAddCommMonoid.toMonoVAddReflectLE
* MonoVAddReflectLE.toContravariantClassLeft

## TODO
* Multiplicativize
* (lex) prod instances
* Pi instances

-/

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class MonoVAddMono (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a

/-- An ordered scalar multiplication is a bi-monotone scalar multiplication. -/
@[to_additive]
class MonoSMulMono (G P : Type*) [LE G] [LE P] [SMul G P] : Prop where
  protected smul_le_smul_left : ∀ a b : P, a ≤ b → ∀ c : G, c • a ≤ c • b
  protected smul_le_smul_right : ∀ c d : G, c ≤ d → ∀ a : P, c • a ≤ d • a

@[to_additive]
instance MonoSMulMono.toCovariantClassLeft [LE G] [LE P] [SMul G P] [MonoSMulMono G P] :
    CovariantClass G P (· • ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ MonoSMulMono.smul_le_smul_left _ _ bc a

@[to_additive]
instance [OrderedCommMonoid G] : MonoSMulMono G G where
  smul_le_smul_left _ _ := mul_le_mul_left'
  smul_le_smul_right _ _ := mul_le_mul_right'

/-- We get an ordered commutative monoid from ordered scalar multiplication. Will anyone use? -/
@[to_additive "We get an ordered additive commutative monoid from ordered vector addition. Will
anyone use?"]
def MonoSMulMono.toOrderedCommMonoid [CommMonoid G] [PartialOrder G] [MonoSMulMono G G] :
    OrderedCommMonoid G where
  mul_le_mul_left := MonoSMulMono.smul_le_smul_left

@[to_additive]
theorem MonoSMulMono.smul_le_smul [Preorder G] [Preorder P] [SMul G P] [MonoSMulMono G P] {a b : G}
    {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d :=
  (MonoSMulMono.smul_le_smul_left _ _ hcd _).trans (MonoSMulMono.smul_le_smul_right _ _ hab _)

section WithTop

namespace WithTop

variable [LE G] [LE P] [_root_.SMul G P] [MonoSMulMono G P] {g : WithTop G} {p : WithTop P}

@[to_additive]
instance SMul : SMul (WithTop G) (WithTop P) :=
  ⟨Option.map₂ (· • ·)⟩

@[to_additive (attr := simp)]
theorem coe_SMul (g : G) (p : P) :
    ↑(g • p) = ((g : WithTop G) • (p : WithTop P)) :=
  rfl

@[to_additive (attr := simp)]
theorem top_SMul : (⊤ : WithTop G) • p = ⊤ :=
  rfl

@[to_additive (attr := simp)]
theorem SMul_top : g • (⊤ : WithTop P) = ⊤ := by cases g <;> rfl

@[to_additive (attr := simp)]
theorem SMul_eq_top : g • p = ⊤ ↔ g = ⊤ ∨ p = ⊤ := by
  match g, p with
  | ⊤, _ => simp
  | _, ⊤ => simp
  | (g : G), (p : P) =>
    simp only [← coe_SMul, coe_ne_top, or_self, iff_false, ne_eq]

@[to_additive]
theorem SMul_ne_top : g • p ≠ ⊤ ↔ g ≠ ⊤ ∧ p ≠ ⊤ :=
  SMul_eq_top.not.trans not_or

@[to_additive]
theorem SMul_lt_top [LT G] [LT P] : g • p < ⊤ ↔ g < ⊤ ∧ p < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, SMul_ne_top]

/-!
theorem vAdd_eq_coe : ∀ {g : WithTop G} {p : WithTop P} {q : P},
    g +ᵥ p = q ↔ ∃ (g' : G) (p' : P), ↑g' = g ∧ ↑p' = p ∧ g' +ᵥ p' = q
  | ⊤, p, q => by simp
  | some g, ⊤, q => by simp
  | some g, some p, q => by
      simp only [exists_and_left]
-/

@[to_additive]
theorem sMul_coe_eq_top_iff {p : P} : g • (p : WithTop P) = ⊤ ↔ g = ⊤ := by simp

@[to_additive]
theorem coe_sMul_eq_top_iff {g : G} : (g : WithTop G) • p = ⊤ ↔ p = ⊤ := by simp

@[to_additive]
instance [LE G] [LE P] [MonoSMulMono G P] :
    MonoSMulMono (WithTop G) (WithTop P) where
  smul_le_smul_left := fun p p' hpp' g => by
    match g, p, p' with
    | ⊤, _, _ => simp
    | (g : G), _, ⊤ => simp
    | (g : G), ⊤, (p' : P) => exact (not_top_le_coe p' hpp').elim
    | (g : G), (p : P), (p' : P) =>
      simp_rw [← WithTop.coe_SMul, WithTop.coe_le_coe] at *
      exact MonoSMulMono.smul_le_smul_left p p' hpp' g
  smul_le_smul_right := fun g g' hgg' p => by
    match g, g', p with
    | _, _, ⊤ => simp
    | _, ⊤, (p : P) => simp
    | ⊤, (g' : G), _ => exact (not_top_le_coe g' hgg').elim
    | (g : G), (g' : G), (p : P) =>
      simp_rw [← WithTop.coe_SMul, WithTop.coe_le_coe] at *
      exact MonoSMulMono.smul_le_smul_right g g' hgg' p

end WithTop

end WithTop

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class CancelVAdd (G P : Type*) [VAdd G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right. -/
@[to_additive]
class CancelSMul (G P : Type*) [SMul G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a • b = a • c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a • c = b • c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class MonoVAddReflectLE (G P : Type*) [LE G] [LE P] [VAdd G P] extends MonoVAddMono G P : Prop where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

/-- An ordered cancellative scalar multiplication is an ordered scalar multiplication that is
  cancellative. -/
@[to_additive]
class MonoSMulReflectLE (G P : Type*) [LE G] [LE P] [SMul G P] extends MonoSMulMono G P : Prop where
  protected le_of_smul_le_smul_left : ∀ (a : G) (b c : P), a • b ≤ a • c → b ≤ c
  protected le_of_smul_le_smul_right : ∀ (a b : G) (c : P), a • c ≤ b • c → a ≤ b

@[to_additive]
instance [PartialOrder G] [PartialOrder P] [SMul G P] [MonoSMulReflectLE G P] : CancelSMul G P where
  left_cancel a b c h := (MonoSMulReflectLE.le_of_smul_le_smul_left a b c h.le).antisymm
    (MonoSMulReflectLE.le_of_smul_le_smul_left a c b h.ge)
  right_cancel a b c h := by
    refine (MonoSMulReflectLE.le_of_smul_le_smul_right a b c h.le).antisymm ?_
    exact (MonoSMulReflectLE.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]
instance [OrderedCancelCommMonoid G] : MonoSMulReflectLE G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]
instance (priority := 200) [LE G] [LE P] [SMul G P] [MonoSMulReflectLE G P] :
    ContravariantClass G P (· • ·) (· ≤ ·) :=
  ⟨MonoSMulReflectLE.le_of_smul_le_smul_left⟩

namespace SMul

@[to_additive]
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [MonoSMulReflectLE G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
    a • c < b • d := by
  refine lt_of_le_of_lt (MonoSMulMono.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_le (MonoSMulMono.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := MonoSMulReflectLE.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [MonoSMulReflectLE G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) :
    a • c < b • d := by
  refine lt_of_le_of_lt (MonoSMulMono.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_le (MonoSMulMono.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := MonoSMulReflectLE.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

end SMul

/-- Scalar multiplication for subsets. -/
@[to_additive "Vector addition for subsets."]
protected def Set.SMul [SMul G P] : SMul (Set G) (Set P) :=
  ⟨image2 (· • ·)⟩

scoped[Pointwise] attribute [instance] Set.SMul
scoped[Pointwise] attribute [instance] Set.VAdd

open Pointwise

@[to_additive]
theorem Set.mem_SMul [SMul G P] {s : Set G} {t : Set P} {b : P} :
    b ∈ s • t ↔ ∃ x ∈ s, ∃ y ∈ t, x • y = b :=
  Iff.rfl

@[to_additive]
theorem Set.sMul_mem_SMul [SMul G P] {s : Set G} {t : Set P} {a : G} {b : P} :
    a ∈ s → b ∈ t → a • b ∈ s • t :=
  Set.mem_image2_of_mem

namespace SMul

variable [SMul G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `SMul.antidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that scalar multiply to `a`.-/
@[to_additive "`VAdd.antidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that vector-add to `a`."]
def antidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]
theorem mem_Antidiagonal : x ∈ antidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a :=
  Iff.rfl

@[to_additive]
theorem antidiagonal_mono_left (h : s₁ ⊆ s₂) :
    antidiagonal s₁ t a ⊆ antidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
theorem antidiagonal_mono_right (h : t₁ ⊆ t₂) :
    antidiagonal s t₁ a ⊆ antidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end SMul

namespace SMulAntidiagonal

open SMul

variable {s : Set G} {t : Set P} {a : P}

@[to_additive VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
theorem fst_eq_fst_iff_snd_eq_snd [SMul G P] [CancelSMul G P] {x y : antidiagonal s t a} :
    (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × P).2 :=
  ⟨fun h =>
    CancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    CancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

variable [PartialOrder G] [PartialOrder P] [SMul G P] [MonoSMulReflectLE G P]
  {x y : antidiagonal s t a}

@[to_additive VAddAntidiagonal.eq_of_fst_eq_fst]
theorem eq_of_fst_eq_fst (h : (x : G × P).fst = (y : G × P).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]
theorem eq_of_snd_eq_snd (h : (x : G × P).snd = (y : G × P).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

@[to_additive VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 ≤ (y : G × P).1)
    (h₂ : (x : G × P).2 ≤ (y : G × P).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (smul_lt_smul_of_lt_of_le hlt h₂).ne <|
        (mem_Antidiagonal.1 x.2).2.2.trans (mem_Antidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]
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

end SMulAntidiagonal

/-- The vector sum of two monotone functions is monotone. -/
@[to_additive]
theorem Monotone.SMul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [MonoSMulMono G P] {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (MonoSMulMono.smul_le_smul_left _ _ (hg hab) _).trans
    (MonoSMulMono.smul_le_smul_right _ _ (hf hab) _)

namespace Set

@[to_additive]
theorem Nonempty.SMul [SMul G P] {s : Set G} {t : Set P} :
    s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image2

@[to_additive]
theorem IsPWO.SMul [PartialOrder G] [PartialOrder P] [SMul G P] [MonoSMulReflectLE G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s • t) := by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.SMul monotone_snd)

@[to_additive]
theorem IsWF.SMul [LinearOrder G] [LinearOrder P] [SMul G P] [MonoSMulReflectLE G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s • t) :=
  (hs.isPWO.SMul ht.isPWO).isWF

@[to_additive]
theorem IsWF.min_SMul [LinearOrder G] [LinearOrder P] [_root_.SMul G P] [MonoSMulReflectLE G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.SMul ht).min (hsn.SMul htn) = hs.min hsn • ht.min htn := by
  refine' le_antisymm (IsWF.min_le _ _ (mem_SMul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) _
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact MonoSMulMono.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

section

variable [PartialOrder G] [PartialOrder P] [SMul G P] [MonoSMulReflectLE G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) {u : Set G} {hu : u.IsPWO} {v : Set P}
    {hv : v.IsPWO} {x : G × P}

/-- `Finset.SMulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose scalar multiplicatoin yields `a`, but its construction requires proofs that `s`
and `t` are well-ordered. -/
@[to_additive "`Finset.VAddAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` whose vector addition yields `a`, but its construction requires proofs that `s` and
`t` are well-ordered."]
noncomputable def SMulAntidiagonal [PartialOrder G] [PartialOrder P] [MonoSMulReflectLE G P]
    {s : Set G} {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) (a : P) : Finset (G × P) :=
  (SMulAntidiagonal.finite_of_isPWO hs ht a).toFinset

@[to_additive (attr := simp)]
theorem mem_SMulAntidiagonal :
    x ∈ SMulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a := by
  simp only [SMulAntidiagonal, Set.Finite.mem_toFinset]
  exact Set.mem_sep_iff

@[to_additive]
theorem SMulAntidiagonal_mono_left {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : u ⊆ s) :
    SMulAntidiagonal hu ht a ⊆ SMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| SMul.antidiagonal_mono_left h

@[to_additive]
theorem SMulAntidiagonal_mono_right {a : P} {hs : s.IsPWO} {ht : t.IsPWO} (h : v ⊆ t) :
    SMulAntidiagonal hs hv a ⊆ SMulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| SMul.antidiagonal_mono_right h

@[to_additive]
theorem support_SMulAntidiagonal_subset_SMul {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (SMulAntidiagonal hs ht a).Nonempty } ⊆ (s • t) :=
  fun a ⟨b, hb⟩ => by
  rw [mem_SMulAntidiagonal] at hb
  rw [Set.mem_SMul]
  use b.1
  refine { left := hb.1, right := ?_ }
  use b.2
  exact { left := hb.2.1, right := hb.2.2 }

@[to_additive]
theorem isPWO_support_SMulAntidiagonal {hs : s.IsPWO} {ht : t.IsPWO} :
    { a | (SMulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.SMul ht).mono (support_SMulAntidiagonal_subset_SMul)

end

@[to_additive]
theorem SMulAntidiagonal_min_SMul_min [LinearOrder G] [LinearOrder P] [SMul G P]
    [MonoSMulReflectLE G P] {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty)
    (hnt : t.Nonempty) :
    SMulAntidiagonal hs.isPWO ht.isPWO (hs.min hns • ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_SMulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (SMul.smul_lt_smul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, CancelSMul.left_cancel _ _ _ hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

end Finset
