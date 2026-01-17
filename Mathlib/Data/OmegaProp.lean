module

import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Quot
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Semi-Computable Propositions

This file defines `ΩProp`, the type of _semi-computable propositions_. It is classically equivalent
to `Bool` and `Prop`, but supports some operations which are not computable with the other types.
Operationally, an `p : ΩProp` is a sequence of booleans such that `p` is "true" iff at least one
boolean in the sequence is `true`.

# Main Declarations

* `ΩProp.true`, `ΩProp.false`: Analogues of `True` and `False`.
* `ΩProp.and`, `ΩProp.or`: Analogues of `∧` and `∨`.
* `ΩProp.bind`: Dependent conjunction (`ΩProp.bind p q ↔ ∃h : p, q h`).
* `ΩProp.any`: Existential quantification over `ℕ`.
  This is also the implementation of `OmegaCompletePartialOrder.ωSup`.
* `ΩProp.find`: Computes a `Squash`ed witness (of type `ℕ`) from an `ΩProp.any` proof.
-/

public section

private def ΩProp.setoid : Setoid (ℕ → Bool) where
  r p q := (∃n, p n) ↔ (∃n, q n)
  iseqv := by constructor <;> grind

/-- The type of semi-decidable propositions. -/
structure ΩProp : Type where
  private mk' ::
  private get : Quotient ΩProp.setoid

namespace ΩProp

/-- Given a sequence `p : ℕ → Bool`, the proposition
`mk p` is `true` iff `p n = true` for some `n`. -/
def mk (p : ℕ → Bool) : ΩProp where
  get := ⟦p⟧

@[simp]
lemma mk_eq_iff {p₁ p₂} : mk p₁ = mk p₂ ↔ ((∃ n, p₁ n) ↔ (∃ n, p₂ n)) := by
  apply Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)
  · simp only [mk, mk'.injEq, Quotient.eq_iff_equiv] at h
    exact h
  · unfold mk
    simp only [mk'.injEq]
    apply Quotient.sound h

@[elab_as_elim, induction_eliminator]
lemma induction {p : ΩProp → Prop} (mk : ∀ f, p (mk f)) (a : ΩProp) : p a := by
  rcases a with ⟨a⟩
  cases a using Quotient.ind with | _ q =>
  apply mk

@[elab_as_elim]
lemma inductionPi
    {p : (ℕ → ΩProp) → Prop}
    (mk : ∀ f : ℕ → ℕ → Bool, p fun n ↦ mk (f n))
    (c : ℕ → ΩProp) : p c := by
  have : c = fun n ↦ ⟨⟦(c n).get.out⟧⟩ := by
    ext n
    rw [Quotient.out_eq]
  rw [this]
  apply mk

/-- Dependent elimination by applying a function to the underlying sequence. -/
@[elab_as_elim]
def elim
    {P : ΩProp → Type*} (mk : (p : ℕ → Bool) → P (mk p))
    (mk_coe : ∀ (p₁ p₂ : ℕ → Bool) (h : (∃ n, p₁ n) ↔ (∃ n, p₂ n)), mk_eq_iff.2 h ▸ mk p₁ = mk p₂)
    (a : ΩProp) : P a :=
  Quotient.recOn (motive := fun a ↦ P ⟨a⟩) a.get mk fun p₁ p₂ h ↦ by
    simp only [eqRec_eq_cast] at ⊢ mk_coe
    apply mk_coe
    apply h

@[simp]
lemma elim_mk
    {P : ΩProp → Type*} (mk : (p : ℕ → Bool) → P (mk p))
    (mk_coe : ∀ (p₁ p₂ : ℕ → Bool) (h : (∃ n, p₁ n) ↔ (∃ n, p₂ n)), mk_eq_iff.2 h ▸ mk p₁ = mk p₂)
    (a : ℕ → Bool) : elim mk mk_coe (.mk a) = mk a := by
  rfl

/-- Dependent elimination of a sequence of `ΩProp`s into a subsingleton. -/
@[elab_as_elim]
def elimPiSubsingleton
    {P : (ℕ → ΩProp) → Type*} [∀ p, Subsingleton (P p)]
    (mk : (p : ℕ → ℕ → Bool) → P (fun n ↦ mk (p n)))
    (a : ℕ → ΩProp) : P a :=
  let x := Quotient.recOnSubsingleton
    (motive := fun a ↦ P fun n ↦ ⟨a.eval n⟩)
    (Quotient.countableChoice fun i ↦ (a i).get)
    mk
  cast
    (by dsimp only
        congr 1
        ext n
        rw [Quotient.eval_countableChoice])
    x

@[simp]
lemma elimPiSubsingleton_mk
    {P : (ℕ → ΩProp) → Type*} [∀ p, Subsingleton (P p)]
    (mk : (p : ℕ → ℕ → Bool) → P (fun n ↦ mk (p n)))
    (a : ℕ → ℕ → Bool) : elimPiSubsingleton mk (fun n ↦ .mk (a n)) = mk a := by
  subsingleton

/-- Dependent elimination of a sequence of `ΩProp`s into a subsingleton. -/
@[elab_as_elim]
def elimOnPiSubsingleton
    {P : (ℕ → ΩProp) → Type*} [∀ p, Subsingleton (P p)]
    (a : ℕ → ΩProp)
    (mk : (p : ℕ → ℕ → Bool) → P (fun n ↦ mk (p n)))
    : P a :=
  elimPiSubsingleton mk a

@[simp]
lemma elimOnPiSubsingleton_mk
    {P : (ℕ → ΩProp) → Type*} [∀ p, Subsingleton (P p)]
    (mk : (p : ℕ → ℕ → Bool) → P (fun n ↦ mk (p n)))
    (a : ℕ → ℕ → Bool) : elimOnPiSubsingleton (fun n ↦ .mk (a n)) mk = mk a := by
  subsingleton

/-- Lifts a function on the underlying sequence to a function on `ΩProp`,
requiring that it respects the quotient's equivalence relation.
-/
def lift
    {A : Type*} (mk : (ℕ → Bool) → A)
    (mk_coe : ∀ p₁ p₂, ((∃ n, p₁ n) ↔ (∃ n, p₂ n)) → mk p₁ = mk p₂)
    (a : ΩProp) : A :=
  a.get.lift mk mk_coe

@[simp]
lemma lift_mk {A f} (hf p) : lift (A := A) f hf (mk p) = f p := by
  rfl

/-- Like `lift`, but for two argument functions. -/
def lift₂
    {A : Type*} (mk : (ℕ → Bool) → (ℕ → Bool) → A)
    (mk_coe :
      ∀ p₁ p₂, ((∃ n, p₁ n) ↔ (∃ n, p₂ n)) →
      ∀ q₁ q₂, ((∃ n, q₁ n) ↔ (∃ n, q₂ n)) →
        mk p₁ q₁ = mk p₂ q₂)
    (a b : ΩProp) : A :=
  lift
    (fun f ↦ lift (mk f) (by grind) b)
    (by intro p₁ p₂ hp
        induction b
        grind [lift_mk])
    a

@[simp]
lemma lift₂_mk
    {A : Type*} (mk : (ℕ → Bool) → (ℕ → Bool) → A)
    (mk_coe :
      ∀ p₁ p₂, ((∃ n, p₁ n) ↔ (∃ n, p₂ n)) →
      ∀ q₁ q₂, ((∃ n, q₁ n) ↔ (∃ n, q₂ n)) →
        mk p₁ q₁ = mk p₂ q₂)
    (p q) : lift₂ mk mk_coe (.mk p) (.mk q) = mk p q := by
  rfl

/-- Like `lift`, but for `ℕ`-ary functions. -/
def liftPi
    {A : Type*} (mk : (ℕ → ℕ → Bool) → A)
    (mk_coe : ∀ p q, (∀ i, (∃ n, p i n) ↔ (∃ n, q i n)) → mk p = mk q)
    (a : ℕ → ΩProp) : A :=
  Quotient.liftOn (Quotient.countableChoice fun i ↦ (a i).get)
    mk
    mk_coe

@[simp]
lemma liftPi_mk
    {A : Type*} (mk : (ℕ → ℕ → Bool) → A)
    (mk_coe : ∀ p q, (∀ i, (∃ n, p i n) ↔ (∃ n, q i n)) → mk p = mk q)
    (a : ℕ → ℕ → Bool) : liftPi mk mk_coe (fun n ↦ .mk (a n)) = mk a := by
  dsimp only [liftPi, ΩProp.mk]
  rw [Quotient.countableChoice_eq]
  rfl

/-- The `ΩProp` analogue to the proposition `True`. -/
def true : ΩProp := mk fun _ ↦ .true

/-- The `ΩProp` analogue to the proposition `False`. -/
def false : ΩProp := mk fun _ ↦ .false

@[simp]
lemma false_ne_true : false ≠ true := by
  simp only [
    false, true, ne_eq, mk_eq_iff, Bool.false_eq_true,
    exists_const, iff_true, not_false_eq_true]

@[simp]
lemma true_ne_false : true ≠ false := by
  symm
  simp only [ne_eq, false_ne_true, not_false_eq_true]

@[elab_as_elim, cases_eliminator]
lemma cases {p : ΩProp → Prop} (true : p true) (false : p false) (a : ΩProp) : p a := by
  induction a with | mk q =>
  by_cases h : ∃n, q n
  · have : mk q = ΩProp.true := by
      simp only [ΩProp.true, mk_eq_iff, h, exists_const]
    simp only [this, true]
  · have : mk q = ΩProp.false := by
      simp only [ΩProp.false, mk_eq_iff, h, Bool.false_eq_true, exists_const]
    simp only [this, false]

/-- An `ΩProp` may be treated as a normal `Prop`. -/
@[coe]
def coe := (· = true)

instance : CoeSort ΩProp Prop where
  coe := coe

@[simp]
lemma coe_true : true ↔ _root_.True := by
  simp only [coe]

@[simp]
lemma coe_false : false ↔ _root_.False := by
  simp only [coe, false_ne_true]

@[simp]
lemma coe_mk {p} : mk p ↔ ∃n, p n := by
  simp only [coe, true, mk_eq_iff, exists_const, iff_true]

@[ext]
lemma ext {a b : ΩProp} (h : a ↔ b) : a = b := by
  cases a
  · cases b
    · simp only
    · simp only [coe_true, coe_false, iff_false, not_true_eq_false] at h
  · cases b
    · simp only [coe_false, coe_true, iff_true] at h
    · simp only

@[simp]
lemma eq_true_iff_coe (a) : a = true ↔ a := by rfl

@[simp]
lemma eq_false_iff_not_coe (a) : a = false ↔ ¬a := by
  cases a
  · simp only [true_ne_false, coe_true, not_true_eq_false]
  · simp only [coe_false, not_false_eq_true]

@[simp]
lemma neg_eq_true (a) : ¬a = true ↔ a = false := by
  cases a
  · simp only [not_true_eq_false, true_ne_false]
  · simp only [false_ne_true, not_false_eq_true]

@[simp]
lemma neg_eq_false (a) : ¬a = false ↔ a = true := by
  cases a
  · simp only [true_ne_false, not_false_eq_true]
  · simp only [not_true_eq_false, false_ne_true]

/-- The disjunction of a countable number of `ΩProp`s. -/
def any : (ℕ → ΩProp) → ΩProp :=
  liftPi (fun p ↦ mk fun n ↦ p n.unpair.1 n.unpair.2) (by
    intro p q hpq
    simp only [mk_eq_iff]
    apply Iff.intro
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hpq n.unpair.1).1 ⟨n.unpair.2, hn⟩
      use Nat.pair n.unpair.1 m
      simp only [Nat.unpair_pair, hm]
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hpq n.unpair.1).2 ⟨n.unpair.2, hn⟩
      use Nat.pair n.unpair.1 m
      simp only [Nat.unpair_pair, hm])

@[simp]
lemma coe_any {c : ℕ → ΩProp} : any c ↔ ∃n, c n := by
  induction c using inductionPi with | mk p =>
  simp only [coe, any, liftPi_mk, true, mk_eq_iff, exists_const, iff_true]
  apply Iff.intro
  · grind
  · rintro ⟨n, m, h⟩
    use Nat.pair n m
    simp only [Nat.unpair_pair, h]

@[simp]
lemma any_const (a) : any (fun _ ↦ a) = a := by
  ext
  simp only [coe_any, exists_const]

/-- The disjunction of two `ΩProp`s. -/
def or (a b : ΩProp) : ΩProp := any fun
  | 0 => a
  | _ => b

@[simp]
lemma coe_or (a b : ΩProp) : or a b ↔ a ∨ b := by
  simp only [or, coe_any]
  apply Iff.intro
  · rintro ⟨⟨_|n⟩, hn⟩ <;> grind
  · rintro ⟨rfl|rfl⟩
    · use 0
      simp only [coe_true]
    · use 1

@[simp]
lemma true_or (a : ΩProp) : or true a = true := by
  ext
  simp only [coe_or, coe_true, _root_.true_or]

@[simp]
lemma false_or (a : ΩProp) : or false a = a := by
  ext
  simp only [coe_or, coe_false, _root_.false_or]

@[simp]
lemma or_true (a : ΩProp) : or a true = true := by
  ext
  simp only [coe_or, coe_true, _root_.or_true]

@[simp]
lemma or_false (a : ΩProp) : or a false = a := by
  ext
  simp only [coe_or, coe_false, _root_.or_false]

@[simp]
lemma or_self (a : ΩProp) : or a a = a := by
  ext
  simp only [coe_or, _root_.or_self]

/-- If `ΩProp.any p` holds, then `p n` holds for some `n`.
The function `find` computes such an `n`.

Note that we cannot know _which_ `n` it is because `any p` is
equal to `any q` for any `q : ℕ → Bool` satisfying `∃m, q m = true`.
Hence the return type of this function must be `Squash`ed. -/
def find {p : ℕ → ΩProp} : ↑(any p) → Squash { n // p n } :=
  elimOnPiSubsingleton p fun p hp ↦ by
    simp only [coe_any, coe_mk] at hp
    have : ∃n : ℕ, p n.unpair.1 n.unpair.2 := by
      rcases hp with ⟨m, n, h⟩
      use Nat.pair m n
      simp only [Nat.unpair_pair, h]
    apply Squash.mk
    use (Nat.find this).unpair.1
    simp only [coe_mk]
    use (Nat.find this).unpair.2
    exact Nat.find_spec this

@[simps -isSimp]
instance : OmegaCompletePartialOrder ΩProp where
  le a b := a → b
  le_refl a := by grind
  le_trans a b c h₁ h₂ := by grind
  le_antisymm a b h₁ h₂ := by ext; grind
  ωSup c := any c
  le_ωSup c i h := by
    simp only [coe_any]
    use i
  ωSup_le c a h₁ h₂ := by
    simp only [coe_any] at h₂
    grind

@[simp]
lemma false_le (a : ΩProp) : false ≤ a := by
  simp only [le_def, coe_false, IsEmpty.forall_iff]

@[simp]
lemma le_false (a : ΩProp) : a ≤ false ↔ ¬a := by
  simp only [le_def, coe_false, imp_false]

@[simp]
lemma true_le (a : ΩProp) : true ≤ a ↔ a := by
  simp only [le_def, coe_true, forall_const]

@[simp]
lemma le_true (a : ΩProp) : a ≤ true := by
  simp only [le_def, coe_true, implies_true]

private lemma bind_helper
    {A B : Type*} {P : A → Sort*} {a b} (f : P a → B) (h : a = b)
    : Eq.rec (motive := fun a _ ↦ P a → B) f h
    = fun x ↦ f (h ▸ x) := by
  induction h
  rfl

/-- The dependent conjunction of `ΩProp`s. -/
def bind : (a : ΩProp) → (a → ΩProp) → ΩProp :=
  elim
    (fun p f ↦ any fun n ↦
      if h : p n
      then f (by simp only [coe_mk]; use n)
      else false)
    (by intro p₁ p₂ h
        have hp : mk p₁ = mk p₂ := by simp only [mk_eq_iff, h]
        rw [bind_helper (P := fun a : ΩProp ↦ a → ΩProp)]
        ext f
        simp only [coe_any]
        apply Iff.intro
        · simp only [forall_exists_index]
          intro n hn
          cases hp₁ : p₁ n with
          | false => simp only [hp₁, Bool.false_eq_true, ↓reduceDIte, coe_false] at hn
          | true =>
            simp only [hp₁, ↓reduceDIte] at hn
            obtain ⟨m, hm⟩ := h.1 (by grind)
            use m
            simp only [hm, ↓reduceDIte]
            rw [bind_helper] at hn
            exact hn
        · simp only [forall_exists_index]
          intro n hn
          cases hp₂ : p₂ n with
          | false => simp only [hp₂, Bool.false_eq_true, ↓reduceDIte, coe_false] at hn
          | true =>
            simp only [hp₂, ↓reduceDIte] at hn
            obtain ⟨m, hm⟩ := h.2 (by grind)
            use m
            simp only [hm, ↓reduceDIte]
            rw [bind_helper]
            exact hn)

@[simp]
lemma coe_bind
    (a : ΩProp) (f : a → ΩProp)
    : bind a f ↔ ∃h : a, f h := by
  induction a with | mk p =>
  simp only [bind, elim_mk, coe_any, coe_mk]
  apply Iff.intro
  · rintro ⟨n, hn⟩
    cases hp : p n with
    | true =>
      simp only [hp, ↓reduceDIte] at hn
      use ⟨n, hp⟩
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceDIte, coe_false] at hn
  · rintro ⟨⟨n, hn⟩, hp⟩
    use n
    simp only [hn, ↓reduceDIte, hp]

@[simp]
lemma true_bind (f : true → ΩProp) : bind true f = f (by simp only [coe_true]) := by
  ext
  simp only [coe_bind, coe_true, exists_true_left]

@[simp]
lemma false_bind (f : false → ΩProp) : bind false f = false := by
  ext
  simp only [coe_bind, coe_false, IsEmpty.exists_iff]

/-- The conjunction of two `ΩProp`s. -/
def and (a b : ΩProp) : ΩProp := bind a fun _ ↦ b

@[simp]
lemma bind_const (a b : ΩProp) : bind a (fun _ ↦ b) = and a b := by rfl

@[simp]
lemma coe_and {a b} : and a b ↔ a ∧ b := by
  simp only [← bind_const, coe_bind, exists_prop]

@[simp]
lemma and_true (a : ΩProp) : and a true = a := by
  ext
  simp only [coe_and, coe_true, _root_.and_true]

@[simp]
lemma and_false (a : ΩProp) : and a false = false := by
  ext
  simp only [coe_and, coe_false, _root_.and_false]

@[simp]
lemma true_and (a : ΩProp) : and true a = a := by
  ext
  simp only [coe_and, coe_true, _root_.true_and]

@[simp]
lemma false_and (a : ΩProp) : and false a = false := by
  ext
  simp only [coe_and, coe_false, _root_.false_and]

@[simp]
lemma and_self (a : ΩProp) : and a a = a := by
  ext
  simp only [coe_and, _root_.and_self]

open OmegaCompletePartialOrder

def Chain.true (n : ℕ) : Chain ΩProp where
  toFun k := if k < n then .false else .true
  monotone' _ _ _ := by
    dsimp only
    split_ifs <;> grind [le_true]

@[simp]
lemma Chain.true_coe (k n) : true n k = if k < n then .false else .true := by rfl

def Chain.false : Chain ΩProp where
  toFun _ := .false
  monotone' _ _ _ := by simp only [le_refl]

@[simp]
lemma Chain.false_coe (n) : false n = .false := by rfl

@[elab_as_elim]
lemma Chain.cases
    {p : Chain ΩProp → Prop}
    (true : ∀ n, p (true n))
    (false : p false)
    (c) : p c := by
  classical
  by_cases h : ∃n, c n
  · have : c = Chain.true (Nat.find h) := by
      ext n
      simp only [true_coe, Nat.lt_find_iff]
      split_ifs with h'
      · simp only [le_refl, h', coe_false]
      · simp only [not_forall, Decidable.not_not] at h'
        rcases h' with ⟨m, hn, hm⟩
        have := c.monotone hn
        simp only [coe_true, iff_true]
        apply this hm
    rw [this]
    apply true
  · have : c = Chain.false := by
      ext n
      simp only [not_exists, false_coe, coe_false, iff_false] at ⊢ h
      apply h
    simp only [this, false]

@[simp]
lemma ωSup_true (n) : ωSup (Chain.true n) = true := by
  apply le_antisymm
  · simp only [ωSup_le_iff, Chain.true_coe, le_true, implies_true]
  · simp only [ωSup, true_le, coe_any, Chain.true_coe]
    use n + 1
    simp only [(by grind : ¬n + 1 < n), ↓reduceIte, coe_true]

@[simp]
lemma ωSup_false : ωSup Chain.false = false := by
  apply le_antisymm
  · simp only [ωSup_le_iff, Chain.false_coe, le_refl, implies_true]
  · simp only [false_le]

@[simp, fun_prop]
lemma ωScottContinuous_and : ωScottContinuous fun x : ΩProp × ΩProp ↦ and x.1 x.2 := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c ↦ ?_⟩
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp only [Prod.mk_le_mk] at ⊢ h
    cases a₁
    · cases b₁
      · simpa only [and_self, true_le, coe_and] using h
      · simp only [and_false, false_le]
    · cases b₁
      · simp only [and_true, false_le]
      · simp only [and_self, false_le]
  · simp only [Prod.ωSup_fst, Prod.ωSup_snd]
    generalize h₁ : c.map OrderHom.fst = c₁
    generalize h₂ : c.map OrderHom.snd = c₂
    have : c = Chain.zip c₁ c₂ := by
      simp only [← h₁, ← h₂]
      rfl
    simp only [this]
    cases c₁ using Chain.cases with
    | true n =>
      simp only [ωSup_true, true_and]
      apply le_antisymm
      · simp only [ωSup_le_iff]
        intro i
        apply le_ωSup_of_le (i ⊔ n)
        simp only [
          Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, Chain.zip_coe, Chain.true_coe,
          sup_lt_iff, lt_self_iff_false, _root_.and_false, ↓reduceIte, true_and]
        apply c₂.monotone
        grind
      · simp only [
          ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk,
          Function.comp_apply, Chain.zip_coe, Chain.true_coe]
        intro i
        split_ifs
        · simp only [false_and, false_le]
        · simp only [true_and]
          apply le_ωSup
    | false =>
      simp only [ωSup_false, false_and]
      apply le_antisymm
      · simp only [false_le]
      · simp only [
          ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
          Chain.zip_coe, Chain.false_coe, false_and, le_refl, implies_true]

@[simp, fun_prop]
lemma ωScottContinuous_any
    {α : Type*} [OmegaCompletePartialOrder α]
    {f : α → ℕ → ΩProp} (hf : ∀ n, ωScottContinuous (f · n))
    : ωScottContinuous fun x ↦ any (f x) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c ↦ ?_⟩
  · intro x y h₁ h₂
    simp only [coe_any] at ⊢ h₂
    rcases h₂ with ⟨n, h₂⟩
    exact ⟨n, (hf n).monotone h₁ h₂⟩
  · ext
    simp only [
      coe_any, (hf _).map_ωSup c, ωSup_def, Chain.map_coe,
      OrderHom.coe_mk, Function.comp_apply]
    grind

@[simp, fun_prop]
lemma ωScottContinuous_or : ωScottContinuous fun x : ΩProp × ΩProp ↦ or x.1 x.2 := by
  apply ωScottContinuous_any fun n ↦ ?_
  cases n <;> fun_prop

@[simp, fun_prop]
lemma ωScottContinuous_coe : ωScottContinuous fun a : ΩProp ↦ (a : Prop) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c ↦ ?_⟩
  · intro a₁ a₂ h
    exact h
  · simp only [ωSup, coe_any, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, iSup_Prop_eq]

end ΩProp
