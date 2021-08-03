import Mathlib.Tactic.Basic

-- TODO(Jeremy): where is the best place to put these?
lemma EqIffBeqTrue [DecidableEq α] {a b : α} : a = b ↔ ((a == b) = true) :=
⟨decideEqTrue, ofDecideEqTrue⟩

lemma NeqIffBeqFalse [DecidableEq α] {a b : α} : a ≠ b ↔ ((a == b) = false) :=
⟨decideEqFalse, ofDecideEqFalse⟩

lemma decide_eq_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p :=
⟨ofDecideEqTrue, decideEqTrue⟩

lemma decide_eq_false_iff_not (p : Prop) [Decidable p] : (decide p = false) ↔ ¬ p :=
⟨ofDecideEqFalse, decideEqFalse⟩

lemma optParam_eq (α : Sort u) (default : α) : optParam α default = α := rfl

def not_false := notFalse
def proof_irrel := @proofIrrel
def congr_fun := @congrFun
def congr_arg := @congrArg
def of_eq_true := @ofEqTrue

lemma not_of_eq_false {p : Prop} (h : p = False) : ¬p := fun hp => h ▸ hp

lemma cast_proof_irrel (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

def cast_eq := @castEq

lemma Ne.def (a b : α) : (a ≠ b) = ¬ (a = b) := rfl

def false_of_ne := @falseOfNe
def ne_false_of_self := @neFalseOfSelf
def ne_true_of_not := @neTrueOfNot
def true_ne_false := trueNeFalse
def eq_of_heq := @eqOfHEq
def heq_of_eq := @heqOfEq
def heq_of_heq_of_eq := @heqOfHEqOfEq
def heq_of_eq_of_heq := @heqOfEqOfHEq
def type_eq_of_heq := @typeEqOfHEq
def eq_rec_heq := @eqRecHEq

lemma heq_of_eq_rec_left {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a = a') → (h₂ : Eq.rec (motive := fun a _ => φ a) p₁ e = p₂) → p₁ ≅ p₂
| rfl, rfl => HEq.rfl

lemma heq_of_eq_rec_right {φ : α → Sort v} {a a' : α} {p₁ : φ a} {p₂ : φ a'} :
  (e : a' = a) → (h₂ : p₁ = Eq.rec (motive := fun a _ => φ a) p₂ e) → p₁ ≅ p₂
| rfl, rfl => HEq.rfl

lemma of_heq_true (h : a ≅ True) : a := of_eq_true (eq_of_heq h)

def cast_heq := @castHEq

def And.elim (f : a → b → α) (h : a ∧ b) : α := f h.1 h.2

lemma And.symm : a ∧ b → b ∧ a | ⟨ha, hb⟩ => ⟨hb, ha⟩

lemma Or.elim {a b c : Prop} (h₁ : a → c) (h₂ : b → c) : (h : a ∨ b) → c
| inl ha => h₁ ha
| inr hb => h₂ hb

lemma not_not_em (a : Prop) : ¬¬(a ∨ ¬a) := fun H => H (Or.inr fun h => H (Or.inl h))

lemma Or.symm : a ∨ b → b ∨ a
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

def Iff.elim (f : (a → b) → (b → a) → c) (h : a ↔ b) : c := f h.1 h.2

def Iff.elim_left : (a ↔ b) → a → b := Iff.mp

def Iff.elim_right : (a ↔ b) → b → a := Iff.mpr

lemma iff_comm : (a ↔ b) ↔ (b ↔ a) := ⟨Iff.symm, Iff.symm⟩

lemma iff_iff_implies_and_implies : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  ⟨fun ⟨ha, hb⟩ => ⟨ha, hb⟩, fun ⟨ha, hb⟩ => ⟨ha, hb⟩⟩

lemma Eq.to_iff : a = b → (a ↔ b) | rfl => Iff.rfl

lemma neq_of_not_iff : ¬(a ↔ b) → a ≠ b := mt Eq.to_iff

lemma not_iff_not_of_iff (h₁ : a ↔ b) : ¬ a ↔ ¬ b :=
Iff.intro
  (λ (hna : ¬ a) (hb : b) => hna (Iff.elim_right h₁ hb))
  (λ (hnb : ¬ b) (ha : a) => hnb (Iff.elim_left h₁ ha))

lemma of_iff_true (h : a ↔ True) : a := h.2 ⟨⟩

lemma not_of_iff_false : (a ↔ False) → ¬a := Iff.mp

lemma not_not_intro : a → ¬¬a := fun a h => h a

lemma iff_true_intro (h : a) : a ↔ True := ⟨fun _ => ⟨⟩, fun _ => h⟩

lemma iff_false_intro (h : ¬a) : a ↔ False := ⟨h, fun h => h.elim⟩

lemma not_iff_false_intro (h : a) : ¬a ↔ False := iff_false_intro (not_not_intro h)

lemma not_not_not : ¬¬¬a ↔ ¬a := ⟨mt not_not_intro, not_not_intro⟩

lemma imp_congr_left (h : a ↔ b) : (a → c) ↔ (b → c) :=
⟨fun hac ha => hac (h.2 ha), fun hbc ha => hbc (h.1 ha)⟩

lemma imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
⟨fun hab ha => (h ha).1 (hab ha), fun hcd ha => (h ha).2 (hcd ha)⟩

lemma imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
(imp_congr_left h₁).trans (imp_congr_right h₂)

lemma imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) := imp_congr_ctx h₁ fun _ => h₂

lemma Not.intro {a : Prop} (h : a → False) : ¬a := h

def Not.elim (h : ¬a) (ha : a) : α := absurd ha h

lemma not_true : ¬True ↔ False := not_iff_false_intro ⟨⟩

lemma not_false_iff : ¬False ↔ True := iff_true_intro not_false

lemma not_congr (h : a ↔ b) : ¬a ↔ ¬b := ⟨mt h.2, mt h.1⟩

lemma ne_self_iff_false (a : α) : a ≠ a ↔ False := not_iff_false_intro rfl

lemma eq_self_iff_true (a : α) : a = a ↔ True := iff_true_intro rfl

lemma heq_self_iff_true (a : α) : a ≅ a ↔ True := iff_true_intro HEq.rfl

lemma iff_not_self : ¬(a ↔ ¬a) | H => let f h := H.1 h h; f (H.2 f)

lemma not_iff_self : ¬(¬a ↔ a) | H => iff_not_self H.symm

lemma eq_comm {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩

lemma And.imp (f : a → c) (g : b → d) (h : a ∧ b) : c ∧ d := ⟨f h.1, g h.2⟩

lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := ⟨And.imp h₁.1 h₂.1, And.imp h₁.2 h₂.2⟩

lemma and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
⟨fun ⟨ha, hb⟩ => ⟨ha, (h ha).1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (h ha).2 hb⟩⟩

lemma and_comm : a ∧ b ↔ b ∧ a := ⟨And.symm, And.symm⟩

lemma and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

lemma and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
by rw [← and_assoc, ← and_assoc, @and_comm a b]

lemma and_iff_left (hb : b) : a ∧ b ↔ a := ⟨And.left, fun ha => ⟨ha, hb⟩⟩

lemma and_iff_right (ha : a) : a ∧ b ↔ b := ⟨And.right, fun hb => ⟨ha, hb⟩⟩

lemma and_true : a ∧ True ↔ a := and_iff_left ⟨⟩

lemma true_and : True ∧ a ↔ a := and_iff_right ⟨⟩

lemma and_false : a ∧ False ↔ False := iff_false_intro And.right

lemma false_and : False ∧ a ↔ False := iff_false_intro And.left

lemma and_not_self : ¬(a ∧ ¬a) | ⟨ha, hn⟩ => hn ha
lemma not_and_self : ¬(¬a ∧ a) | ⟨hn, ha⟩ => hn ha

lemma and_self : a ∧ a ↔ a := ⟨And.left, fun h => ⟨h, h⟩⟩

lemma Or.imp (f : a → c) (g : b → d) (h : a ∨ b) : c ∨ d := h.elim (inl ∘ f) (inr ∘ g)

lemma Or.imp_left (f : a → b) : a ∨ c → b ∨ c := Or.imp f id

lemma Or.imp_right (f : b → c) : a ∨ b → a ∨ c := Or.imp id f

lemma or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
⟨Or.imp h₁.1 h₂.1, Or.imp h₁.2 h₂.2⟩

lemma or_comm : a ∨ b ↔ b ∨ a := ⟨Or.symm, Or.symm⟩

lemma Or.resolve_left (h : a ∨ b) (na : ¬a) : b := h.elim na.elim id

lemma Or.neg_resolve_left (h : ¬a ∨ b) (ha : a) : b := h.elim (absurd ha) id

lemma Or.resolve_right (h : a ∨ b) (nb : ¬b) : a := h.elim id nb.elim

lemma Or.neg_resolve_right (h : a ∨ ¬b) (nb : b) : a := h.elim id (absurd nb)

open Or in
lemma or_assoc {a b c} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
⟨fun | inl (inl h) => inl h
     | inl (inr h) => inr (inl h)
     | inr h => inr (inr h),
 fun | inl h => inl (inl h)
     | inr (inl h) => inl (inr h)
     | inr (inr h) => inr h⟩

lemma or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
by rw [← or_assoc, ← or_assoc, @or_comm a b]

lemma or_true : a ∨ True ↔ True := iff_true_intro (Or.inr ⟨⟩)

lemma true_or : True ∨ a ↔ True := iff_true_intro (Or.inl ⟨⟩)

lemma or_false : a ∨ False ↔ a := ⟨fun h => h.resolve_right id, Or.inl⟩

lemma false_or : False ∨ a ↔ a := ⟨fun h => h.resolve_left id, Or.inr⟩

lemma or_self : a ∨ a ↔ a := ⟨fun h => h.elim id id, Or.inl⟩

lemma not_or_intro : (na : ¬a) → (nb : ¬b) → ¬(a ∨ b) := Or.elim

lemma not_or (p q) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨fun H => ⟨mt Or.inl H, mt Or.inr H⟩, fun ⟨hp, hq⟩ pq => pq.elim hp hq⟩

@[simp] lemma iff_true : (a ↔ True) ↔ a := ⟨fun h => h.2 ⟨⟩, iff_true_intro⟩

@[simp] lemma true_iff : (True ↔ a) ↔ a := iff_comm.trans iff_true

@[simp] lemma iff_false : (a ↔ False) ↔ ¬a := ⟨Iff.mp, iff_false_intro⟩

@[simp] lemma false_iff : (False ↔ a) ↔ ¬a := iff_comm.trans iff_false

@[simp] lemma iff_self : (a ↔ a) ↔ True := iff_true_intro Iff.rfl

lemma iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
⟨fun h => h₁.symm.trans $ h.trans h₂, fun h => h₁.trans $ h.trans h₂.symm⟩

@[simp] lemma imp_true_iff : (α → True) ↔ True := iff_true_intro fun _ => ⟨⟩

@[simp] lemma false_imp_iff : (False → a) ↔ True := iff_true_intro False.elim

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

lemma ExistsUnique.intro {p : α → Prop} (w : α)
  (h₁ : p w) (h₂ : ∀ y, p y → y = w) : ∃! x, p x := ⟨w, h₁, h₂⟩

lemma ExistsUnique.exists {p : α → Prop} : (∃! x, p x) → ∃ x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

lemma ExistsUnique.unique {p : α → Prop} (h : ∃! x, p x)
  {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
let ⟨x, hx, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

lemma forall_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a :=
⟨fun H a => (h a).1 (H a), fun H a => (h a).2 (H a)⟩

lemma Exists.imp {p q : α → Prop} (h : ∀ a, p a → q a) : (∃ a, p a) → ∃ a, q a
| ⟨a, ha⟩ => ⟨a, h a ha⟩

lemma exists_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃ a, p a) ↔ ∃ a, q a :=
⟨Exists.imp fun x => (h x).1, Exists.imp fun x => (h x).2⟩

lemma exists_unique_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∃! a, p a) ↔ ∃! a, q a :=
exists_congr fun x => and_congr (h _) $ forall_congr fun y => imp_congr_left (h _)

lemma forall_not_of_not_exists {p : α → Prop} (hne : ¬∃ x, p x) (x) : ¬p x | hp => hne ⟨x, hp⟩

instance forall_prop_decidable {p} (P : p → Prop)
  [Dp : Decidable p] [DP : ∀ h, Decidable (P h)] : Decidable (∀ h, P h) :=
  if h : p
  then decidableOfDecidableOfIff (DP h) ⟨λ h2 _ => h2, λ al => al h⟩
  else isTrue (λ h2 => absurd h2 h)

@[simp] theorem forall_eq {p : α → Prop} {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨λ h => h a' rfl, λ h a e => e.symm ▸ h⟩

theorem forall_and_distrib {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h => ⟨λ x => (h x).left, λ x => (h x).right⟩, λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩⟩

def Decidable.by_cases := @byCases
def Decidable.by_contradiction := @byContradiction
def Decidable.of_not_not := @ofNotNot

lemma Decidable.not_and [Decidable p] [Decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q := notAndIffOrNot _ _

def decidable_of_decidable_of_iff {p q : Prop} (hp : Decidable p) (h : p ↔ q) : Decidable q :=
if hp : p then isTrue (Iff.mp h hp)
else isFalse (Iff.mp (not_iff_not_of_iff h) hp)

@[inline] def Or.by_cases [Decidable p] (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
if hp : p then h₁ hp else h₂ (h.resolve_left hp)

@[inline] def Or.by_cases' [Decidable q] (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
if hq : q then h₂ hq else h₁ (h.resolve_right hq)

lemma Exists.nonempty {p : α → Prop} : (∃ x, p x) → Nonempty α | ⟨x, _⟩ => ⟨x⟩

@[simp] def if_pos := @ifPos
@[simp] def if_neg := @ifNeg
@[simp] def dif_pos := @difPos
@[simp] def dif_neg := @difNeg

lemma ite_id [h : Decidable c] {α} (t : α) : (if c then t else t) = t := by cases h <;> rfl

@[simp] lemma if_true {h : Decidable True} (t e : α) : (@ite α True h t e) = t :=
if_pos trivial

@[simp] lemma if_false {h : Decidable False} (t e : α) : (@ite α False h t e) = e :=
if_neg not_false

lemma dif_eq_if [h : Decidable c] {α} (t : α) (e : α) : (if h : c then t else e) = ite c t e :=
by cases h <;> rfl

/-- Universe lifting operation -/
structure ulift.{r, s} (α : Type s) : Type (max s r) :=
up :: (down : α)

namespace ulift
/- Bijection between α and ulift.{v} α -/
lemma up_down {α : Type u} : ∀ (b : ulift.{v} α), up (down b) = b
| up a => rfl

lemma down_up {α : Type u} (a : α) : down (up.{v} a) = a := rfl
end ulift

/-- Universe lifting operation from Sort to Type -/
structure plift (α : Sort u) : Type u :=
up :: (down : α)

namespace plift
/- Bijection between α and plift α -/
lemma up_down : ∀ (b : plift α), up (down b) = b
| (up a) => rfl

lemma down_up (a : α) : down (up a) = a := rfl
end plift

namespace WellFounded

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end WellFounded

-- Below are items ported from mathlib/src/logic/basic.lean

theorem iff_of_eq (e : a = b) : a ↔ b := e ▸ Iff.rfl

def decidable_of_iff (a : Prop) (h : a ↔ b) [D : Decidable a] : Decidable b :=
decidableOfDecidableOfIff D h

/-
Stuff from mathlib's logic/basic.lean.
TODO: import the whole thing.
-/

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
  fun ⟨ha, hb⟩ => Or.rec ha hb⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
Iff.intro (λ h ha hb => h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩ => h ha hb)

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

section equality

variable {α : Sort _} {a b : α}

@[simp] theorem heq_iff_eq : HEq a b ↔ a = b :=
⟨eq_of_heq, heq_of_eq⟩

@[simp] lemma eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
  (@Eq.rec α a (λ α _ => β) y a' h) = y :=
by cases h
   exact rfl

lemma congr_arg2 {α β γ : Type _} (f : α → β → γ) {x x' : α} {y y' : β}
  (hx : x = x') (hy : y = y') : f x y = f x' y' :=
by subst hx
   subst hy
   exact rfl

end equality

@[simp] theorem forall_const (α : Sort _) [i : Nonempty α] : (α → b) ↔ b :=
⟨i.elim, λ hb x => hb⟩

@[simp] theorem exists_imp_distrib {p : α → Prop} : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
⟨λ h x hpx => h ⟨x, hpx⟩, λ h ⟨x, hpx⟩ => h x hpx⟩

@[simp] theorem exists_false : ¬ (∃a:α, False) := fun ⟨a, h⟩ => h

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨λ ⟨x, hq, hp⟩ => ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩ => ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp [and_comm]

@[simp] theorem exists_eq {a' : α} : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' {a' : α} : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_eq_left {p : α → Prop} {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨a, e, h⟩ => e ▸ h, λ h => ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {p : α → Prop} {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a => and_comm).trans exists_eq_left

@[simp] theorem exists_eq_left' {p : α → Prop} {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_apply_eq_apply {α β : Type _} (f : α → β) (a' : α) : ∃ a, f a = f a' :=
⟨a', rfl⟩

protected theorem decidable.not_imp_symm [Decidable a] (h : ¬a → b) (hb : ¬b) : a :=
Decidable.by_contradiction $ hb ∘ h

theorem not.decidable_imp_symm [Decidable a] : (¬a → b) → ¬b → a := decidable.not_imp_symm

theorem not_forall_of_exists_not {p : α → Prop} : (∃ x, ¬ p x) → ¬ ∀ x, p x
| ⟨x, hn⟩, h => hn (h x)

protected theorem Decidable.not_forall {p : α → Prop}
  [Decidable (∃ x, ¬ p x)] [∀ x, Decidable (p x)] : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨not.decidable_imp_symm $ λ nx x => not.decidable_imp_symm (λ h => ⟨x, h⟩) nx,
 not_forall_of_exists_not⟩

@[simp] theorem not_exists {p : α → Prop} : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
@forall_const (q h) p ⟨h⟩

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
lemma apply_dite {α β : Sort _} (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬ P → α) :
  f (dite P x y) = dite P (λ h => f (x h)) (λ h => f (y h)) :=
by by_cases h : P <;> simp[h]

/-- A function applied to a `int` is a `ite` of that function applied to each of the branches. -/
lemma apply_ite {α β : Sort _} (f : α → β) (P : Prop) [Decidable P] (x y : α) :
  f (ite P x y) = ite P (f x) (f y) :=
apply_dite f P (λ _ => x) (λ _ => y)

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] lemma dite_not {α : Sort _} (P : Prop) [Decidable P]  (x : ¬ P → α) (y : ¬¬ P → α) :
  dite (¬ P) x y = dite P (λ h => y (not_not_intro h)) x :=
by by_cases h : P <;> simp[h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] lemma ite_not {α : Sort _} (P : Prop) [Decidable P] (x y : α) :
 ite (¬ P) x y = ite P y x :=
dite_not P (λ _ => x) (λ _ => y)

open Classical

@[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x := Decidable.not_forall
