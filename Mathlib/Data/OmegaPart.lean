module

public import Mathlib.Data.OmegaProp
public import Mathlib.Control.LawfulFix

/-!
# Semi-Computable Optional Values

This file defines `ΩPart α`, the type of _semi-computable values_. It is classically equivalent
to `Option`, but supports a different set of operations without giving up computability.
`ΩPart α` behaves the same as `Option α` except that `o : Option α` is decidably none or some a for
some `a : α`, while the domain of `o : Part α` need only be semi-decidable.

# Main Declarations

* `ΩPart.none`: The partial value whose domain is `ΩProp.false`.
* `ΩPart.some a`: The partial value whose domain is `ΩProp.true` and whose value is `a`.
* `ΩPart.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* A computable `OmegaCompletePartialOrder` instance.
* `ΩPart.unwrap`: Gets the value of a partial value regardless of its domain. Logically unsound, but
  operationally sound (i.e., it will throw an error or not terminate if the value does not exist.)
-/

public section

/-- Semi-computable optional values. -/
structure ΩPart (A : Type*) where
  Dom : ΩProp
  get : Dom → A

namespace ΩPart

variable {A B C : Type*}

instance : Membership A (ΩPart A) where
  mem x a := ∃d, a = x.get d

@[simp]
lemma mem_mk (a : A) (Dom : ΩProp) (get : Dom → A) : a ∈ mk Dom get ↔ ∃h, a = get h := by
  rfl

@[simp]
lemma mem_get {x : ΩPart A} (h : x.Dom) : x.get h ∈ x := by
  simp only [Membership.mem, exists_prop, and_true, h]

@[ext]
lemma ext {x y : ΩPart A} (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have : x₁ = y₁ := by
    ext
    cases x₁
    · specialize h (x₂ (by simp only [ΩProp.coe_true]))
      simp only [mem_mk, ΩProp.coe_true, exists_const, true_iff] at h
      grind
    · simpa only [
        ΩProp.coe_false, false_iff, mem_mk, IsEmpty.exists_iff,
        not_exists, forall_eq_apply_imp_iff, imp_false] using h
  subst this
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext h'
  simp only [mem_mk, h', exists_true_left, eq_iff_eq_cancel_left] at h
  exact h

@[grind →]
lemma mem_unique {a b} {x : ΩPart A} (h₁ : a ∈ x) (h₂ : b ∈ x) : a = b := by
  simp only [Membership.mem] at h₁ h₂
  grind

/-- An empty optional value. Corresponds to non-termination. -/
@[simps, expose]
def none : ΩPart A where
  Dom := .false
  get h := by simp only [ΩProp.coe_false] at h

@[simp]
lemma mem_none {a : A} : a ∉ none := by
  simp only [Membership.mem, none, ΩProp.coe_false, IsEmpty.exists_iff, not_false_eq_true]

/-- A present optional value. -/
@[simps, expose]
def some (a : A) : ΩPart A where
  Dom := .true
  get _ := a

@[simp]
lemma mem_some {a b : A} : a ∈ some b ↔ a = b := by
  simp only [Membership.mem, some, ΩProp.coe_true, exists_const]

@[elab_as_elim, cases_eliminator]
lemma cases {p : ΩPart A → Prop} (none : p none) (some : ∀ x, p (some x)) (x) : p x := by
  rcases x with ⟨Dom, get⟩
  cases Dom with
  | true =>
    change p ⟨.true, fun _ ↦ get (by simp only [ΩProp.coe_true])⟩
    apply some
  | false =>
    have : get = fun h ↦ by simp only [ΩProp.coe_false] at h := by
      ext h
      simp only [ΩProp.coe_false] at h
    simp only [this]
    apply none

/-- Monadic bind for optional values. -/
def bind (f : A → ΩPart B) (x : ΩPart A) : ΩPart B where
  Dom := x.Dom.bind fun h ↦ (f (x.get h)).Dom
  get h :=
    have : ∃h' : x.Dom, (f (x.get h')).Dom := by
      simpa only [ΩProp.coe_bind] using h
    (f (x.get this.choose)).get this.choose_spec

@[simp]
lemma mem_bind (f : A → ΩPart B) (x : ΩPart A) (b : B) : b ∈ bind f x ↔ ∃a ∈ x, b ∈ f a := by
  simp only [Membership.mem, bind, ΩProp.coe_bind, ↓existsAndEq, true_and]
  apply Iff.intro
  · grind
  · rintro ⟨h₁, h₂, rfl⟩
    grind

@[simp]
lemma bind_none (f : A → ΩPart B) : bind f none = none := by
  ext
  simp only [mem_bind, mem_none, false_and, exists_false]

@[simp]
lemma none_bind : bind (fun _ ↦ none) = fun _ : ΩPart A ↦ (none : ΩPart B) := by
  ext
  simp only [mem_bind, mem_none, and_false, exists_false]

@[simp]
lemma some_bind : bind (some (A := A)) = id := by
  ext
  simp only [mem_bind, mem_some, exists_eq_right', id_eq]

@[simp]
lemma bind_some (f : A → ΩPart B) (x : A) : bind f (some x) = f x := by
  ext
  simp only [mem_bind, mem_some, exists_eq_left]

lemma bind_bind
    (f : B → ΩPart C) (g : A → ΩPart B) (x : ΩPart A)
    : bind f (bind g x) = bind (bind f ∘ g) x := by
  ext
  simp only [mem_bind, Function.comp_apply]
  grind

@[simps -isSimp]
instance [LE A] : LE (ΩPart A) where
  le x y := ∀a ∈ x, ∃b ∈ y, a ≤ b

lemma dom_mono [LE A] {x y : ΩPart A} (h : x ≤ y) : Dom x ≤ Dom y := by
  intro h'
  obtain ⟨b, hb⟩ := h (x.get h') (by simp only [mem_get])
  exact hb.1.1

lemma get_mono [LE A] {x y : ΩPart A} (h : x ≤ y) (hx : _) : x.get hx ≤ y.get (dom_mono h hx) := by
  specialize h (x.get hx)
  simp only [mem_get, forall_const] at h
  rcases h with ⟨b, hb₁, hb₂⟩
  simp only [Membership.mem] at hb₁
  rcases hb₁ with ⟨b, rfl⟩
  exact hb₂

instance [Preorder A] : Preorder (ΩPart A) where
  le_refl := by
    simp only [le_def]
    grind
  le_trans := by
    simp only [le_def]
    grind

instance [PartialOrder A] : PartialOrder (ΩPart A) where
  le_antisymm x y h₁ h₂ := by
    simp only [le_def] at h₁ h₂
    ext a
    grind

open OmegaCompletePartialOrder

instance [OmegaCompletePartialOrder A] : OmegaCompletePartialOrder (ΩPart A) where
  ωSup c := {
    Dom := .any fun n ↦ (c n).Dom
    get h := Quot.recOn (ΩProp.find (ΩProp.coe_any.mp h))
      (fun n ↦ ωSup {
        toFun m := (c (m + n)).get (by
          obtain ⟨_, ⟨h, _⟩, _⟩ := c.monotone
            (by grind : n ≤ m + n)
            ((c n).get n.property)
            (by simp only [mem_get])
          exact h)
        monotone' i₁ i₂ hi := get_mono (c.monotone (by grind)) _
      })
      (by intro n₁ n₂ _
          simp only [eq_rec_constant]
          apply le_antisymm
          · simp only [ωSup_le_iff]
            intro m
            apply le_ωSup_of_le (m + n₁) (get_mono (c.monotone (Nat.le_add_right _ _)) _)
          · simp only [ωSup_le_iff]
            intro m
            apply le_ωSup_of_le (m + n₂) (get_mono (c.monotone (Nat.le_add_right _ _)) _))
  }
  le_ωSup c i a ha := by
    rcases ha with ⟨ha, rfl⟩
    simp only [eq_rec_constant, mem_mk, ↓existsAndEq, true_and]
    have : ∃n, (c n).Dom := by use i
    use ΩProp.coe_any.mpr this
    induction ΩProp.find this using Quot.ind with | mk n =>
    apply le_ωSup_of_le i (get_mono (c.monotone (Nat.le_add_right i n)) ha)
  ωSup_le c x h a ha := by
    rcases ha with ⟨ha, rfl⟩
    simp only [eq_rec_constant]
    dsimp only at ha
    induction ΩProp.find (ΩProp.coe_any.mp ha) using Quot.ind with | mk n =>
    use x.get (dom_mono (h n) n.property)
    simp only [mem_get, ωSup_le_iff, true_and]
    intro i
    apply get_mono (h (i + n))

def Chain.none [Preorder A] : Chain (ΩPart A) where
  toFun _ := .none
  monotone' _ _ _ := by grind

@[simp]
lemma Chain.none_coe [Preorder A] n : Chain.none (A := A) n = .none := by
  rfl

@[simp]
lemma ωSup_none [OmegaCompletePartialOrder A] : ωSup Chain.none = (none : ΩPart A) := by
  ext a
  simp only [
    ωSup, eq_rec_constant, mem_mk, ΩProp.coe_any,
    mem_none, iff_false, not_exists, forall_exists_index]
  intro n h₁ rfl
  simp only [Chain.none_coe, none_Dom, ΩProp.coe_false] at h₁

def Chain.some [Preorder A] (a : A) : Chain (ΩPart A) where
  toFun _ := .some a
  monotone' _ _ _ := by grind

@[simp]
lemma Chain.some_coe [Preorder A] (a : A) (n) : Chain.some a n = .some a := by
  rfl

@[simp]
lemma ωSup_some [OmegaCompletePartialOrder A] (a : A) : ωSup (Chain.some a) = some a := by
  ext b
  simp only [
    ωSup, Chain.some_coe, some_get, eq_rec_constant, mem_mk, some_Dom,
    ΩProp.any_const, ΩProp.coe_true, exists_true_left, mem_some]
  have : ↑(ΩProp.any fun n ↦ ((Chain.some b) n).Dom) := by
    simp only [Chain.some_coe, some_Dom, ΩProp.any_const, ΩProp.coe_true]
  induction ΩProp.find (ΩProp.coe_any.mp this) using Quot.ind with | mk c =>
  have : ωSup { toFun := fun m ↦ a, monotone' _ _ _ := by rfl } = a := by
    apply le_antisymm
    · simp only [ωSup_le_iff, Chain, OrderHom.coe_mk, le_refl, implies_true]
    · simp only [Chain, OrderHom.coe_mk, le_refl, le_ωSup_of_le 0]
  simp only [this]

/-- `unwrap o` gets the value at `o`, ignoring the condition. This
function is logically unsound, but operationally sound  (i.e., it
will throw an error or not terminate if the value does not exist.). -/
unsafe def unwrap (o : ΩPart A) : A := o.get lcProof

end ΩPart
