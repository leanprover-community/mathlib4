/- written mostly by Hannah Fechtner,
with enormous help from Jeremy Avigad -/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Basic
import KnotProject.Braid_Definitions_alt

/-!
# Presented Monoids

In this file we introduce presented monoids, given by a set of generators and relations.
Also known as a string re-writing system (SRS) or a semi-Thue system

This is implemented using equivalence classes of lists for the monoid elements.
We quotient by the reflexive, transitive, steps-to, symmetric closure of a relation
"steps-to" closure means that the relation can be re-written in the middle of a list

## Main results

- 'RTSClosure_equiv_relation' : the reflexive, transitive, symmetric closure of re-writing
                                a relation anywhere in a list is an equivalence relation
- 'one_m' : the unit element of the presented monoid
- 'mul_append' : multiplication on elements of the presented monoid
- instance Monoid (PresentedMonoid rel) : an instance; the monoid structure works

## References

See [Avigad, Logic and Computation, 13.2] for an account of rewrite systems.
-/

namespace PresentedMonoid

inductive StepsTo (R : List α → List α → Prop) : List α → List α → Prop
  | basic : R x y → StepsTo R x y
  | left  : StepsTo R x y → StepsTo R (z ++ x) (z ++ y)
  | right : StepsTo R x y → StepsTo R (x ++ z) (y ++ z)

-- symmetric closure of a relation
inductive SClosure (rw_rel : α → α → Prop) : α → α → Prop
  | basic : rw_rel a b → SClosure rw_rel a b
  | symm : SClosure rw_rel a b → SClosure rw_rel b a

-- alternate definition for the symmetric closure of a relation
inductive SClosure₁ (rw_rel : α → α → Prop) : α → α → Prop
  | basic : rw_rel a b → SClosure₁ rw_rel a b
  | symm : rw_rel a b → SClosure₁ rw_rel b a

-- two helpers for the below theorem
theorem SClosure_of_SClosure₁ {a b : List α} : SClosure₁ (R) a b → SClosure (R) a b := by
  intro h
  induction h
  · rename_i ih
    exact SClosure.basic ih
  rename_i ih
  apply SClosure.symm
  exact SClosure.basic ih

theorem SClosure₁_of_SClosure {a b : List α} : SClosure (R) a b → SClosure₁ (R) a b := by
  intro h
  induction h
  · rename_i ih
    exact SClosure₁.basic ih
  rename_i one two
  induction two
  · rename_i ih
    exact SClosure₁.symm ih
  rename_i ih
  exact SClosure₁.basic ih

-- the two definitions are equivalent
theorem SClosure_defs_equiv {a b : List α} : SClosure₁ (R) a b ↔ SClosure (R) a b :=
  ⟨SClosure_of_SClosure₁, SClosure₁_of_SClosure⟩

-- reflexive, transitive closure of a relation
inductive RTClosure (rw_rel : α → α → Prop) : α → α → Prop
  | refl : RTClosure rw_rel a a
  | trans : (RTClosure rw_rel a b) → RTClosure rw_rel b c → RTClosure rw_rel a c
  | rw : (rw_rel a b) → RTClosure rw_rel a b

-- first alternative definition
inductive RTClosure₁ (rw_rel : α → α → Prop) : α → α → Prop
  | refl : RTClosure₁ rw_rel a a
  | trans : (RTClosure₁ rw_rel a b) → rw_rel b c → RTClosure₁ rw_rel a c
  | rw : (rw_rel a b) → RTClosure₁ rw_rel a b

-- second alternative definition
inductive RTClosure₂ (rw_rel : α → α → Prop) : α → α → Prop
  | refl : RTClosure₂ rw_rel a a
  | trans : (rw_rel a b) → RTClosure₂ rw_rel b c → RTClosure₂ rw_rel a c
  | rw : (rw_rel a b) → RTClosure₂ rw_rel a b

--helpers to show all three definitions are equivalent
theorem RTClosure_of_RTClosure₁ {a b : List α} : RTClosure₁ (R) a b → RTClosure (R) a b := by
  intro h
  induction h
  · exact RTClosure.refl
  · rename_i simple ih
    exact RTClosure.trans ih (RTClosure.rw simple)
  next ih =>
  exact RTClosure.rw ih

theorem RTClosure₁_of_RTClosure {a b : List α} : RTClosure (R) a b → RTClosure₁ (R) a b := by
  intro h
  induction h
  · exact RTClosure₁.refl
  · rename_i d _ _ _ i j k
    induction k
    · exact j
    · rename_i p q r
      exact RTClosure₁.trans (r (RTClosure_of_RTClosure₁ p)) q
    next m =>
    exact RTClosure₁.trans j m
  next ih =>
  exact RTClosure₁.rw ih

theorem RTClosure_of_RTClosure₂ {a b : List α} : RTClosure₂ (R) a b → RTClosure (R) a b := by
  intro h
  induction h
  · exact RTClosure.refl
  · rename_i simple _ ih
    exact RTClosure.trans (RTClosure.rw simple) ih
  next ih =>
  exact RTClosure.rw ih

theorem RTClosure₂_of_RTClosure {a b : List α} : RTClosure (R) a b → RTClosure₂ (R) a b := by
  intro h
  induction h
  · exact RTClosure₂.refl
  · rename_i g i
    induction g
    · exact i
    · rename_i n o p q _ s
      apply RTClosure₂.trans o
      apply q
      · exact RTClosure_of_RTClosure₂ p
      · exact s
      exact i
    rename_i j _ _
    exact RTClosure₂.trans j i
  next ih =>
  exact RTClosure₂.rw ih

--these two aren't strictly necessary, but are just nice to have to complete things
theorem RTClosure₂_of_RTClosure₁ {a b : List α} : RTClosure₁ (R) a b → RTClosure₂ (R) a b :=
  fun h => RTClosure₂_of_RTClosure (RTClosure_of_RTClosure₁ h)

theorem RTClosure₁_of_RTClosure₂ {a b : List α} : RTClosure₂ (R) a b → RTClosure₁ (R) a b :=
  fun h => RTClosure₁_of_RTClosure (RTClosure_of_RTClosure₂ h)

--the first alternate definition is equivalent to the original
theorem RTClosure_iff_RTClosure₁ {a b : List α} : RTClosure (R) a b ↔ RTClosure₁ (R) a b :=
  ⟨RTClosure₁_of_RTClosure, RTClosure_of_RTClosure₁⟩

-- the second alternate definition is equivalent to the original
theorem RTClosure_iff_RTClosure₂ {a b : List α} : RTClosure (R) a b ↔ RTClosure₂ (R) a b :=
  ⟨RTClosure₂_of_RTClosure, RTClosure_of_RTClosure₂⟩

-- the two alternative definitions are equivalent
theorem RTClosure₁_iff_RTClosure₂ {a b : List α} : RTClosure₁ (R) a b ↔ RTClosure₂ (R) a b :=
  RTClosure_iff_RTClosure₁.symm.trans RTClosure_iff_RTClosure₂

-- the reflexive, transitive closure of a symmetric relation is symmetric
theorem RTClosure_symm_of_symm (rel : List α → List α → Prop) (symm : ∀ a b, (rel a b → rel b a)) {a b : List α} :
    (RTClosure (StepsTo rel) a b) → RTClosure (StepsTo rel) b a := by
  intro orig
  induction orig
  · exact RTClosure.refl
  · rename_i first second
    exact RTClosure.trans second first
  next ih =>
  apply RTClosure.rw
  induction ih
  · apply StepsTo.basic
    next backwards =>
    exact symm _ _ backwards
  · apply StepsTo.left
    next thing =>
    exact thing
  apply StepsTo.right
  next thing =>
  exact thing

-- the reflexive, transitive closure of the symmetric closure of a relation
-- there are perhaps other equivalent definitions, but we won't go into this here
abbrev RTSClosure (rel : List α → List α → Prop) := RTClosure (StepsTo (SClosure rel))

-- a few facts showing the properties perpetuate upwards

theorem RTSClosure_symm (rel : List α → List α → Prop) {a b : List α} :
    (RTSClosure rel a b → ((RTSClosure rel)) b a) := by
  apply RTClosure_symm_of_symm
  apply SClosure.symm

theorem StepsTo_symm_symm (rel : List α → List α → Prop) :
    StepsTo (SClosure rel) m l → StepsTo (SClosure rel) l m := by
  intro h
  induction h
  · next ih =>
      exact StepsTo.basic (SClosure.symm ih)
  · next ih1 =>
      exact StepsTo.left ih1
  next ih1 =>
    exact StepsTo.right ih1

theorem RTClosure_right {rel : List α → List α → Prop} : RTClosure (StepsTo rel) a b →
    RTClosure (StepsTo rel) (a++c) (b++c) := by
  intro h
  induction h
  · apply RTClosure.refl
  · rename_i h3 h4
    exact h3.trans h4
  next ih =>
    apply RTClosure.rw
    exact StepsTo.right ih

theorem RTClosure_left {rel : List α → List α → Prop} {c : List α}: RTClosure (StepsTo rel) a b →
    RTClosure (StepsTo rel) (c++a) (c++b) := by
  intro h
  induction h
  · exact RTClosure.refl
  · rename_i h3 h4
    exact h3.trans h4
  next ih =>
    exact RTClosure.rw (StepsTo.left ih)

theorem StepsTo_both_parts {rel : List α → List α → Prop} (h1: StepsTo rel e f)
    (h2 : StepsTo rel g h)
    : RTClosure (StepsTo rel) (List.append e g) (List.append f h) :=
  RTClosure.trans (RTClosure.rw (StepsTo.left h2)) (RTClosure.rw (StepsTo.right h1))

theorem RTClosure_both_parts {rel : List α → List α → Prop} (h1: RTClosure (StepsTo rel) e f)
    (h2 : RTClosure (StepsTo rel) g h) :
    RTClosure (StepsTo rel) (List.append e g) (List.append f h) := by
  induction h1
  · exact RTClosure_left h2
  · induction h2
    · rename_i ih1 ih2
      exact ih1.trans ih2
    · rename_i ih8 _ _ _ _ _ _ _ ih5 _
      exact ih5.trans <| RTClosure_right ih8
    rename_i ih8 _ _ _ ih1 _
    exact (ih1.trans (RTClosure_right ih8))
  rename_i ih
  exact (RTClosure_left h2).trans (RTClosure_right (RTClosure.rw ih))


-- the reflexive transitive closure of a symmetric relation is an equivalence relation
def RTClosure_equiv_relation (rel : List α → List α → Prop ) (symm_proof : Symmetric rel) :
    Equivalence (RTClosure (StepsTo rel)) where
  refl := @RTClosure.refl _ _
  symm := RTClosure_symm_of_symm rel symm_proof
  trans := @RTClosure.trans _ _

-- the reflexive transitive closure of the symmetric closure of a relation is an equivalence relation
def RTSClosure_equiv_relation (rel : List α → List α → Prop )
    : Equivalence (RTClosure (StepsTo (SClosure rel))) where
  refl := @RTClosure.refl _ _
  symm := RTSClosure_symm rel
  trans := @RTClosure.trans _ _

-- create a setoid from a symmetric relation
def mySetoid {rel : List α → List α → Prop} (symm : Symmetric rel):
  Setoid (List α) := ⟨RTClosure (StepsTo rel), RTClosure_equiv_relation rel symm⟩

-- create a setoid from an arbitrary relation by taking its symmetric closure
def mySetoid_SC (rel : List α → List α → Prop) :
  Setoid (List α) := ⟨RTClosure (StepsTo (SClosure rel)), RTSClosure_equiv_relation rel⟩

-- quotient said set by the symmetric closure of the relation ... name is as-of-yet aspirational!
abbrev PresentedMonoid (rel : List α → List α → Prop) : Type := Quotient (mySetoid_SC rel)

-- give this thing a binary operation and a unit element

-- helpers for the binary operation to make the Setoid into a Monoid
def append_monoid {rel : List α → List α → Prop} (a b : List α) : PresentedMonoid rel :=
  Quotient.mk (mySetoid_SC (rel)) (List.append a b)

theorem f_preserved_append {α : Type} {rel : List α → List α → Prop} : ∀ (a b c d : List (α)),
  (RTClosure (StepsTo (SClosure rel)) a c) → (RTClosure (StepsTo (SClosure rel)) b d) →
    @append_monoid α rel a b = append_monoid c d := by
  intro a b c d hac hbd
  apply Quotient.sound
  exact RTClosure_both_parts hac hbd

-- the binary operation to make the Setoid into a Monoid
def mul_append {α : Type} {rel : List α → List α → Prop} : PresentedMonoid rel →
      PresentedMonoid rel → PresentedMonoid rel :=
  Quotient.lift₂
    append_monoid
    f_preserved_append

-- helpers to "cancel out" Quotient.lift of Quotient.mk things
theorem generated_helper_1 {α : Type} {rel : List α → List α → Prop} (a : Quotient (mySetoid_SC rel))
    (f : Quotient (mySetoid_SC rel) → Prop)
    (h: ∀ a', f (Quotient.mk (mySetoid_SC (rel)) a')) : f a := by
    have H := Quotient.exists_rep a
    match H with
    | ⟨ b, hb⟩ =>
        rw [← hb]
        apply h

theorem generated_helper_2 {α : Type} {rel : List α → List α → Prop} (a b : Quotient (mySetoid_SC rel))
    (f : Quotient (mySetoid_SC rel) → Quotient (mySetoid_SC rel) → Prop)
    (h: ∀ a' b', f (Quotient.mk (mySetoid_SC (rel)) a') (Quotient.mk (mySetoid_SC (rel)) b'))
    : f a b := by
  have Ha := Quotient.exists_rep a
  have Hb := Quotient.exists_rep b
  match Ha, Hb with
  | ⟨a', ha⟩, ⟨b', hb⟩ =>
      rw [← ha, ← hb]
      apply h

theorem generated_helper_3 {α : Type} {rel : List α → List α → Prop} (a b c : Quotient (mySetoid_SC rel))
    (f : Quotient (mySetoid_SC rel) → Quotient (mySetoid_SC rel) → Quotient (mySetoid_SC rel) → Prop)
    (h: ∀ a' b' c', f (Quotient.mk (mySetoid_SC (rel)) a') (Quotient.mk (mySetoid_SC (rel)) b') (Quotient.mk (mySetoid_SC (rel)) c'))
    : f a b c := by
  have Ha := Quotient.exists_rep a
  have Hb := Quotient.exists_rep b
  have Hc := Quotient.exists_rep c
  match Ha, Hb, Hc with
  | ⟨a', ha⟩, ⟨b', hb⟩, ⟨c', hc⟩ =>
        rw [← ha, ← hb, ←hc]
        apply h

-- associativity of our binary operator
theorem mul_assoc_monoid {α : Type} {rel : List α → List α → Prop} : ∀ (a b c : Quotient (mySetoid_SC rel)),
    mul_append (mul_append a  b) c = mul_append a (mul_append b c) := by
  intro a b c
  have H : ∀ a' b' c', (mul_append (mul_append (Quotient.mk (mySetoid_SC (rel)) a')
    (Quotient.mk (mySetoid_SC (rel)) b')) (Quotient.mk (mySetoid_SC (rel)) c') )
    = mul_append (Quotient.mk (mySetoid_SC (rel)) a')
    (mul_append (Quotient.mk (mySetoid_SC (rel)) b') (Quotient.mk (mySetoid_SC (rel)) c')) := by
    intro a' b' c'
    apply Quotient.sound
    simp only [List.append_eq, List.append_assoc]
    apply refl
  apply generated_helper_3 a b c
    (λ (a : Quotient (mySetoid_SC rel))  => λ b => λ c =>
    mul_append (mul_append a b) c = mul_append a (mul_append b c)) H

-- unit element for the monoid
def one_m {α : Type} {rel : List α → List α → Prop} := Quotient.mk (mySetoid_SC (rel)) []

-- and its properties hold
theorem one_mul_monoid {α : Type} {rel : List α → List α → Prop} : ∀ (a : PresentedMonoid rel),
    @mul_append _ rel one_m a = a := by
  intro a
  have H : ∀ (a' : List α), mul_append one_m (Quotient.mk (mySetoid_SC rel) a')
            = Quotient.mk (mySetoid_SC rel) a' := by
    intro a'
    apply Quotient.sound
    simp only [List.append_eq, List.nil_append]
    apply refl
  apply generated_helper_1 a (λ a => @mul_append _ rel one_m a = a) H

theorem mul_one_monoid {α : Type} {rel : List α → List α → Prop} : ∀ (a : PresentedMonoid rel),
    mul_append a one_m = a := by
  intro a
  have H : ∀ (a' : List α), mul_append (Quotient.mk (mySetoid_SC rel) a') one_m
            = Quotient.mk (mySetoid_SC rel) a' := by
    intro a'
    apply Quotient.sound
    simp only [List.append_eq, List.append_nil]
    apply refl
  apply generated_helper_1 a (λ a => @mul_append _ rel a one_m = a) H

-- showing that with our binary operator and unit element, we have a monoid!
instance {α : Type} {rel : List α → List α → Prop} : Monoid (PresentedMonoid rel) where
  mul := mul_append
  one := one_m
  mul_assoc := mul_assoc_monoid
  one_mul := one_mul_monoid
  mul_one := mul_one_monoid

-- just to make sure lean knows the "nickname" for this presented monoid thing
instance {α : Type} {rel : List α → List α → Prop} : Monoid (Quotient (mySetoid_SC rel)) :=
  inferInstanceAs <| Monoid (PresentedMonoid rel)
