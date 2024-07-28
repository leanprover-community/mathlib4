/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Setoid.Basic

/-!
# Congruence relations

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `Setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `ConGen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `EqvGen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `EqvGen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

/-- A congruence relation on a type with an addition is an equivalence relation which
    preserves addition. -/
structure AddCon [Add M] extends Setoid M where
  /-- Additive congruence relations are closed under addition -/
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)

/-- A congruence relation on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
@[to_additive AddCon]
structure Con [Mul M] extends Setoid M where
  /-- Congruence relations are closed under multiplication -/
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)

/-- The equivalence relation underlying an additive congruence relation. -/
add_decl_doc AddCon.toSetoid

/-- The equivalence relation underlying a multiplicative congruence relation. -/
add_decl_doc Con.toSetoid

variable {M}

/-- The inductively defined smallest additive congruence relation containing a given binary
    relation. -/
inductive AddConGen.Rel [Add M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → AddConGen.Rel r x y
  | refl : ∀ x, AddConGen.Rel r x x
  | symm : ∀ {x y}, AddConGen.Rel r x y → AddConGen.Rel r y x
  | trans : ∀ {x y z}, AddConGen.Rel r x y → AddConGen.Rel r y z → AddConGen.Rel r x z
  | add : ∀ {w x y z}, AddConGen.Rel r w x → AddConGen.Rel r y z → AddConGen.Rel r (w + y) (x + z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive AddConGen.Rel]
inductive ConGen.Rel [Mul M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → ConGen.Rel r x y
  | refl : ∀ x, ConGen.Rel r x x
  | symm : ∀ {x y}, ConGen.Rel r x y → ConGen.Rel r y x
  | trans : ∀ {x y z}, ConGen.Rel r x y → ConGen.Rel r y z → ConGen.Rel r x z
  | mul : ∀ {w x y z}, ConGen.Rel r w x → ConGen.Rel r y z → ConGen.Rel r (w * y) (x * z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive addConGen "The inductively defined smallest additive congruence relation containing
a given binary relation."]
def conGen [Mul M] (r : M → M → Prop) : Con M :=
  ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩

namespace Con

section

variable [Mul M] [Mul N] [Mul P] (c : Con M)

@[to_additive]
instance : Inhabited (Con M) :=
  ⟨conGen EmptyRelation⟩

-- Porting note: upgraded to FunLike
/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive "A coercion from an additive congruence relation to its underlying binary relation."]
instance : FunLike (Con M) M (M → Prop) where
  coe c := c.r
  coe_injective' := fun x y h => by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    have : x = y := h
    subst x; rfl

@[to_additive (attr := simp)]
theorem rel_eq_coe (c : Con M) : c.r = c :=
  rfl

/-- Congruence relations are reflexive. -/
@[to_additive "Additive congruence relations are reflexive."]
protected theorem refl (x) : c x x :=
  c.toSetoid.refl' x

/-- Congruence relations are symmetric. -/
@[to_additive "Additive congruence relations are symmetric."]
protected theorem symm {x y} : c x y → c y x := c.toSetoid.symm'

/-- Congruence relations are transitive. -/
@[to_additive "Additive congruence relations are transitive."]
protected theorem trans {x y z} : c x y → c y z → c x z := c.toSetoid.trans'

/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive "Additive congruence relations preserve addition."]
protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) := c.mul'

@[to_additive (attr := simp)]
theorem rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b :=
  Iff.rfl

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
    `x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive "Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation
`c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`."]
instance : Membership (M × M) (Con M) :=
  ⟨fun x c => c x.1 x.2⟩

variable {c}

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying binary relation
is injective."]
theorem ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[to_additive (attr := ext) "Extensionality rule for additive congruence relations."]
theorem ext {c d : Con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext; apply H

/-- The map sending a congruence relation to its underlying equivalence relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying equivalence
relation is injective."]
theorem toSetoid_inj {c d : Con M} (H : c.toSetoid = d.toSetoid) : c = d :=
  ext <| ext_iff.1 H

/-- Iff version of extensionality rule for congruence relations. -/
@[to_additive "Iff version of extensionality rule for additive congruence relations."]
protected theorem ext_iff {c d : Con M} : c = d ↔ (∀ x y, c x y ↔ d x y) :=
  ⟨fun h _ _ => h ▸ Iff.rfl, ext⟩

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive "Two additive congruence relations are equal iff their underlying binary relations
are equal."]
theorem coe_inj {c d : Con M} : ⇑c = ⇑d ↔ c = d := DFunLike.coe_injective.eq_iff

/-- The kernel of a multiplication-preserving function as a congruence relation. -/
@[to_additive "The kernel of an addition-preserving function as an additive congruence relation."]
def mulKer (f : M → P) (h : ∀ x y, f (x * y) = f x * f y) : Con M where
  toSetoid := Setoid.ker f
  mul' h1 h2 := by
    dsimp [Setoid.ker, onFun] at *
    rw [h, h1, h2, h]

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
    `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod "Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`."]
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive "The product of an indexed collection of additive congruence relations."]
def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

variable (c)

-- Quotients
/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive "Defining the quotient by an additive congruence relation of a type with
an addition."]
protected def Quotient :=
  Quotient c.toSetoid

-- Porting note: made implicit
variable {c}

/-- The morphism into the quotient by a congruence relation -/
@[to_additive (attr := coe) "The morphism into the quotient by an additive congruence relation"]
def toQuotient : M → c.Quotient :=
  Quotient.mk''

variable (c)

-- Porting note: was `priority 0`. why?
/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive "Coercion from a type with an addition to its quotient by an additive congruence
relation"]
instance (priority := 10) : CoeTC M c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive "The quotient by a decidable additive congruence relation has decidable equality."]
instance (priority := 500) [∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[to_additive (attr := simp)]
theorem quot_mk_eq_coe {M : Type*} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x : c.Quotient) :=
  rfl

-- Porting note (#11215): TODO: restore `elab_as_elim`
/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
@[to_additive "The function on the quotient by a congruence relation `c`
induced by a function that is constant on `c`'s equivalence classes."]
protected def liftOn {β} {c : Con M} (q : c.Quotient) (f : M → β) (h : ∀ a b, c a b → f a = f b) :
    β :=
  Quotient.liftOn' q f h

-- Porting note (#11215): TODO: restore `elab_as_elim`
/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
    that is constant on `c`'s equivalence classes. -/
@[to_additive "The binary function on the quotient by a congruence relation `c`
induced by a binary function that is constant on `c`'s equivalence classes."]
protected def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M → M → β)
    (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h

/-- A version of `Quotient.hrecOn₂'` for quotients by `Con`. -/
@[to_additive "A version of `Quotient.hrecOn₂'` for quotients by `AddCon`."]
protected def hrecOn₂ {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort*}
    (a : cM.Quotient) (b : cN.Quotient) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → HEq (f x y) (f x' y')) : φ a b :=
  Quotient.hrecOn₂' a b f h

@[to_additive (attr := simp)]
theorem hrec_on₂_coe {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort*} (a : M)
    (b : N) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → HEq (f x y) (f x' y')) :
    Con.hrecOn₂ (↑a) (↑b) f h = f a b :=
  rfl

variable {c}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
    congruence relation. -/
@[to_additive (attr := elab_as_elim) "The inductive principle used to prove propositions about
the elements of a quotient by an additive congruence relation."]
protected theorem induction_on {C : c.Quotient → Prop} (q : c.Quotient) (H : ∀ x : M, C x) : C q :=
  Quotient.inductionOn' q H

/-- A version of `Con.induction_on` for predicates which take two arguments. -/
@[to_additive (attr := elab_as_elim) "A version of `AddCon.induction_on` for predicates which take
two arguments."]
protected theorem induction_on₂ {d : Con N} {C : c.Quotient → d.Quotient → Prop} (p : c.Quotient)
    (q : d.Quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
  Quotient.inductionOn₂' p q H

variable (c)

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[to_additive (attr := simp) "Two elements are related by an additive congruence relation `c` iff
they are represented by the same element of the quotient by `c`."]
protected theorem eq {a b : M} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''

/-- The multiplication induced on the quotient by a congruence relation on a type with a
    multiplication. -/
@[to_additive "The addition induced on the quotient by an additive congruence relation on a type
with an addition."]
instance hasMul : Mul c.Quotient :=
  ⟨Quotient.map₂' (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩

/-- The kernel of the quotient map induced by a congruence relation `c` equals `c`. -/
@[to_additive (attr := simp) "The kernel of the quotient map induced by an additive congruence
relation `c` equals `c`."]
theorem mul_ker_mk_eq : (mulKer ((↑) : M → c.Quotient) fun _ _ => rfl) = c :=
  ext fun _ _ => Quotient.eq''

variable {c}

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
    definition). -/
@[to_additive (attr := simp) "The coercion to the quotient of an additive congruence relation
commutes with addition (by definition)."]
theorem coe_mul (x y : M) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
    that is constant on `c`'s equivalence classes. -/
@[to_additive (attr := simp) "Definition of the function on the quotient by an additive congruence
relation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected theorem liftOn_coe {β} (c : Con M) (f : M → β) (h : ∀ a b, c a b → f a = f b) (x : M) :
    Con.liftOn (x : c.Quotient) f h = f x :=
  rfl

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
@[to_additive "Makes an additive isomorphism of quotients by two additive congruence relations,
given that the relations are equal."]
protected def congr {c d : Con M} (h : c = d) : c.Quotient ≃* d.Quotient :=
  { Quotient.congr (Equiv.refl M) <| by apply Con.ext_iff.mp h with
    map_mul' := fun x y => by rcases x with ⟨⟩; rcases y with ⟨⟩; rfl }

-- The complete lattice of congruence relations on a type
/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive "For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`."]
instance : LE (Con M) where
  le c d := ∀ ⦃x y⦄, c x y → d x y

/-- Definition of `≤` for congruence relations. -/
@[to_additive "Definition of `≤` for additive congruence relations."]
theorem le_def {c d : Con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type with
an addition."]
instance : InfSet (Con M) where
  sInf S :=
    { r := fun x y => ∀ c : Con M, c ∈ S → c x y
      iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm <| h c hc,
        fun h1 h2 c hc => c.trans (h1 c hc) <| h2 c hc⟩
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of
the set's image under the map to the underlying equivalence relation."]
theorem sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S) :=
  Setoid.ext' fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[to_additive (attr := simp, norm_cast)
  "The infimum of a set of additive congruence relations is the same as the infimum
  of the set's image under the map to the underlying binary relation."]
theorem coe_sInf (S : Set (Con M)) :
    ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} (f : ι → Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf, ← Set.range_comp, sInf_range, Function.comp]

@[to_additive]
instance : PartialOrder (Con M) where
  le_refl _ _ _ := id
  le_trans _ _ _ h1 h2 _ _ h := h2 <| h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive "The complete lattice of additive congruence relations on a given type with
an addition."]
instance : CompleteLattice (Con M) where
  __ := completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
        hr hr'
          h⟩
  inf c d := ⟨c.toSetoid ⊓ d.toSetoid, fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf  _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top := { Setoid.completeLattice.top with mul' := by tauto }
  le_top _ := fun _ _ _ => trivial
  bot := { Setoid.completeLattice.bot with mul' := fun h1 h2 => h1 ▸ h2 ▸ rfl }
  bot_le c := fun x y h => h ▸ c.refl x

/-- The infimum of two congruence relations equals the infimum of the underlying binary
    operations. -/
@[to_additive (attr := simp, norm_cast)
  "The infimum of two additive congruence relations equals the infimum of the underlying binary
  operations."]
theorem coe_inf {c d : Con M} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d :=
  rfl

/-- Definition of the infimum of two congruence relations. -/
@[to_additive "Definition of the infimum of two additive congruence relations."]
theorem inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
@[to_additive addConGen_eq "The inductively defined smallest additive congruence relation
containing a binary relation `r` equals the infimum of the set of additive congruence relations
containing `r`."]
theorem conGen_eq (r : M → M → Prop) : conGen r = sInf { s : Con M | ∀ x y, r x y → s x y } :=
  le_antisymm
    (le_sInf (fun s hs x y (hxy : (conGen r) x y) =>
      show s x y by
        apply ConGen.Rel.recOn (motive := fun x y _ => s x y) hxy
        · exact fun x y h => hs x y h
        · exact s.refl'
        · exact fun _ => s.symm'
        · exact fun _ _ => s.trans'
        · exact fun _ _ => s.mul))
    (sInf_le ConGen.Rel.of)

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
@[to_additive addConGen_le "The smallest additive congruence relation containing a binary
relation `r` is contained in any additive congruence relation containing `r`."]
theorem conGen_le {r : M → M → Prop} {c : Con M} (h : ∀ x y, r x y → c x y) :
    conGen r ≤ c := by rw [conGen_eq]; exact sInf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive addConGen_mono "Given binary relations `r, s` with `r` contained in `s`, the
smallest additive congruence relation containing `s` contains the smallest additive congruence
relation containing `r`."]
theorem conGen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) : conGen r ≤ conGen s :=
  conGen_le fun x y hr => ConGen.Rel.of _ _ <| h x y hr

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[to_additive (attr := simp) addConGen_of_addCon "Additive congruence relations equal the smallest
additive congruence relation in which they are contained."]
theorem conGen_of_con (c : Con M) : conGen c = c :=
  le_antisymm (by rw [conGen_eq]; exact sInf_le fun _ _ => id) ConGen.Rel.of

-- Porting note: removing simp, simp can prove it
/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
@[to_additive addConGen_idem "The map sending a binary relation to the smallest additive
congruence relation in which it is contained is idempotent."]
theorem conGen_idem (r : M → M → Prop) : conGen (conGen r) = conGen r :=
  conGen_of_con _

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive sup_eq_addConGen "The supremum of additive congruence relations `c, d` equals the
smallest additive congruence relation containing the binary relation '`x` is related to `y`
by `c` or `d`'."]
theorem sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y := by
  rw [conGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
@[to_additive "The supremum of two additive congruence relations equals the smallest additive
congruence relation containing the supremum of the underlying binary operations."]
theorem sup_def {c d : Con M} : c ⊔ d = conGen (⇑c ⊔ ⇑d) := by rw [sup_eq_conGen]; rfl

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
@[to_additive sSup_eq_addConGen "The supremum of a set of additive congruence relations `S` equals
the smallest additive congruence relation containing the binary relation 'there exists `c ∈ S`
such that `x` is related to `y` by `c`'."]
theorem sSup_eq_conGen (S : Set (Con M)) :
    sSup S = conGen fun x y => ∃ c : Con M, c ∈ S ∧ c x y := by
  rw [conGen_eq]
  apply congr_arg sInf
  ext
  exact ⟨fun h _ _ ⟨r, hr⟩ => h hr.1 hr.2, fun h r hS _ _ hr => h _ _ ⟨r, hS, hr⟩⟩

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive "The supremum of a set of additive congruence relations is the same as the smallest
additive congruence relation containing the supremum of the set's image under the map to the
underlying binary relation."]
theorem sSup_def {S : Set (Con M)} :
    sSup S = conGen (sSup ((⇑) '' S)) := by
  rw [sSup_eq_conGen, sSup_image]
  congr with (x y)
  simp only [sSup_image, iSup_apply, iSup_Prop_eq, exists_prop, rel_eq_coe]

variable (M)

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
@[to_additive "There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`."]
protected def gi : @GaloisInsertion (M → M → Prop) (Con M) _ _ conGen DFunLike.coe where
  choice r _ := conGen r
  gc _ c := ⟨fun H _ _ h => H <| ConGen.Rel.of _ _ h, @fun H => conGen_of_con c ▸ conGen_mono H⟩
  le_l_u x := (conGen_of_con x).symm ▸ le_refl x
  choice_eq _ _ := rfl

variable {M} (c)

/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
    image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
    by a congruence relation `c`.' -/
@[to_additive "Given a function `f`, the smallest additive congruence relation containing the
binary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the
elements of `f⁻¹(y)` by an additive congruence relation `c`.'"]
def mapGen (f : M → N) : Con N :=
  conGen fun x y => ∃ a b, f a = x ∧ f b = y ∧ c a b

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
    congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
    elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive "Given a surjective addition-preserving function `f` whose kernel is contained in
an additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined
by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.'"]
def mapOfSurjective (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (h : mulKer f H ≤ c)
    (hf : Surjective f) : Con N :=
  { c.toSetoid.mapOfSurjective f h hf with
    mul' := fun h₁ h₂ => by
      rcases h₁ with ⟨a, b, rfl, rfl, h1⟩
      rcases h₂ with ⟨p, q, rfl, rfl, h2⟩
      exact ⟨a * p, b * q, by rw [H], by rw [H], c.mul h1 h2⟩ }

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
    equals `c`'. -/
@[to_additive "A specialization of 'the smallest additive congruence relation containing
an additive congruence relation `c` equals `c`'."]
theorem mapOfSurjective_eq_mapGen {c : Con M} {f : M → N} (H : ∀ x y, f (x * y) = f x * f y)
    (h : mulKer f H ≤ c) (hf : Surjective f) : c.mapGen f = c.mapOfSurjective f H h hf := by
  rw [← conGen_of_con (c.mapOfSurjective f H h hf)]; rfl

/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
    multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
    defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
@[to_additive "Given types with additions `M, N` and an additive congruence relation `c` on `N`,
an addition-preserving map `f : M → N` induces an additive congruence relation on `f`'s domain
defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' "]
def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]
theorem comap_rel {f : M → N} (H : ∀ x y, f (x * y) = f x * f y) {c : Con N} {x y : M} :
    comap f H c x y ↔ c (f x) (f y) :=
  Iff.rfl

section

open Quotient

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
    bijection between the set of congruence relations containing `c` and the congruence relations
    on the quotient of `M` by `c`. -/
@[to_additive "Given an additive congruence relation `c` on a type `M` with an addition,
the order-preserving bijection between the set of additive congruence relations containing `c` and
the additive congruence relations on the quotient of `M` by `c`."]
def correspondence : { d // c ≤ d } ≃o Con c.Quotient where
  toFun d :=
    d.1.mapOfSurjective (↑) (fun x y => rfl) (by rw [mul_ker_mk_eq]; exact d.2) <|
      @Quotient.exists_rep _ c.toSetoid
  invFun d :=
    ⟨comap ((↑) : M → c.Quotient) (fun x y => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      Subtype.ext_iff_val.2 <|
        ext fun x y =>
          ⟨fun h =>
            let ⟨a, b, hx, hy, H⟩ := h
            d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) <| d.1.trans H <| d.2 <| c.eq.1 hy,
            fun h => ⟨_, _, rfl, rfl, h⟩⟩
  right_inv d :=
    -- Porting note: by exact needed for unknown reason
    by exact
      ext fun x y =>
        ⟨fun h =>
          let ⟨_, _, hx, hy, H⟩ := h
          hx ▸ hy ▸ H,
          Con.induction_on₂ x y fun w z h => ⟨w, z, rfl, rfl, h⟩⟩
  map_rel_iff' := @fun s t => by
    constructor
    · intros h x y hs
      rcases h ⟨x, y, rfl, rfl, hs⟩ with ⟨a, b, hx, hy, ht⟩
      exact t.1.trans (t.1.symm <| t.2 <| Quotient.eq_rel.1 hx)
        (t.1.trans ht (t.2 <| Quotient.eq_rel.1 hy))
    · intros h _ _ hs
      rcases hs with ⟨a, b, hx, hy, Hs⟩
      exact ⟨a, b, hx, hy, h Hs⟩

end

end

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive "The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`."]
instance mulOneClass : MulOneClass c.Quotient where
  one := ((1 : M) : c.Quotient)
  mul_one x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M → c.Quotient) <| mul_one _
  one_mul x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M → c.Quotient) <| one_mul _

variable {c}

/-- The 1 of the quotient of a monoid by a congruence relation is the equivalence class of the
    monoid's 1. -/
@[to_additive (attr := simp) "The 0 of the quotient of an `AddMonoid` by an additive congruence
relation is the equivalence class of the `AddMonoid`'s 0."]
theorem coe_one : ((1 : M) : c.Quotient) = 1 :=
  rfl

variable (c)

-- Porting note: made M implicit
/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive (attr := coe) "The `AddSubmonoid` of `M × M` defined by an additive congruence
relation on an `AddMonoid` `M`."]
protected def submonoid : Submonoid (M × M) where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

variable {c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
    is an equivalence relation. -/
@[to_additive "The additive congruence relation on an `AddMonoid` `M` from
an `AddSubmonoid` of `M × M` for which membership is an equivalence relation."]
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M where
  r x y := (x, y) ∈ N
  iseqv := H
  mul' := N.mul_mem

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
    elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive "Coercion from a congruence relation `c` on an `AddMonoid` `M`
to the `AddSubmonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`."]
instance toSubmonoid : Coe (Con M) (Submonoid (M × M)) :=
  ⟨fun c => c.submonoid⟩

@[to_additive]
theorem mem_coe {c : Con M} {x y} : (x, y) ∈ (↑c : Submonoid (M × M)) ↔ (x, y) ∈ c :=
  Iff.rfl

@[to_additive]
theorem to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d :=
  ext fun x y => show (x, y) ∈ c.submonoid ↔ (x, y) ∈ d from H ▸ Iff.rfl

@[to_additive]
theorem le_iff {c d : Con M} : c ≤ d ↔ (c : Submonoid (M × M)) ≤ d :=
  ⟨fun h _ H => h H, fun h x y hc => h <| show (x, y) ∈ c from hc⟩

/-- The kernel of a monoid homomorphism as a congruence relation. -/
@[to_additive "The kernel of an `AddMonoid` homomorphism as an additive congruence relation."]
def ker (f : M →* P) : Con M :=
  mulKer f (map_mul f)

/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[to_additive (attr := simp) "The definition of the additive congruence relation defined by an
`AddMonoid` homomorphism's kernel."]
theorem ker_rel (f : M →* P) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive "There exists an element of the quotient of an `AddMonoid` by a congruence relation
(namely 0)."]
instance Quotient.inhabited : Inhabited c.Quotient :=
  ⟨((1 : M) : c.Quotient)⟩

variable (c)

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive "The natural homomorphism from an `AddMonoid` to its quotient by an additive
congruence relation."]
def mk' : M →* c.Quotient :=
  { toFun := (↑)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

variable (x y : M)

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
    relation `c` equals `c`. -/
@[to_additive (attr := simp) "The kernel of the natural homomorphism from an `AddMonoid` to its
quotient by an additive congruence relation `c` equals `c`."]
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.eq

variable {c}

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
    surjective. -/
@[to_additive "The natural homomorphism from an `AddMonoid` to its quotient by a congruence
relation is surjective."]
theorem mk'_surjective : Surjective c.mk' :=
  Quotient.surjective_Quotient_mk''

@[to_additive (attr := simp)]
theorem coe_mk' : (c.mk' : M → c.Quotient) = ((↑) : M → c.Quotient) :=
  rfl

@[to_additive (attr := simp)]
-- Porting note: removed dot notation
theorem mrange_mk' : MonoidHom.mrange c.mk' = ⊤ :=
  MonoidHom.mrange_top_iff_surjective.2 mk'_surjective

-- Porting note: used to abuse defeq between sets and predicates
@[to_additive]
theorem ker_apply {f : M →* P} {x y} : ker f x y ↔ f x = f y := Iff.rfl

/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
    relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
    `f`. -/
@[to_additive "Given an `AddMonoid` homomorphism `f : N → M` and an additive congruence relation
`c` on `M`, the additive congruence relation induced on `N` by `f` equals the kernel of `c`'s
quotient homomorphism composed with `f`."]
theorem comap_eq {f : N →* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

variable (c) (f : M →* P)

/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
    homomorphism constant on `c`'s equivalence classes. -/
@[to_additive "The homomorphism on the quotient of an `AddMonoid` by an additive congruence
relation `c` induced by a homomorphism constant on `c`'s equivalence classes."]
def lift (H : c ≤ ker f) : c.Quotient →* P where
  toFun x := (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]

variable {c f}

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive "The diagram describing the universal property for quotients of `AddMonoid`s
commutes."]
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) "The diagram describing the universal property for quotients of
`AddMonoid`s commutes."]
theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) "The diagram describing the universal property for quotients of
`AddMonoid`s commutes."]
theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext; rfl

/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
    homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
    the quotient. -/
@[to_additive (attr := simp) "Given a homomorphism `f` from the quotient of an `AddMonoid` by an
additive congruence relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the `AddMonoid` to the quotient."]
theorem lift_apply_mk' (f : c.Quotient →* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
    are equal on elements that are coercions from the monoid. -/
@[to_additive "Homomorphisms on the quotient of an `AddMonoid` by an additive congruence relation
are equal if they are equal on elements that are coercions from the `AddMonoid`."]
theorem lift_funext (f g : c.Quotient →* P) (h : ∀ a : M, f a = g a) : f = g := by
  rw [← lift_apply_mk' f, ← lift_apply_mk' g]
  congr 1
  exact DFunLike.ext_iff.2 h

/-- The uniqueness part of the universal property for quotients of monoids. -/
@[to_additive "The uniqueness part of the universal property for quotients of `AddMonoid`s."]
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  (lift_funext g (c.lift f H)) fun x => by
    subst f
    rfl

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
    equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
    quotient. -/
@[to_additive "Given an additive congruence relation `c` on an `AddMonoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient."]
theorem lift_range (H : c ≤ ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
    induce a surjective homomorphism on `c`'s quotient. -/
@[to_additive "Surjective `AddMonoid` homomorphisms constant on an additive congruence
relation `c`'s equivalence classes induce a surjective homomorphism on `c`'s quotient."]
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

variable (c f)

/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
    relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
@[to_additive "Given an `AddMonoid` homomorphism `f` from `M` to `P`, the kernel of `f`
is the unique additive congruence relation on `M` whose induced map from the quotient of `M`
to `P` is injective."]
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  toSetoid_inj <| Setoid.ker_eq_lift_of_injective f H h

variable {c}

/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
@[to_additive "The homomorphism induced on the quotient of an `AddMonoid` by the kernel
of an `AddMonoid` homomorphism."]
def kerLift : (ker f).Quotient →* P :=
  ((ker f).lift f) fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of monoids, when the congruence
    relation is the kernel of the homomorphism, commutes. -/
@[to_additive (attr := simp) "The diagram described by the universal property for quotients
of `AddMonoid`s, when the additive congruence relation is the kernel of the homomorphism,
commutes."]
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[to_additive (attr := simp) "Given an `AddMonoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`."]
theorem kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f :=
  lift_range fun _ _ => id

/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive "An `AddMonoid` homomorphism `f` induces an injective homomorphism on the quotient
by `f`'s kernel."]
theorem kerLift_injective (f : M →* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
    map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive "Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient
by `d`."]
def map (c d : Con M) (h : c ≤ d) : c.Quotient →* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
    the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient
    map. -/
@[to_additive "Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, the definition of the homomorphism from the quotient by `c` to the quotient by `d`
induced by `d`'s quotient map."]
theorem map_apply {c d : Con M} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

variable (c)

/-- The **first isomorphism theorem for monoids**. -/
@[to_additive "The first isomorphism theorem for `AddMonoid`s."]
noncomputable def quotientKerEquivRange (f : M →* P) : (ker f).Quotient ≃* MonoidHom.mrange f :=
  { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.submonoidCongr kerLift_range_eq)).comp
        ⟨fun x y h =>
          kerLift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩; rfl⟩⟩) with
    map_mul' := MonoidHom.map_mul _ }

/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive (attr := simps)
  "The first isomorphism theorem for `AddMonoid`s in the case of a homomorphism
  with right inverse."]
def quotientKerEquivOfRightInverse (f : M →* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

/-- The first isomorphism theorem for Monoids in the case of a surjective homomorphism.

For a `computable` version, see `Con.quotientKerEquivOfRightInverse`.
-/
@[to_additive "The first isomorphism theorem for `AddMonoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `AddCon.quotientKerEquivOfRightInverse`.
"]
noncomputable def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- The **second isomorphism theorem for monoids**. -/
@[to_additive "The second isomorphism theorem for `AddMonoid`s."]
noncomputable def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
  (Con.congr comap_eq).trans <| quotientKerEquivRange <| c.mk'.comp f

/-- The **third isomorphism theorem for monoids**. -/
@[to_additive "The third isomorphism theorem for `AddMonoid`s."]
def quotientQuotientEquivQuotient (c d : Con M) (h : c ≤ d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

end MulOneClass

section Monoids

/-- Multiplicative congruence relations preserve natural powers. -/
@[to_additive "Additive congruence relations preserve natural scaling."]
protected theorem pow {M : Type*} [Monoid M] (c : Con M) :
    ∀ (n : ℕ) {w x}, c w x → c (w ^ n) (x ^ n)
  | 0, w, x, _ => by simpa using c.refl _
  | Nat.succ n, w, x, h => by simpa [pow_succ] using c.mul (Con.pow c n h) h

@[to_additive]
instance one [MulOneClass M] (c : Con M) : One c.Quotient where
  -- Using Quotient.mk'' here instead of c.toQuotient
  -- since c.toQuotient is not reducible.
  -- This would lead to non-defeq diamonds since this instance ends up in
  -- quotients modulo ideals.
  one := Quotient.mk'' (1 : M)
  -- one := ((1 : M) : c.Quotient)

@[to_additive]
theorem smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    {w x : M} (h : c w x) : c (a • w) (a • x) := by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

instance _root_.AddCon.Quotient.nsmul {M : Type*} [AddMonoid M] (c : AddCon M) :
    SMul ℕ c.Quotient where
  smul n := (Quotient.map' (n • ·)) fun _ _ => c.nsmul n

@[to_additive existing AddCon.Quotient.nsmul]
instance {M : Type*} [Monoid M] (c : Con M) : Pow c.Quotient ℕ where
  pow x n := Quotient.map' (fun x => x ^ n) (fun _ _ => c.pow n) x

/-- The quotient of a semigroup by a congruence relation is a semigroup. -/
@[to_additive "The quotient of an `AddSemigroup` by an additive congruence relation is
an `AddSemigroup`."]
instance semigroup {M : Type*} [Semigroup M] (c : Con M) : Semigroup c.Quotient :=
  { (Function.Surjective.semigroup _ Quotient.surjective_Quotient_mk'' fun _ _ => rfl :
      Semigroup c.Quotient) with
    /- The `toMul` field is given explicitly for performance reasons.
    This avoids any need to unfold `Function.Surjective.semigroup` when the type checker is checking
    that instance diagrams commute -/
    toMul := Con.hasMul _ }

/-- The quotient of a commutative semigroup by a congruence relation is a semigroup. -/
@[to_additive "The quotient of an `AddCommSemigroup` by an additive congruence relation is
an `AddCommSemigroup`."]
instance commSemigroup {M : Type*} [CommSemigroup M] (c : Con M) : CommSemigroup c.Quotient :=
  { (Function.Surjective.commSemigroup _ Quotient.surjective_Quotient_mk'' fun _ _ => rfl :
      CommSemigroup c.Quotient) with
    /- The `toSemigroup` field is given explicitly for performance reasons.
    This avoids any need to unfold `Function.Surjective.commSemigroup` when the type checker is
    checking that instance diagrams commute -/
    toSemigroup := Con.semigroup _ }

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive "The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`."]
instance monoid {M : Type*} [Monoid M] (c : Con M) : Monoid c.Quotient :=
  { (Function.Surjective.monoid _ Quotient.surjective_Quotient_mk'' rfl
      (fun _ _ => rfl) fun _ _ => rfl : Monoid c.Quotient) with
    /- The `toSemigroup` and `toOne` fields are given explicitly for performance reasons.
    This avoids any need to unfold `Function.Surjective.monoid` when the type checker is
    checking that instance diagrams commute -/
    toSemigroup := Con.semigroup _
    toOne := Con.one _ }

/-- The quotient of a `CommMonoid` by a congruence relation is a `CommMonoid`. -/
@[to_additive "The quotient of an `AddCommMonoid` by an additive congruence
relation is an `AddCommMonoid`."]
instance commMonoid {M : Type*} [CommMonoid M] (c : Con M) : CommMonoid c.Quotient :=
  { (Function.Surjective.commMonoid _ Quotient.surjective_Quotient_mk'' rfl
      (fun _ _ => rfl) fun _ _ => rfl : CommMonoid c.Quotient) with
    /- The `toMonoid` field is given explicitly for performance reasons.
    This avoids any need to unfold `Function.Surjective.commMonoid` when the type checker is
    checking that instance diagrams commute -/
    toMonoid := Con.monoid _ }

/-- Sometimes, a group is defined as a quotient of a monoid by a congruence relation.
Usually, the inverse operation is defined as `Setoid.map f _` for some `f`.
This lemma allows to avoid code duplication in the definition of the inverse operation:
instead of proving both `∀ x y, c x y → c (f x) (f y)` (to define the operation)
and `∀ x, c (f x * x) 1` (to prove the group laws), one can only prove the latter. -/
@[to_additive "Sometimes, an additive group is defined as a quotient of a monoid
  by an additive congruence relation.
  Usually, the inverse operation is defined as `Setoid.map f _` for some `f`.
  This lemma allows to avoid code duplication in the definition of the inverse operation:
  instead of proving both `∀ x y, c x y → c (f x) (f y)` (to define the operation)
  and `∀ x, c (f x + x) 0` (to prove the group laws), one can only prove the latter."]
theorem map_of_mul_left_rel_one [Monoid M] (c : Con M)
    (f : M → M) (hf : ∀ x, c (f x * x) 1) {x y} (h : c x y) : c (f x) (f y) := by
  simp only [← Con.eq, coe_one, coe_mul] at *
  have hf' : ∀ x : M, (x : c.Quotient) * f x = 1 := fun x ↦
    calc
      (x : c.Quotient) * f x = f (f x) * f x * (x * f x) := by simp [hf]
      _ = f (f x) * (f x * x) * f x := by ac_rfl
      _ = 1 := by simp [hf]
  have : (⟨_, _, hf' x, hf x⟩ : c.Quotientˣ) = ⟨_, _, hf' y, hf y⟩ := Units.ext h
  exact congr_arg Units.inv this

end Monoids

section Groups

variable [Group M] [Group N] [Group P] (c : Con M)

/-- Multiplicative congruence relations preserve inversion. -/
@[to_additive "Additive congruence relations preserve negation."]
protected theorem inv {x y} (h : c x y) : c x⁻¹ y⁻¹ :=
  c.map_of_mul_left_rel_one Inv.inv (fun x => by simp only [mul_left_inv, c.refl 1]) h

/-- Multiplicative congruence relations preserve division. -/
@[to_additive "Additive congruence relations preserve subtraction."]
protected theorem div : ∀ {w x y z}, c w x → c y z → c (w / y) (x / z) := @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)

/-- Multiplicative congruence relations preserve integer powers. -/
@[to_additive "Additive congruence relations preserve integer scaling."]
protected theorem zpow : ∀ (n : ℤ) {w x}, c w x → c (w ^ n) (x ^ n)
  | Int.ofNat n, w, x, h => by simpa only [zpow_natCast, Int.ofNat_eq_coe] using c.pow n h
  | Int.negSucc n, w, x, h => by simpa only [zpow_negSucc] using c.inv (c.pow _ h)

/-- The inversion induced on the quotient by a congruence relation on a type with an
    inversion. -/
@[to_additive "The negation induced on the quotient by an additive congruence relation on a type
with a negation."]
instance hasInv : Inv c.Quotient :=
  ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv⟩

/-- The division induced on the quotient by a congruence relation on a type with a
    division. -/
@[to_additive "The subtraction induced on the quotient by an additive congruence relation on a type
with a subtraction."]
instance hasDiv : Div c.Quotient :=
  ⟨(Quotient.map₂' (· / ·)) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩

/-- The integer scaling induced on the quotient by a congruence relation on a type with a
    subtraction. -/
instance _root_.AddCon.Quotient.zsmul {M : Type*} [AddGroup M] (c : AddCon M) :
    SMul ℤ c.Quotient :=
  ⟨fun z => (Quotient.map' (z • ·)) fun _ _ => c.zsmul z⟩

/-- The integer power induced on the quotient by a congruence relation on a type with a
    division. -/
@[to_additive existing AddCon.Quotient.zsmul]
instance zpowinst : Pow c.Quotient ℤ :=
  ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow z h) x⟩

/-- The quotient of a group by a congruence relation is a group. -/
@[to_additive "The quotient of an `AddGroup` by an additive congruence relation is
an `AddGroup`."]
instance group : Group c.Quotient :=
  { (Function.Surjective.group Quotient.mk''
      Quotient.surjective_Quotient_mk'' rfl (fun _ _ => rfl) (fun _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl : Group c.Quotient) with
    toMonoid := Con.monoid _
    toInv := Con.hasInv _
    toDiv := Con.hasDiv _ }

end Groups

section Units

variable {α : Type*} [Monoid M] {c : Con M}

/-- In order to define a function `(Con.Quotient c)ˣ → α` on the units of `Con.Quotient c`,
where `c : Con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
@[to_additive]
def liftOnUnits (u : Units c.Quotient) (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx',
      c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx') : α := by
  refine
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 → y * x = 1 → α) (u : c.Quotient)
      (↑u⁻¹ : c.Quotient)
      (fun (x y : M) (hxy : (x * y : c.Quotient) = 1) (hyx : (y * x : c.Quotient) = 1) =>
        f x y (c.eq.1 hxy) (c.eq.1 hyx))
      (fun x y x' y' hx hy => ?_) u.3 u.4
  refine Function.hfunext ?_ ?_
  · rw [c.eq.2 hx, c.eq.2 hy]
  · rintro Hxy Hxy' -
    refine Function.hfunext ?_ ?_
    · rw [c.eq.2 hx, c.eq.2 hy]
    · rintro Hyx Hyx' -
      exact heq_of_eq (Hf _ _ _ _ _ _ _ _ hx hy)

/-- In order to define a function `(Con.Quotient c)ˣ → α` on the units of `Con.Quotient c`,
where `c : Con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
add_decl_doc AddCon.liftOnAddUnits

@[to_additive (attr := simp)]
theorem liftOnUnits_mk (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx', c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx')
    (x y : M) (hxy hyx) :
    liftOnUnits ⟨(x : c.Quotient), y, hxy, hyx⟩ f Hf = f x y (c.eq.1 hxy) (c.eq.1 hyx) :=
  rfl

@[to_additive (attr := elab_as_elim)]
theorem induction_on_units {p : Units c.Quotient → Prop} (u : Units c.Quotient)
    (H : ∀ (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x) 1), p ⟨x, y, c.eq.2 hxy, c.eq.2 hyx⟩) :
    p u := by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)

end Units

section Actions

@[to_additive]
instance instSMul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) :
    SMul α c.Quotient where
  smul a := (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]
theorem coe_smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
    (a : α) (x : M) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl

@[to_additive]
instance mulAction {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
    (c : Con M) : MulAction α c.Quotient where
  one_smul := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| one_smul _ _
  mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| mul_smul _ _ _

instance mulDistribMulAction {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulAction α M]
    [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient :=
  { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
    smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul' _ _ _ }

end Actions

end Con
