/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.AdaptationNote
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex

/-!
# Free constructions

## Main definitions

* `FreeMagma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `MagmaAssocQuotient α`: quotient of a magma `α` by the associativity equivalence relation.
* `FreeSemigroup α`: free semigroup over alphabet `α`, defined as a structure with two fields
  `head : α` and `tail : List α` (i.e. nonempty lists), with traversable instance and decidable
  equality.
* `FreeMagmaAssocQuotientEquiv α`: isomorphism between `MagmaAssocQuotient (FreeMagma α)` and
  `FreeSemigroup α`.
* `FreeMagma.lift`: the universal property of the free magma, expressing its adjointness.
-/

universe u v l

-- Disable generation of `sizeOf_spec` and `injEq`,
-- which are not needed and the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Free nonabelian additive magma over a given alphabet. -/
inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma α
  | add : FreeAddMagma α → FreeAddMagma α → FreeAddMagma α
  deriving DecidableEq
compile_inductive% FreeAddMagma

-- Disable generation of `sizeOf_spec` and `injEq`,
-- which are not needed and the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Free magma over a given alphabet. -/
@[to_additive]
inductive FreeMagma (α : Type u) : Type u
  | of : α → FreeMagma α
  | mul : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq
compile_inductive% FreeMagma

namespace FreeMagma

variable {α : Type u}

@[to_additive]
instance [Inhabited α] : Inhabited (FreeMagma α) := ⟨of default⟩

@[to_additive]
instance : Mul (FreeMagma α) := ⟨FreeMagma.mul⟩

@[to_additive (attr := simp)]
theorem mul_eq (x y : FreeMagma α) : mul x y = x * y := rfl

/-- Recursor for `FreeMagma` using `x * y` instead of `FreeMagma.mul x y`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
  "Recursor for `FreeAddMagma` using `x + y` instead of `FreeAddMagma.add x y`."]
def recOnMul {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOn x ih1 ih2

@[to_additive (attr := ext 1100)]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeMagma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (DFunLike.ext _ _) fun x ↦ recOnMul x (congr_fun h) <| by intros; simp only [map_mul, *]

end FreeMagma

/-- Lifts a function `α → β` to a magma homomorphism `FreeMagma α → β` given a magma `β`. -/
def FreeMagma.liftAux {α : Type u} {β : Type v} [Mul β] (f : α → β) : FreeMagma α → β
  | FreeMagma.of x => f x
  | x * y => liftAux f x * liftAux f y

/-- Lifts a function `α → β` to an additive magma homomorphism `FreeAddMagma α → β` given
an additive magma `β`. -/
def FreeAddMagma.liftAux {α : Type u} {β : Type v} [Add β] (f : α → β) : FreeAddMagma α → β
  | FreeAddMagma.of x => f x
  | x + y => liftAux f x + liftAux f y

attribute [to_additive existing] FreeMagma.liftAux

namespace FreeMagma

section lift

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

/-- The universal property of the free magma expressing its adjointness. -/
@[to_additive (attr := simps symm_apply)
"The universal property of the free additive magma expressing its adjointness."]
def lift : (α → β) ≃ (FreeMagma α →ₙ* β) where
  toFun f :=
  { toFun := liftAux f
    map_mul' := fun _ _ ↦ rfl }
  invFun F := F ∘ of
  left_inv _ := rfl
  right_inv F := by ext; rfl

@[to_additive (attr := simp)]
theorem lift_of (x) : lift f (of x) = f x := rfl

@[to_additive (attr := simp)]
theorem lift_comp_of : lift f ∘ of = f := rfl

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : FreeMagma α →ₙ* β) : lift (f ∘ of) = f := lift.apply_symm_apply f

end lift

section Map

variable {α : Type u} {β : Type v} (f : α → β)

/-- The unique magma homomorphism `FreeMagma α →ₙ* FreeMagma β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive magma homomorphism `FreeAddMagma α → FreeAddMagma β` that sends
each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMagma α →ₙ* FreeMagma β := lift (of ∘ f)

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl

end Map

section Category

variable {α β : Type u}

@[to_additive]
instance : Monad FreeMagma where
  pure := of
  bind x f := lift f x

/-- Recursor on `FreeMagma` using `pure` instead of `of`. -/
@[to_additive (attr := elab_as_elim) "Recursor on `FreeAddMagma` using `pure` instead of `of`."]
protected def recOnPure {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOnMul x ih1 ih2

@[to_additive (attr := simp)]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) := rfl

@[to_additive (attr := simp)]
theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y := rfl

@[to_additive (attr := simp)]
theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x := rfl

@[to_additive (attr := simp)]
theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl

@[to_additive (attr := simp)]
theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x := rfl

@[to_additive (attr := simp)]
theorem mul_seq {α β : Type u} {f g : FreeMagma (α → β)} {x : FreeMagma α} :
    f * g <*> x = (f <*> x) * (g <*> x) := rfl

@[to_additive]
instance instLawfulMonad : LawfulMonad FreeMagma.{u} := LawfulMonad.mk'
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun x f g ↦ FreeMagma.recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
    rw [mul_bind, mul_bind, mul_bind, ih1, ih2])
  (id_map := fun x ↦ FreeMagma.recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
    rw [map_mul', ih1, ih2])

end Category

end FreeMagma

/-- `FreeMagma` is traversable. -/
protected def FreeMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeMagma α → m (FreeMagma β)
  | FreeMagma.of x => FreeMagma.of <$> F x
  | x * y => (· * ·) <$> x.traverse F <*> y.traverse F

/-- `FreeAddMagma` is traversable. -/
protected def FreeAddMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeAddMagma α → m (FreeAddMagma β)
  | FreeAddMagma.of x => FreeAddMagma.of <$> F x
  | x + y => (· + ·) <$> x.traverse F <*> y.traverse F

attribute [to_additive existing] FreeMagma.traverse

namespace FreeMagma

variable {α : Type u}

section Category

variable {β : Type u}

@[to_additive]
instance : Traversable FreeMagma := ⟨@FreeMagma.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

@[to_additive (attr := simp)]
theorem traverse_pure (x) : traverse F (pure x : FreeMagma α) = pure <$> F x := rfl

@[to_additive (attr := simp)]
theorem traverse_pure' : traverse F ∘ pure = fun x ↦ (pure <$> F x : m (FreeMagma β)) := rfl

@[to_additive (attr := simp)]
theorem traverse_mul (x y : FreeMagma α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y := rfl

@[to_additive (attr := simp)]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeMagma α → FreeMagma α → FreeMagma α) = fun x y ↦
      (· * ·) <$> traverse F x <*> traverse F y := rfl

@[to_additive (attr := simp)]
theorem traverse_eq (x) : FreeMagma.traverse F x = traverse F x := rfl

-- This is not a simp lemma because the left-hand side is not in simp normal form.
@[to_additive]
theorem mul_map_seq (x y : FreeMagma α) :
    ((· * ·) <$> x <*> y : Id (FreeMagma α)) = (x * y : FreeMagma α) := rfl

@[to_additive]
instance : LawfulTraversable FreeMagma.{u} :=
  { instLawfulMonad with
    id_traverse := fun x ↦
      FreeMagma.recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun f g x ↦
      FreeMagma.recOnPure x
        (fun x ↦ by simp only [Function.comp_def, traverse_pure, traverse_pure', functor_norm])
        (fun x y ih1 ih2 ↦ by
          rw [traverse_mul, ih1, ih2, traverse_mul]
          simp [Functor.Comp.map_mk, Functor.map_map, Function.comp_def, Comp.seq_mk, seq_map_assoc,
            map_seq, traverse_mul])
    naturality := fun η α β f x ↦
      FreeMagma.recOnPure x
        (fun x ↦ by simp only [traverse_pure, functor_norm, Function.comp_apply])
        (fun x y ih1 ih2 ↦ by simp only [traverse_mul, functor_norm, ih1, ih2])
    traverse_eq_map_id := fun f x ↦
      FreeMagma.recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; rfl }

end Category

end FreeMagma

/-- Representation of an element of a free magma. -/
protected def FreeMagma.repr {α : Type u} [Repr α] : FreeMagma α → Lean.Format
  | FreeMagma.of x => repr x
  | x * y => "( " ++ x.repr ++ " * " ++ y.repr ++ " )"

/-- Representation of an element of a free additive magma. -/
protected def FreeAddMagma.repr {α : Type u} [Repr α] : FreeAddMagma α → Lean.Format
  | FreeAddMagma.of x => repr x
  | x + y => "( " ++ x.repr ++ " + " ++ y.repr ++ " )"

attribute [to_additive existing] FreeMagma.repr

@[to_additive]
instance {α : Type u} [Repr α] : Repr (FreeMagma α) := ⟨fun o _ => FreeMagma.repr o⟩

/-- Length of an element of a free magma. -/
def FreeMagma.length {α : Type u} : FreeMagma α → ℕ
  | FreeMagma.of _x => 1
  | x * y => x.length + y.length

/-- Length of an element of a free additive magma. -/
def FreeAddMagma.length {α : Type u} : FreeAddMagma α → ℕ
  | FreeAddMagma.of _x => 1
  | x + y => x.length + y.length

attribute [to_additive existing (attr := simp)] FreeMagma.length

/-- The length of an element of a free magma is positive. -/
@[to_additive "The length of an element of a free additive magma is positive."]
lemma FreeMagma.length_pos {α : Type u} (x : FreeMagma α) : 0 < x.length :=
  match x with
  | FreeMagma.of _ => Nat.succ_pos 0
  | mul y z => Nat.add_pos_left (length_pos y) z.length

/-- Associativity relations for an additive magma. -/
inductive AddMagma.AssocRel (α : Type u) [Add α] : α → α → Prop
  | intro : ∀ x y z, AddMagma.AssocRel α (x + y + z) (x + (y + z))
  | left : ∀ w x y z, AddMagma.AssocRel α (w + (x + y + z)) (w + (x + (y + z)))

/-- Associativity relations for a magma. -/
@[to_additive AddMagma.AssocRel "Associativity relations for an additive magma."]
inductive Magma.AssocRel (α : Type u) [Mul α] : α → α → Prop
  | intro : ∀ x y z, Magma.AssocRel α (x * y * z) (x * (y * z))
  | left : ∀ w x y z, Magma.AssocRel α (w * (x * y * z)) (w * (x * (y * z)))

namespace Magma

/-- Semigroup quotient of a magma. -/
@[to_additive AddMagma.FreeAddSemigroup "Additive semigroup quotient of an additive magma."]
def AssocQuotient (α : Type u) [Mul α] : Type u :=
  Quot <| AssocRel α

namespace AssocQuotient

variable {α : Type u} [Mul α]

@[to_additive]
theorem quot_mk_assoc (x y z : α) : Quot.mk (AssocRel α) (x * y * z) = Quot.mk _ (x * (y * z)) :=
  Quot.sound (AssocRel.intro _ _ _)

@[to_additive]
theorem quot_mk_assoc_left (x y z w : α) :
    Quot.mk (AssocRel α) (x * (y * z * w)) = Quot.mk _ (x * (y * (z * w))) :=
  Quot.sound (AssocRel.left _ _ _ _)

@[to_additive]
instance : Semigroup (AssocQuotient α) where
  mul x y := by
    refine Quot.liftOn₂ x y (fun x y ↦ Quot.mk _ (x * y)) ?_ ?_
    · rintro a b₁ b₂ (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · exact quot_mk_assoc_left _ _ _ _
      · rw [← quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc]
    · rintro a₁ a₂ b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · simp only [quot_mk_assoc, quot_mk_assoc_left]
      · rw [quot_mk_assoc, quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc_left,
          quot_mk_assoc_left, ← quot_mk_assoc c d, ← quot_mk_assoc c d, quot_mk_assoc_left]
  mul_assoc x y z :=
    Quot.induction_on₃ x y z fun a b c ↦ quot_mk_assoc a b c

/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α →ₙ* AssocQuotient α where toFun := Quot.mk _; map_mul' _x _y := rfl

@[to_additive]
instance [Inhabited α] : Inhabited (AssocQuotient α) := ⟨of default⟩

@[to_additive (attr := elab_as_elim, induction_eliminator)]
protected theorem induction_on {C : AssocQuotient α → Prop} (x : AssocQuotient α)
    (ih : ∀ x, C (of x)) : C x := Quot.induction_on x ih

section lift

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

@[to_additive (attr := ext 1100)]
theorem hom_ext {f g : AssocQuotient α →ₙ* β} (h : f.comp of = g.comp of) : f = g :=
  (DFunLike.ext _ _) fun x => AssocQuotient.induction_on x <| DFunLike.congr_fun h

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `Magma.AssocQuotient α → β`
given a semigroup `β`. -/
@[to_additive (attr := simps symm_apply) "Lifts an additive magma homomorphism `α → β` to an
additive semigroup homomorphism `AddMagma.AssocQuotient α → β` given an additive semigroup `β`."]
def lift : (α →ₙ* β) ≃ (AssocQuotient α →ₙ* β) where
  toFun f :=
  { toFun := fun x ↦
      Quot.liftOn x f <| by rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only [map_mul, mul_assoc]
    map_mul' := fun x y ↦ Quot.induction_on₂ x y (map_mul f) }
  invFun f := f.comp of
  left_inv _ := (DFunLike.ext _ _) fun _ ↦ rfl
  right_inv _ := hom_ext <| (DFunLike.ext _ _) fun _ ↦ rfl

@[to_additive (attr := simp)]
theorem lift_of (x : α) : lift f (of x) = f x := rfl

@[to_additive (attr := simp)]
theorem lift_comp_of : (lift f).comp of = f := lift.symm_apply_apply f

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : AssocQuotient α →ₙ* β) : lift (f.comp of) = f := lift.apply_symm_apply f

end lift

variable {β : Type v} [Mul β] (f : α →ₙ* β)

/-- From a magma homomorphism `α →ₙ* β` to a semigroup homomorphism
`Magma.AssocQuotient α →ₙ* Magma.AssocQuotient β`. -/
@[to_additive "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`AddMagma.AssocQuotient α → AddMagma.AssocQuotient β`."]
def map : AssocQuotient α →ₙ* AssocQuotient β := lift (of.comp f)

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl

end AssocQuotient

end Magma

/-- Free additive semigroup over a given alphabet. -/
structure FreeAddSemigroup (α : Type u) where
  /-- The head of the element -/
  head : α
  /-- The tail of the element -/
  tail : List α
compile_inductive% FreeAddSemigroup

/-- Free semigroup over a given alphabet. -/
@[to_additive (attr := ext)]
structure FreeSemigroup (α : Type u) where
  /-- The head of the element -/
  head : α
  /-- The tail of the element -/
  tail : List α
compile_inductive% FreeSemigroup

namespace FreeSemigroup

variable {α : Type u}

@[to_additive]
instance : Semigroup (FreeSemigroup α) where
  mul L1 L2 := ⟨L1.1, L1.2 ++ L2.1 :: L2.2⟩
  mul_assoc _L1 _L2 _L3 := FreeSemigroup.ext rfl <| List.append_assoc _ _ _

@[to_additive (attr := simp)]
theorem head_mul (x y : FreeSemigroup α) : (x * y).1 = x.1 := rfl

@[to_additive (attr := simp)]
theorem tail_mul (x y : FreeSemigroup α) : (x * y).2 = x.2 ++ y.1 :: y.2 := rfl

@[to_additive (attr := simp)]
theorem mk_mul_mk (x y : α) (L1 L2 : List α) : mk x L1 * mk y L2 = mk x (L1 ++ y :: L2) := rfl

/-- The embedding `α → FreeSemigroup α`. -/
@[to_additive (attr := simps) "The embedding `α → FreeAddSemigroup α`."]
def of (x : α) : FreeSemigroup α := ⟨x, []⟩

/-- Length of an element of free semigroup. -/
@[to_additive "Length of an element of free additive semigroup"]
def length (x : FreeSemigroup α) : ℕ := x.tail.length + 1

@[to_additive (attr := simp)]
theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [length, Nat.add_right_comm, List.length, List.length_append]

@[to_additive (attr := simp)]
theorem length_of (x : α) : (of x).length = 1 := rfl

@[to_additive]
theorem length_lt_zero {α : Type u} (x : FreeSemigroup α) : x.length > 0 := Nat.zero_lt_succ _

@[to_additive]
theorem length_factor_lt_left {α : Type u} (x y : FreeSemigroup α) :
    x.length < (x * y).length := by
  rw [length_mul, Nat.lt_add_right_iff_pos]
  exact length_lt_zero _

@[to_additive]
theorem length_factor_lt_right {α : Type u} (x y : FreeSemigroup α) :
    y.length < (x * y).length := by
  rw [length_mul, Nat.lt_add_left_iff_pos]
  exact length_lt_zero _

/--
  converts a nonempty list to a free semi group.
-/
@[to_additive "converts a nonempty list to a free additive semi group."]
def fromList {α : Type u}  (l : List α) (h : ¬l.isEmpty) : FreeSemigroup α :=
  match l with
  | a :: l => if h : l.isEmpty then of a else of a * fromList l h

@[to_additive (attr := simp)]
def fromList_head {α : Type u} (l : List α) (h : ¬l.isEmpty) :
    (fromList l h).head = l.head
      (Ne.symm (ne_of_apply_ne List.isEmpty fun a ↦ h (id (Eq.symm a)))
    ) := by
  match l with
  | a :: l =>
    simp only [fromList, List.isEmpty_eq_true, List.head_cons]
    rw [apply_dite head]
    simp only [List.isEmpty_eq_true, of_head, head_mul, dite_eq_ite, ite_self]

@[to_additive (attr := simp)]
def fromList_tail {α : Type u} (l : List α) (h : ¬l.isEmpty) :
    (fromList l h).tail = l.tail := by
  match l with
  | a :: l' =>
    simp only [fromList, List.isEmpty_eq_true, List.tail_cons]
    rw [apply_dite tail]
    simp only [List.isEmpty_eq_true, of_tail, tail_mul, fromList_head, List.nil_append]
    by_cases h : l'.isEmpty
    · simp only [h, ↓reduceDIte, List.nil_eq]
      exact List.isEmpty_iff.mp h
    · simp only [h, Bool.false_eq_true, ↓reduceDIte]
      rw [fromList_tail]
      simp only [List.head_cons_tail]

@[to_additive (attr := simp)]
theorem fromList_singleton {α : Type u} (a : α) {h : ¬[a].isEmpty} : fromList [a] h = of a := rfl

@[to_additive (attr := simp)]
theorem fromList_length {α : Type u} (l : List α) (h : ¬l.isEmpty) :
    (fromList l h).length = l.length :=
  match l with
  | a :: l => if h : l.isEmpty then (
    by
      simp only [fromList, h, List.isEmpty_eq_true, List.length_cons]
      exact Nat.self_eq_add_left.mpr <| List.isEmpty_iff_length_eq_zero.mp h
  ) else (by
    simp only [fromList, h, Bool.false_eq_true,
    ↓reduceDIte, length_mul, length_of, List.length_cons]
    rw [Nat.add_comm]
    exact congr_arg₂ _ (fromList_length l h) rfl
  )

@[to_additive (attr := simp)]
theorem fromList_cons {α : Type u} (a : α) (l : List α) :
    fromList (a :: l) (ne_true_of_eq_false rfl)
      = if h : l.isEmpty then of a else of a * fromList l h := rfl

@[to_additive (attr := simp)]
theorem fromList_append {α : Type u} (l₁ l₂ : List α) (h₁ : ¬l₁.isEmpty) (h₂ : ¬l₂.isEmpty) :
    fromList (l₁ ++ l₂) (by
      simp_all only [List.isEmpty_eq_true, List.append_eq_nil_iff, and_self, not_false_eq_true]
    ) = fromList l₁ h₁ * fromList l₂ h₂ := by
  match l₁ with
  | x :: xs =>
    simp only [List.cons_append, fromList_cons]
    have : (xs ++ l₂).isEmpty = false := by
      simp only [List.isEmpty_eq_false, ne_eq, List.append_eq_nil_iff, not_and]
      intro a
      subst a
      simp_all only [List.isEmpty_eq_true, List.isEmpty_cons, Bool.false_eq_true, not_false_eq_true]
    by_cases h' : xs.isEmpty <;> simp only [this, List.isEmpty_eq_true, List.append_eq_nil_iff, h',
      Bool.false_eq_true, ↓reduceDIte]
    · simp only [List.isEmpty_eq_true] at h'
      simp only [h', List.nil_append]
    · rw [mul_assoc]
      apply congr_arg₂ _ rfl
      exact fromList_append _ _ _ _

/--
  converts a free semigroup to a list.
-/
@[to_additive "converts a free additive semigroup to a list."]
def toList {α : Type u} : FreeSemigroup α → List α := fun x => x.head :: x.tail

@[to_additive (attr := simp)]
theorem toList_of {α : Type u} (a : α) : toList (of a) = [a] := rfl

@[to_additive (attr := simp)]
theorem toList_mul {α : Type u} (x y : FreeSemigroup α) :
  toList (x * y) = toList x ++ toList y := rfl

@[to_additive (attr := simp)]
theorem toList_length {α : Type u} (x : FreeSemigroup α) :
  x.toList.length = x.length := rfl

@[to_additive]
theorem toList_nonEmpty {α : Type u} (x : FreeSemigroup α) : ¬x.toList.isEmpty := by
  rw [toList]
  simp only [List.isEmpty_cons, Bool.false_eq_true, not_false_eq_true]

@[to_additive (attr := simp)]
theorem fromList_toList {α : Type u} (x : FreeSemigroup α) :
    fromList (toList x) (toList_nonEmpty x) = x := by
  simp only [toList, fromList, List.isEmpty_eq_true]
  by_cases h : x.tail.isEmpty <;> simp only [h, Bool.false_eq_true, ↓reduceDIte]
  · rw [List.isEmpty_iff] at h
    exact FreeSemigroup.ext rfl (id (Eq.symm h))
  · apply FreeSemigroup.ext
    · simp only [head_mul, of_head]
    · simp only [tail_mul, of_tail, List.nil_append]
      set y := x.tail with hy
      simp only [<- hy]
      match y with
      | a :: l =>
        simp only [fromList_cons, List.isEmpty_eq_true, List.cons.injEq]
        by_cases h : l.isEmpty
        · simp only [h, ↓reduceDIte, of_head, of_tail, List.nil_eq, true_and]
          exact List.isEmpty_iff.mp h
        · simp only [h, Bool.false_eq_true, ↓reduceDIte, head_mul, of_head, tail_mul, of_tail,
          fromList_head, fromList_tail, List.head_cons_tail, List.nil_append, and_self]

@[to_additive]
theorem toList_injective {α : Type u} : Function.Injective (toList : FreeSemigroup α → List α) := by
  intro x y h
  rw [← fromList_toList x, ← fromList_toList y]
  simp only [h, fromList_toList]

/--
  defines a lexicographic order on free semi group.
  Not a default instance because it should be better to declare it explicitly.
-/
@[to_additive "defines a lexicographic order on free additive semi group.
  Not a default instance because it should be better to declare it explicitly."]
def instLinearOrder [LinearOrder α] : LinearOrder (FreeSemigroup α) :=
  LinearOrder.lift' (toList : FreeSemigroup α → List α) toList_injective


@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) := ⟨of default⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
  "Recursor for free additive semigroup using `of` and `+`."]
protected def recOnMul {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
      FreeSemigroup.recOn x fun f s ↦
      List.recOn s ih1 (fun hd tl ih f ↦ ih2 f ⟨hd, tl⟩ (ih1 f) (ih hd)) f

@[to_additive (attr := ext 1100)]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeSemigroup α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (DFunLike.ext _ _) fun x ↦
    FreeSemigroup.recOnMul x (congr_fun h) fun x y hx hy ↦ by simp only [map_mul, *]

section lift

variable {β : Type v} [Semigroup β] (f : α → β)

/-- Lifts a function `α → β` to a semigroup homomorphism `FreeSemigroup α → β` given
a semigroup `β`. -/
@[to_additive (attr := simps symm_apply) "Lifts a function `α → β` to an additive semigroup
homomorphism `FreeAddSemigroup α → β` given an additive semigroup `β`."]
def lift : (α → β) ≃ (FreeSemigroup α →ₙ* β) where
  toFun f :=
    { toFun := fun x ↦ x.2.foldl (fun a b ↦ a * f b) (f x.1)
      map_mul' := fun x y ↦ by
        simp [head_mul, tail_mul, ← List.foldl_map, List.foldl_append, List.foldl_cons,
          List.foldl_assoc] }
  invFun f := f ∘ of
  left_inv _ := rfl
  right_inv _ := hom_ext rfl

@[to_additive (attr := simp)]
theorem lift_of (x : α) : lift f (of x) = f x := rfl

@[to_additive (attr := simp)]
theorem lift_comp_of : lift f ∘ of = f := rfl

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : FreeSemigroup α →ₙ* β) : lift (f ∘ of) = f := hom_ext rfl

@[to_additive]
theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := by rw [map_mul, lift_of]

end lift

section Map

variable {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : FreeSemigroup α →ₙ* FreeSemigroup β :=
  lift <| of ∘ f

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl

@[to_additive (attr := simp)]
theorem length_map (x) : (map f x).length = x.length :=
  FreeSemigroup.recOnMul x (fun _ ↦ rfl) (fun x y hx hy ↦ by simp only [map_mul, length_mul, *])

end Map

section Category

variable {β : Type u}

@[to_additive]
instance : Monad FreeSemigroup where
  pure := of
  bind x f := lift f x

/-- Recursor that uses `pure` instead of `of`. -/
@[to_additive (attr := elab_as_elim) "Recursor that uses `pure` instead of `of`."]
def recOnPure {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) : C x :=
  FreeSemigroup.recOnMul x ih1 ih2

@[to_additive (attr := simp)]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) := rfl

@[to_additive (attr := simp)]
theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul (map f) _ _

@[to_additive (attr := simp)]
theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x := rfl

@[to_additive (attr := simp)]
theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) :
    x * y >>= f = (x >>= f) * (y >>= f) := map_mul (lift f) _ _

@[to_additive (attr := simp)]
theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x := rfl

@[to_additive (attr := simp)]
theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} :
    f * g <*> x = (f <*> x) * (g <*> x) := mul_bind _ _ _

@[to_additive]
instance instLawfulMonad : LawfulMonad FreeSemigroup.{u} := LawfulMonad.mk'
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun x g f ↦
    recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by rw [mul_bind, mul_bind, mul_bind, ih1, ih2])
  (id_map := fun x ↦ recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by rw [map_mul', ih1, ih2])

/-- `FreeSemigroup` is traversable. -/
@[to_additive "`FreeAddSemigroup` is traversable."]
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) (x : FreeSemigroup α) : m (FreeSemigroup β) :=
  recOnPure x (fun x ↦ pure <$> F x) fun _x _y ihx ihy ↦ (· * ·) <$> ihx <*> ihy

@[to_additive]
instance : Traversable FreeSemigroup := ⟨@FreeSemigroup.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

@[to_additive (attr := simp)]
theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x := rfl

@[to_additive (attr := simp)]
theorem traverse_pure' : traverse F ∘ pure = fun x ↦ (pure <$> F x : m (FreeSemigroup β)) := rfl

section

variable [LawfulApplicative m]

@[to_additive (attr := simp)]
theorem traverse_mul (x y : FreeSemigroup α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun _ ↦ rfl)
    (fun hd tl ih x ↦ show
        (· * ·) <$> pure <$> F x <*> traverse F (mk hd tl * mk y L2) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (mk hd tl)) <*> traverse F (mk y L2)
        by rw [ih]; simp only [Function.comp_def, (mul_assoc _ _ _).symm, functor_norm])
    x

@[to_additive (attr := simp)]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeSemigroup α → FreeSemigroup α → FreeSemigroup α) =
      fun x y ↦ (· * ·) <$> traverse F x <*> traverse F y :=
  funext fun x ↦ funext fun y ↦ traverse_mul F x y

end

@[to_additive (attr := simp)]
theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x := rfl

-- This is not a simp lemma because the left-hand side is not in simp normal form.
@[to_additive]
theorem mul_map_seq (x y : FreeSemigroup α) :
    ((· * ·) <$> x <*> y : Id (FreeSemigroup α)) = (x * y : FreeSemigroup α) := rfl

@[to_additive]
instance : LawfulTraversable FreeSemigroup.{u} :=
  { instLawfulMonad with
    id_traverse := fun x ↦
      FreeSemigroup.recOnMul x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun f g x ↦
      recOnPure x (fun x ↦ by simp only [traverse_pure, functor_norm, Function.comp_def])
        fun x y ih1 ih2 ↦ by
          rw [traverse_mul, ih1, ih2, traverse_mul, Functor.Comp.map_mk]
          simp only [Function.comp_def, functor_norm, traverse_mul]
    naturality := fun η α β f x ↦
      recOnPure x (fun x ↦ by simp only [traverse_pure, functor_norm, Function.comp])
          (fun x y ih1 ih2 ↦ by simp only [traverse_mul, functor_norm, ih1, ih2])
    traverse_eq_map_id := fun f x ↦
      FreeSemigroup.recOnMul x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; rfl }

end Category

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeSemigroup α) :=
  fun _ _ ↦ decidable_of_iff' _ FreeSemigroup.ext_iff

end FreeSemigroup

namespace FreeMagma

variable {α : Type u} {β : Type v}

/-- The canonical multiplicative morphism from `FreeMagma α` to `FreeSemigroup α`. -/
@[to_additive "The canonical additive morphism from `FreeAddMagma α` to `FreeAddSemigroup α`."]
def toFreeSemigroup : FreeMagma α →ₙ* FreeSemigroup α := FreeMagma.lift FreeSemigroup.of

@[to_additive (attr := simp)]
theorem toFreeSemigroup_of (x : α) : toFreeSemigroup (of x) = FreeSemigroup.of x := rfl

@[to_additive (attr := simp)]
theorem toFreeSemigroup_comp_of : @toFreeSemigroup α ∘ of = FreeSemigroup.of := rfl

@[to_additive]
theorem toFreeSemigroup_comp_map (f : α → β) :
    toFreeSemigroup.comp (map f) = (FreeSemigroup.map f).comp toFreeSemigroup := by ext1; rfl

@[to_additive]
theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    toFreeSemigroup (map f x) = FreeSemigroup.map f (toFreeSemigroup x) :=
  DFunLike.congr_fun (toFreeSemigroup_comp_map f) x

@[to_additive (attr := simp)]
theorem length_toFreeSemigroup (x : FreeMagma α) : (toFreeSemigroup x).length = x.length :=
  FreeMagma.recOnMul x (fun _ ↦ rfl) fun x y hx hy ↦ by
    rw [map_mul, FreeSemigroup.length_mul, hx, hy]; rfl

end FreeMagma

/-- Isomorphism between `Magma.AssocQuotient (FreeMagma α)` and `FreeSemigroup α`. -/
@[to_additive "Isomorphism between `AddMagma.AssocQuotient (FreeAddMagma α)` and
`FreeAddSemigroup α`."]
def FreeMagmaAssocQuotientEquiv (α : Type u) :
    Magma.AssocQuotient (FreeMagma α) ≃* FreeSemigroup α :=
      (Magma.AssocQuotient.lift FreeMagma.toFreeSemigroup).toMulEquiv
      (FreeSemigroup.lift (Magma.AssocQuotient.of ∘ FreeMagma.of))
      (by ext; rfl)
      (by ext1; rfl)
