/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.WithOne.Basic

#align_import algebra.free from "leanprover-community/mathlib"@"6d0adfa76594f304b4650d098273d4366edeb61b"

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

/-- Free nonabelian additive magma over a given alphabet. -/
inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma α
  | add : FreeAddMagma α → FreeAddMagma α → FreeAddMagma α
  deriving DecidableEq
#align free_add_magma FreeAddMagma
compile_inductive% FreeAddMagma

/-- Free magma over a given alphabet. -/
@[to_additive]
inductive FreeMagma (α : Type u) : Type u
  | of : α → FreeMagma α
  | mul : FreeMagma α → FreeMagma α → FreeMagma α
  deriving DecidableEq
#align free_magma FreeMagma
compile_inductive% FreeMagma

namespace FreeMagma

variable {α : Type u}

@[to_additive]
instance [Inhabited α] : Inhabited (FreeMagma α) := ⟨of default⟩

@[to_additive]
instance : Mul (FreeMagma α) := ⟨FreeMagma.mul⟩

-- Porting note: invalid attribute 'match_pattern', declaration is in an imported module
-- attribute [match_pattern] Mul.mul

@[to_additive (attr := simp)]
theorem mul_eq (x y : FreeMagma α) : mul x y = x * y := rfl
#align free_magma.mul_eq FreeMagma.mul_eq

/- Porting note: these lemmas are autogenerated by the inductive definition and due to
the existence of mul_eq not in simp normal form -/
attribute [nolint simpNF] FreeAddMagma.add.sizeOf_spec
attribute [nolint simpNF] FreeMagma.mul.sizeOf_spec
attribute [nolint simpNF] FreeAddMagma.add.injEq
attribute [nolint simpNF] FreeMagma.mul.injEq

/-- Recursor for `FreeMagma` using `x * y` instead of `FreeMagma.mul x y`. -/
@[to_additive (attr := elab_as_elim) "Recursor for `FreeAddMagma` using `x + y` instead of
`FreeAddMagma.add x y`."]
def recOnMul {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOn x ih1 ih2
#align free_magma.rec_on_mul FreeMagma.recOnMul

@[to_additive (attr := ext 1100)]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeMagma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (DFunLike.ext _ _) fun x ↦ recOnMul x (congr_fun h) <| by intros; simp only [map_mul, *]
#align free_magma.hom_ext FreeMagma.hom_ext

end FreeMagma

/-- Lifts a function `α → β` to a magma homomorphism `FreeMagma α → β` given a magma `β`. -/
def FreeMagma.liftAux {α : Type u} {β : Type v} [Mul β] (f : α → β) : FreeMagma α → β
  | FreeMagma.of x => f x
  -- Adaptation note: around nightly-2024-02-25, we need to write `mul x y` in the pattern here,
  -- instead of `x * y`.
  | mul x y => liftAux f x * liftAux f y
#align free_magma.lift_aux FreeMagma.liftAux

/-- Lifts a function `α → β` to an additive magma homomorphism `FreeAddMagma α → β` given
an additive magma `β`. -/
def FreeAddMagma.liftAux {α : Type u} {β : Type v} [Add β] (f : α → β) : FreeAddMagma α → β
  | FreeAddMagma.of x => f x
  | x + y => liftAux f x + liftAux f y
#align free_add_magma.lift_aux FreeAddMagma.liftAux

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
    map_mul' := fun x y ↦ rfl }
  invFun F := F ∘ of
  left_inv f := rfl
  right_inv F := by ext; rfl
#align free_magma.lift FreeMagma.lift

@[to_additive (attr := simp)]
theorem lift_of (x) : lift f (of x) = f x := rfl
#align free_magma.lift_of FreeMagma.lift_of

@[to_additive (attr := simp)]
theorem lift_comp_of : lift f ∘ of = f := rfl
#align free_magma.lift_comp_of FreeMagma.lift_comp_of

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : FreeMagma α →ₙ* β) : lift (f ∘ of) = f := lift.apply_symm_apply f
#align free_magma.lift_comp_of' FreeMagma.lift_comp_of'

end lift

section Map

variable {α : Type u} {β : Type v} (f : α → β)

/-- The unique magma homomorphism `FreeMagma α →ₙ* FreeMagma β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive magma homomorphism `FreeAddMagma α → FreeAddMagma β` that sends
each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMagma α →ₙ* FreeMagma β := lift (of ∘ f)
#align free_magma.map FreeMagma.map

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl
#align free_magma.map_of FreeMagma.map_of

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
#align free_magma.rec_on_pure FreeMagma.recOnPure

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) := rfl
#align free_magma.map_pure FreeMagma.map_pure

@[to_additive (attr := simp)]
theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y := rfl
#align free_magma.map_mul' FreeMagma.map_mul'

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x := rfl
#align free_magma.pure_bind FreeMagma.pure_bind

@[to_additive (attr := simp)]
theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl
#align free_magma.mul_bind FreeMagma.mul_bind

@[to_additive (attr := simp)]
theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x := rfl
#align free_magma.pure_seq FreeMagma.pure_seq

@[to_additive (attr := simp)]
theorem mul_seq {α β : Type u} {f g : FreeMagma (α → β)} {x : FreeMagma α} :
    f * g <*> x = (f <*> x) * (g <*> x) := rfl
#align free_magma.mul_seq FreeMagma.mul_seq

@[to_additive]
instance instLawfulMonad : LawfulMonad FreeMagma.{u} := LawfulMonad.mk'
  (pure_bind := fun f x ↦ rfl)
  (bind_assoc := fun x f g ↦ FreeMagma.recOnPure x (fun x ↦ rfl) fun x y ih1 ih2 ↦ by
    rw [mul_bind, mul_bind, mul_bind, ih1, ih2])
  (id_map := fun x ↦ FreeMagma.recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
    rw [map_mul', ih1, ih2])

end Category

end FreeMagma

/-- `FreeMagma` is traversable. -/
protected def FreeMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeMagma α → m (FreeMagma β)
  | FreeMagma.of x => FreeMagma.of <$> F x
  -- Adaptation note: around nightly-2024-02-25, we need to write `mul x y` in the pattern here,
  -- instead of `x * y`.
  | mul x y => (· * ·) <$> x.traverse F <*> y.traverse F
#align free_magma.traverse FreeMagma.traverse

/-- `FreeAddMagma` is traversable. -/
protected def FreeAddMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) : FreeAddMagma α → m (FreeAddMagma β)
  | FreeAddMagma.of x => FreeAddMagma.of <$> F x
  | x + y => (· + ·) <$> x.traverse F <*> y.traverse F
#align free_add_magma.traverse FreeAddMagma.traverse

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
#align free_magma.traverse_pure FreeMagma.traverse_pure

@[to_additive (attr := simp)]
theorem traverse_pure' : traverse F ∘ pure = fun x ↦ (pure <$> F x : m (FreeMagma β)) := rfl
#align free_magma.traverse_pure' FreeMagma.traverse_pure'

@[to_additive (attr := simp)]
theorem traverse_mul (x y : FreeMagma α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y := rfl
#align free_magma.traverse_mul FreeMagma.traverse_mul

@[to_additive (attr := simp)]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeMagma α → FreeMagma α → FreeMagma α) = fun x y ↦
      (· * ·) <$> traverse F x <*> traverse F y := rfl
#align free_magma.traverse_mul' FreeMagma.traverse_mul'

@[to_additive (attr := simp)]
theorem traverse_eq (x) : FreeMagma.traverse F x = traverse F x := rfl
#align free_magma.traverse_eq FreeMagma.traverse_eq

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem mul_map_seq (x y : FreeMagma α) :
    ((· * ·) <$> x <*> y : Id (FreeMagma α)) = (x * y : FreeMagma α) := rfl
#align free_magma.mul_map_seq FreeMagma.mul_map_seq

@[to_additive]
instance : LawfulTraversable FreeMagma.{u} :=
  { instLawfulMonad with
    id_traverse := fun x ↦
      FreeMagma.recOnPure x (fun x ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun f g x ↦
      FreeMagma.recOnPure x
        (fun x ↦ by simp only [(· ∘ ·), traverse_pure, traverse_pure', functor_norm])
        (fun x y ih1 ih2 ↦ by
          rw [traverse_mul, ih1, ih2, traverse_mul];
          simp [Functor.Comp.map_mk, Functor.map_map, (· ∘ ·), Comp.seq_mk, seq_map_assoc,
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

-- Porting note: changed String to Lean.Format
/-- Representation of an element of a free magma. -/
protected def FreeMagma.repr {α : Type u} [Repr α] : FreeMagma α → Lean.Format
  | FreeMagma.of x => repr x
  -- Adaptation note: around nightly-2024-02-25, we need to write `mul x y` in the pattern here,
  -- instead of `x * y`.
  | mul x y => "( " ++ x.repr ++ " * " ++ y.repr ++ " )"
#align free_magma.repr FreeMagma.repr

/-- Representation of an element of a free additive magma. -/
protected def FreeAddMagma.repr {α : Type u} [Repr α] : FreeAddMagma α → Lean.Format
  | FreeAddMagma.of x => repr x
  | x + y => "( " ++ x.repr ++ " + " ++ y.repr ++ " )"
#align free_add_magma.repr FreeAddMagma.repr

attribute [to_additive existing] FreeMagma.repr

@[to_additive]
instance {α : Type u} [Repr α] : Repr (FreeMagma α) := ⟨fun o _ => FreeMagma.repr o⟩

/-- Length of an element of a free magma. -/
def FreeMagma.length {α : Type u} : FreeMagma α → ℕ
  | FreeMagma.of _x => 1
  -- Adaptation note: around nightly-2024-02-25, we need to write `mul x y` in the pattern here,
  -- instead of `x * y`.
  | mul x y => x.length + y.length
#align free_magma.length FreeMagma.length

/-- Length of an element of a free additive magma. -/
def FreeAddMagma.length {α : Type u} : FreeAddMagma α → ℕ
  | FreeAddMagma.of _x => 1
  | x + y => x.length + y.length
#align free_add_magma.length FreeAddMagma.length

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
#align add_magma.assoc_rel AddMagma.AssocRel

/-- Associativity relations for a magma. -/
@[to_additive AddMagma.AssocRel "Associativity relations for an additive magma."]
inductive Magma.AssocRel (α : Type u) [Mul α] : α → α → Prop
  | intro : ∀ x y z, Magma.AssocRel α (x * y * z) (x * (y * z))
  | left : ∀ w x y z, Magma.AssocRel α (w * (x * y * z)) (w * (x * (y * z)))
#align magma.assoc_rel Magma.AssocRel

namespace Magma

/-- Semigroup quotient of a magma. -/
@[to_additive AddMagma.FreeAddSemigroup "Additive semigroup quotient of an additive magma."]
def AssocQuotient (α : Type u) [Mul α] : Type u :=
  Quot <| AssocRel α
#align magma.assoc_quotient Magma.AssocQuotient

namespace AssocQuotient

variable {α : Type u} [Mul α]

@[to_additive]
theorem quot_mk_assoc (x y z : α) : Quot.mk (AssocRel α) (x * y * z) = Quot.mk _ (x * (y * z)) :=
  Quot.sound (AssocRel.intro _ _ _)
#align magma.assoc_quotient.quot_mk_assoc Magma.AssocQuotient.quot_mk_assoc

@[to_additive]
theorem quot_mk_assoc_left (x y z w : α) :
    Quot.mk (AssocRel α) (x * (y * z * w)) = Quot.mk _ (x * (y * (z * w))) :=
  Quot.sound (AssocRel.left _ _ _ _)
#align magma.assoc_quotient.quot_mk_assoc_left Magma.AssocQuotient.quot_mk_assoc_left

@[to_additive]
instance : Semigroup (AssocQuotient α) where
  mul x y := by
    refine' Quot.liftOn₂ x y (fun x y ↦ Quot.mk _ (x * y)) _ _
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
#align magma.assoc_quotient.of Magma.AssocQuotient.of

@[to_additive]
instance [Inhabited α] : Inhabited (AssocQuotient α) := ⟨of default⟩

@[to_additive (attr := elab_as_elim)]
protected theorem induction_on {C : AssocQuotient α → Prop} (x : AssocQuotient α)
    (ih : ∀ x, C (of x)) : C x := Quot.induction_on x ih
#align magma.assoc_quotient.induction_on Magma.AssocQuotient.induction_on

section lift

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

@[to_additive (attr := ext 1100)]
theorem hom_ext {f g : AssocQuotient α →ₙ* β} (h : f.comp of = g.comp of) : f = g :=
  (DFunLike.ext _ _) fun x => AssocQuotient.induction_on x <| DFunLike.congr_fun h
#align magma.assoc_quotient.hom_ext Magma.AssocQuotient.hom_ext

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
  left_inv f := (DFunLike.ext _ _) fun x ↦ rfl
  right_inv f := hom_ext <| (DFunLike.ext _ _) fun x ↦ rfl
#align magma.assoc_quotient.lift Magma.AssocQuotient.lift

@[to_additive (attr := simp)]
theorem lift_of (x : α) : lift f (of x) = f x := rfl
#align magma.assoc_quotient.lift_of Magma.AssocQuotient.lift_of

@[to_additive (attr := simp)]
theorem lift_comp_of : (lift f).comp of = f := lift.symm_apply_apply f
#align magma.assoc_quotient.lift_comp_of Magma.AssocQuotient.lift_comp_of

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : AssocQuotient α →ₙ* β) : lift (f.comp of) = f := lift.apply_symm_apply f
#align magma.assoc_quotient.lift_comp_of' Magma.AssocQuotient.lift_comp_of'

end lift

variable {β : Type v} [Mul β] (f : α →ₙ* β)

/-- From a magma homomorphism `α →ₙ* β` to a semigroup homomorphism
`Magma.AssocQuotient α →ₙ* Magma.AssocQuotient β`. -/
@[to_additive "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`AddMagma.AssocQuotient α → AddMagma.AssocQuotient β`."]
def map : AssocQuotient α →ₙ* AssocQuotient β := lift (of.comp f)
#align magma.assoc_quotient.map Magma.AssocQuotient.map

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl
#align magma.assoc_quotient.map_of Magma.AssocQuotient.map_of

end AssocQuotient

end Magma

/-- Free additive semigroup over a given alphabet. -/
structure FreeAddSemigroup (α : Type u) where
  /-- The head of the element -/
  head : α
  /-- The tail of the element -/
  tail : List α
#align free_add_semigroup FreeAddSemigroup
compile_inductive% FreeAddSemigroup

/-- Free semigroup over a given alphabet. -/
@[to_additive (attr := ext)]
structure FreeSemigroup (α : Type u) where
  /-- The head of the element -/
  head : α
  /-- The tail of the element -/
  tail : List α
#align free_semigroup FreeSemigroup
compile_inductive% FreeSemigroup

namespace FreeSemigroup

variable {α : Type u}

@[to_additive]
instance : Semigroup (FreeSemigroup α) where
  mul L1 L2 := ⟨L1.1, L1.2 ++ L2.1 :: L2.2⟩
  -- Porting note: replaced ext by FreeSemigroup.ext
  mul_assoc _L1 _L2 _L3 := FreeSemigroup.ext _ _ rfl <| List.append_assoc _ _ _

@[to_additive (attr := simp)]
theorem head_mul (x y : FreeSemigroup α) : (x * y).1 = x.1 := rfl
#align free_semigroup.head_mul FreeSemigroup.head_mul

@[to_additive (attr := simp)]
theorem tail_mul (x y : FreeSemigroup α) : (x * y).2 = x.2 ++ y.1 :: y.2 := rfl
#align free_semigroup.tail_mul FreeSemigroup.tail_mul

@[to_additive (attr := simp)]
theorem mk_mul_mk (x y : α) (L1 L2 : List α) : mk x L1 * mk y L2 = mk x (L1 ++ y :: L2) := rfl
#align free_semigroup.mk_mul_mk FreeSemigroup.mk_mul_mk

/-- The embedding `α → FreeSemigroup α`. -/
@[to_additive (attr := simps) "The embedding `α → FreeAddSemigroup α`."]
def of (x : α) : FreeSemigroup α := ⟨x, []⟩
#align free_semigroup.of FreeSemigroup.of

/-- Length of an element of free semigroup. -/
@[to_additive "Length of an element of free additive semigroup"]
def length (x : FreeSemigroup α) : ℕ := x.tail.length + 1
#align free_semigroup.length FreeSemigroup.length

@[to_additive (attr := simp)]
theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [length, Nat.add_right_comm, List.length, List.length_append]
#align free_semigroup.length_mul FreeSemigroup.length_mul

@[to_additive (attr := simp)]
theorem length_of (x : α) : (of x).length = 1 := rfl
#align free_semigroup.length_of FreeSemigroup.length_of

@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) := ⟨of default⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[to_additive (attr := elab_as_elim) "Recursor for free additive semigroup using `of` and `+`."]
protected def recOnMul {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
      FreeSemigroup.recOn x fun f s ↦
      List.recOn s ih1 (fun hd tl ih f ↦ ih2 f ⟨hd, tl⟩ (ih1 f) (ih hd)) f
#align free_semigroup.rec_on_mul FreeSemigroup.recOnMul

@[to_additive (attr := ext 1100)]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeSemigroup α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (DFunLike.ext _ _) fun x ↦
    FreeSemigroup.recOnMul x (congr_fun h) fun x y hx hy ↦ by simp only [map_mul, *]
#align free_semigroup.hom_ext FreeSemigroup.hom_ext

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
  left_inv f := rfl
  right_inv f := hom_ext rfl
#align free_semigroup.lift FreeSemigroup.lift

@[to_additive (attr := simp)]
theorem lift_of (x : α) : lift f (of x) = f x := rfl
#align free_semigroup.lift_of FreeSemigroup.lift_of

@[to_additive (attr := simp)]
theorem lift_comp_of : lift f ∘ of = f := rfl
#align free_semigroup.lift_comp_of FreeSemigroup.lift_comp_of

@[to_additive (attr := simp)]
theorem lift_comp_of' (f : FreeSemigroup α →ₙ* β) : lift (f ∘ of) = f := hom_ext rfl
#align free_semigroup.lift_comp_of' FreeSemigroup.lift_comp_of'

@[to_additive]
theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := by rw [map_mul, lift_of]
#align free_semigroup.lift_of_mul FreeSemigroup.lift_of_mul

end lift

section Map

variable {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : FreeSemigroup α →ₙ* FreeSemigroup β :=
  lift <| of ∘ f
#align free_semigroup.map FreeSemigroup.map

@[to_additive (attr := simp)]
theorem map_of (x) : map f (of x) = of (f x) := rfl
#align free_semigroup.map_of FreeSemigroup.map_of

@[to_additive (attr := simp)]
theorem length_map (x) : (map f x).length = x.length :=
  FreeSemigroup.recOnMul x (fun x ↦ rfl) (fun x y hx hy ↦ by simp only [map_mul, length_mul, *])
#align free_semigroup.length_map FreeSemigroup.length_map

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
#align free_semigroup.rec_on_pure FreeSemigroup.recOnPure

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) := rfl
#align free_semigroup.map_pure FreeSemigroup.map_pure

@[to_additive (attr := simp)]
theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul (map f) _ _
#align free_semigroup.map_mul' FreeSemigroup.map_mul'

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x := rfl
#align free_semigroup.pure_bind FreeSemigroup.pure_bind

@[to_additive (attr := simp)]
theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) :
    x * y >>= f = (x >>= f) * (y >>= f) := map_mul (lift f) _ _
#align free_semigroup.mul_bind FreeSemigroup.mul_bind

@[to_additive (attr := simp)]
theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x := rfl
#align free_semigroup.pure_seq FreeSemigroup.pure_seq

@[to_additive (attr := simp)]
theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} :
    f * g <*> x = (f <*> x) * (g <*> x) := mul_bind _ _ _
#align free_semigroup.mul_seq FreeSemigroup.mul_seq

@[to_additive]
instance instLawfulMonad : LawfulMonad FreeSemigroup.{u} := LawfulMonad.mk'
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun x g f ↦
    recOnPure x (fun x ↦ rfl) fun x y ih1 ih2 ↦ by rw [mul_bind, mul_bind, mul_bind, ih1, ih2])
  (id_map := fun x ↦ recOnPure x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by rw [map_mul', ih1, ih2])

/-- `FreeSemigroup` is traversable. -/
@[to_additive "`FreeAddSemigroup` is traversable."]
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u}
    (F : α → m β) (x : FreeSemigroup α) : m (FreeSemigroup β) :=
  recOnPure x (fun x ↦ pure <$> F x) fun _x _y ihx ihy ↦ (· * ·) <$> ihx <*> ihy
#align free_semigroup.traverse FreeSemigroup.traverse

@[to_additive]
instance : Traversable FreeSemigroup := ⟨@FreeSemigroup.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

@[to_additive (attr := simp)]
theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x := rfl
#align free_semigroup.traverse_pure FreeSemigroup.traverse_pure

@[to_additive (attr := simp)]
theorem traverse_pure' : traverse F ∘ pure = fun x ↦ (pure <$> F x : m (FreeSemigroup β)) := rfl
#align free_semigroup.traverse_pure' FreeSemigroup.traverse_pure'

section

variable [LawfulApplicative m]

@[to_additive (attr := simp)]
theorem traverse_mul (x y : FreeSemigroup α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun x ↦ rfl)
    (fun hd tl ih x ↦ show
        (· * ·) <$> pure <$> F x <*> traverse F (mk hd tl * mk y L2) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (mk hd tl)) <*> traverse F (mk y L2)
        by rw [ih]; simp only [(· ∘ ·), (mul_assoc _ _ _).symm, functor_norm])
    x
#align free_semigroup.traverse_mul FreeSemigroup.traverse_mul

@[to_additive (attr := simp)]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeSemigroup α → FreeSemigroup α → FreeSemigroup α) =
      fun x y ↦ (· * ·) <$> traverse F x <*> traverse F y :=
  funext fun x ↦ funext fun y ↦ traverse_mul F x y
#align free_semigroup.traverse_mul' FreeSemigroup.traverse_mul'

end

@[to_additive (attr := simp)]
theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x := rfl
#align free_semigroup.traverse_eq FreeSemigroup.traverse_eq

-- Porting note (#10675): dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem mul_map_seq (x y : FreeSemigroup α) :
    ((· * ·) <$> x <*> y : Id (FreeSemigroup α)) = (x * y : FreeSemigroup α) := rfl
#align free_semigroup.mul_map_seq FreeSemigroup.mul_map_seq

@[to_additive]
instance : LawfulTraversable FreeSemigroup.{u} :=
  { instLawfulMonad with
    id_traverse := fun x ↦
      FreeSemigroup.recOnMul x (fun x ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, mul_map_seq]
    comp_traverse := fun f g x ↦
      recOnPure x (fun x ↦ by simp only [traverse_pure, functor_norm, (· ∘ ·)])
        fun x y ih1 ih2 ↦ by (rw [traverse_mul, ih1, ih2,
          traverse_mul, Functor.Comp.map_mk]; simp only [Function.comp, functor_norm, traverse_mul])
    naturality := fun η α β f x ↦
      recOnPure x (fun x ↦ by simp only [traverse_pure, functor_norm, Function.comp])
          (fun x y ih1 ih2 ↦ by simp only [traverse_mul, functor_norm, ih1, ih2])
    traverse_eq_map_id := fun f x ↦
      FreeSemigroup.recOnMul x (fun _ ↦ rfl) fun x y ih1 ih2 ↦ by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; rfl }

end Category

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeSemigroup α) :=
  fun _ _ ↦ decidable_of_iff' _ (FreeSemigroup.ext_iff _ _)

end FreeSemigroup

namespace FreeMagma

variable {α : Type u} {β : Type v}

/-- The canonical multiplicative morphism from `FreeMagma α` to `FreeSemigroup α`. -/
@[to_additive "The canonical additive morphism from `FreeAddMagma α` to `FreeAddSemigroup α`."]
def toFreeSemigroup : FreeMagma α →ₙ* FreeSemigroup α := FreeMagma.lift FreeSemigroup.of
#align free_magma.to_free_semigroup FreeMagma.toFreeSemigroup

@[to_additive (attr := simp)]
theorem toFreeSemigroup_of (x : α) : toFreeSemigroup (of x) = FreeSemigroup.of x := rfl
#align free_magma.to_free_semigroup_of FreeMagma.toFreeSemigroup_of

@[to_additive (attr := simp)]
theorem toFreeSemigroup_comp_of : @toFreeSemigroup α ∘ of = FreeSemigroup.of := rfl
#align free_magma.to_free_semigroup_comp_of FreeMagma.toFreeSemigroup_comp_of

@[to_additive]
theorem toFreeSemigroup_comp_map (f : α → β) :
    toFreeSemigroup.comp (map f) = (FreeSemigroup.map f).comp toFreeSemigroup := by ext1; rfl
#align free_magma.to_free_semigroup_comp_map FreeMagma.toFreeSemigroup_comp_map

@[to_additive]
theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    toFreeSemigroup (map f x) = FreeSemigroup.map f (toFreeSemigroup x) :=
  DFunLike.congr_fun (toFreeSemigroup_comp_map f) x
#align free_magma.to_free_semigroup_map FreeMagma.toFreeSemigroup_map

@[to_additive (attr := simp)]
theorem length_toFreeSemigroup (x : FreeMagma α) : (toFreeSemigroup x).length = x.length :=
  FreeMagma.recOnMul x (fun x ↦ rfl) fun x y hx hy ↦ by
    rw [map_mul, FreeSemigroup.length_mul, hx, hy]; rfl
#align free_magma.length_to_free_semigroup FreeMagma.length_toFreeSemigroup

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
#align free_magma_assoc_quotient_equiv FreeMagmaAssocQuotientEquiv


namespace List

variable {α : Type u}

/-- Free monoid over a given alphabet is a list with appending operation -/
@[to_additive]
instance : Monoid (List α) where
  mul L1 L2 := L1.append L2
  mul_assoc _L1 _L2 _L3 := append_assoc _ _ _
  one := []
  one_mul := nil_append
  mul_one := append_nil

@[to_additive (attr := simp)]
theorem mul_def (x y : List α) : x * y = x.append y := rfl

/-- The embedding `α → List α`. -/
@[simp]
def of (x : α) : List α := [x]

@[to_additive (attr := simp)]
theorem length_mul (x y : List α) : (x * y).length = x.length + y.length := by
  simp [Nat.add_right_comm, List.length, List.length_append]

theorem length_of (x : α) : (of x).length = 1 := rfl

instance [Inhabited α] : Inhabited (List α) := ⟨of default⟩

/-- Recursor for free monoid using `of` and `*`. -/
@[to_additive (attr := elab_as_elim) "Recursor for free additive monoid using `of` and `+`."]
protected def recOnMul {C : List α → Sort l} (x) (ih1 : C 1) (ihof : ∀ x, C (of x))
    (ih : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
  List.recOn x ih1 fun a as h ↦ ih a as (ihof a) h

@[ext 1100]
theorem hom_ext {β : Type v} [MulOneClass β] {f g : List α →* β} (h : f ∘ of = g ∘ of) : f = g :=
  (DFunLike.ext _ _) fun x ↦
    List.recOnMul x (by simp) (congr_fun h) fun x y hx hy ↦ by simp only [map_mul, *]

section lift

variable {β : Type v} [Monoid β] (f : α → β)

theorem append_foldl_mul (b : β) (x y : List β) :
    (x ++ y).foldl (· * ·) b = x.foldl (· * ·) b * y.foldl (· * ·) 1 := by
  rw [← @List.foldl_assoc β (· * ·), mul_one, List.foldl_append]

/-- Lifts a function `α → β` to a monoid homomorphism `List α → β` given a monoid `β`. -/
@[simp]
def lift : (α → β) ≃ (List α →* β) where
  toFun f :=
    { toFun := fun x ↦ x.foldl (· * f ·) 1
      map_one' := by simp [List.foldl]
      map_mul' := fun x y ↦ by
        simp [← foldl_map]
        rw [← foldl_append, append_foldl_mul] }
  invFun f := f ∘ of
  left_inv f := by ext; simp
  right_inv f := hom_ext (by ext; simp)

@[simp]
theorem lift_of (x : α) : lift f (of x) = f x := by simp

@[simp]
theorem lift_comp_of : lift f ∘ of = f := by ext; simp

@[simp]
theorem lift_comp_of' (f : List α →* β) : lift (f ∘ of) = f := hom_ext (by ext; simp)

theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := by rw [map_mul, lift_of]

end lift

section Map

variable {β : Type v} (f : α → β)

@[simp]
theorem map_of (x) : map f (of x) = of (f x) := rfl

end Map

section Category

variable {β : Type u}

instance : Monad List where
  pure := of
  bind x f := lift f x

/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_elim]
def recOnPure {C : List α → Sort l} (x) (ih1 : C 1) (ihpure : ∀ x, C (pure x))
    (ih : ∀ x y, C (pure x) → C y → C (pure x * y)) : C x :=
  List.recOnMul x ih1 ihpure ih

@[simp, nolint simpNF]
theorem map_pure (f : α → β) (x) : (f <$> pure x : List β) = pure (f x) := rfl

@[simp]
theorem map_mul' (f : α → β) (x y : List α) : f <$> (x * y) = f <$> x * f <$> y := by simp

@[simp, nolint simpNF]
theorem pure_bind (f : α → List β) (x) : pure x >>= f = f x := rfl

@[simp]
theorem mul_bind (f : α → List β) (x y : List α) :
    x * y >>= f = (x >>= f) * (y >>= f) := map_mul (lift f) _ _

@[simp]
theorem pure_seq {f : α → β} {x : List α} : pure f <*> x = f <$> x := by simp [Seq.seq]

@[simp]
theorem mul_seq {f g : List (α → β)} {x : List α} :
    f * g <*> x = (f <*> x) * (g <*> x) := by simp [Seq.seq]

end Category

end List

/-- Isomorphism between `WithOne (FreeSemigroup α)` and `List α`. -/
@[to_additive "Isomorphism between `WithOne (FreeAddSemigroup α)` and
`FreeAddMonoid α`."]
def FreeSemigroupWithOneEquiv (α : Type u) :
    WithOne (FreeSemigroup α) ≃* List α where
  toFun x :=
    match x with
    | 1 => 1
    | some y => y.1 :: y.2
  invFun x :=
    match x with
    | [] => 1
    | x :: xs => some ⟨x, xs⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_mul' := fun x y ↦ by
    simp
    match x with
    | 1 => rw [one_mul, (by rfl : (1:List _) = List.nil), List.nil_append]
    | some x =>
      match y with
      | 1 => rw [mul_one, (by rfl : (1:List _) = List.nil), List.append_nil]
      | some y => rfl
