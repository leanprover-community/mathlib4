/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2.Init

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `Data.Sym.Basic`). The equivalence is `Sym2.equivSym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `Sym2.equivMultiset`), there is a
`Mem` instance `Sym2.Mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : Sym2 α`, then `Mem.other h` is the other
element of the pair, defined using `Classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `Sym2` is provided as `Sym2.lift`, which
states that functions from `Sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `Sym2.fromRel` which is a special case of `Sym2.lift`.

## Notation

The element `Sym2.mk (a, b)` can be written as `s(a, b)` for short.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

@[expose] public section

assert_not_exists MonoidWithZero

open List (Vector)
open Finset Function Sym

universe u

variable {α β γ : Type*}

namespace Sym2

/-- This is the relation capturing the notion of pairs equivalent up to permutations. -/
@[aesop (rule_sets := [Sym2]) [safe [constructors, cases], norm]]
inductive Rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)

attribute [refl] Rel.refl

@[symm]
theorem Rel.symm {x y : α × α} : Rel α x y → Rel α y x := by aesop (rule_sets := [Sym2])

@[trans]
theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
  aesop (rule_sets := [Sym2])

theorem Rel.is_equivalence : Equivalence (Rel α) :=
  { refl := fun (x, y) ↦ Rel.refl x y, symm := Rel.symm, trans := Rel.trans }

/-- One can use `attribute [local instance] Sym2.Rel.setoid` to temporarily
make `Quotient` functionality work for `α × α`. -/
@[instance_reducible]
def Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩

@[simp, grind =]
theorem rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap := by
  aesop (rule_sets := [Sym2])

theorem rel_iff {x y z w : α} : Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

end Sym2

/-- `Sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`Sym2.equivMultiset`).
-/
abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)

/-- Constructor for `Sym2`. This is the quotient map `α × α → Sym2 α`. -/
protected abbrev Sym2.mk {α : Type*} (a b : α) : Sym2 α := Quot.mk (Sym2.Rel α) (a, b)

/-- `s(x, y)` is an unordered pair,
which is to say a pair modulo the action of the symmetric group.

It is equal to `Sym2.mk (x, y)`. -/
notation3 "s(" x ", " y ")" => Sym2.mk x y

namespace Sym2

protected theorem sound {a b c d : α} (h : Rel α (a, b) (c, d)) : s(a, b) = s(c, d) :=
  Quot.sound h

protected theorem exact {a b c d : α} (h : s(a, b) = s(c, d)) : Rel α (a, b) (c, d) :=
  Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp, grind =]
protected theorem eq {a b c d : α} : s(a, b) = s(c, d) ↔ Rel α (a, b) (c, d) :=
  Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f s(x, y)) : ∀ i, f i :=
  Quot.ind <| Prod.rec <| h

@[elab_as_elim]
protected theorem inductionOn {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f s(x, y)) : f i :=
  i.ind hf

@[elab_as_elim]
protected theorem inductionOn₂ {f : Sym2 α → Sym2 β → Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : ∀ a₁ a₂ b₁ b₂, f s(a₁, a₂) s(b₁, b₂)) : f i j :=
  Quot.induction_on₂ i j <| by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _

/-- Dependent recursion principle for `Sym2`. See `Quot.rec`. -/
@[elab_as_elim]
protected def rec {motive : Sym2 α → Sort*}
    (f : (a b : α) → motive s(a, b))
    (h : (a b c d : α) → (h : Rel α (a, b) (c, d)) → Eq.ndrec (f a b) (Sym2.sound h) = f c d)
    (z : Sym2 α) : motive z :=
  Quot.rec (fun (a, b) ↦ f a b) (fun (a, b) (c, d) ↦ h a b c d) z

/-- Dependent recursion principle for `Sym2`. See `Quot.recOn`. -/
@[elab_as_elim]
protected def recOn {motive : Sym2 α → Sort*} (z : Sym2 α)
    (f : (a b : α) → motive s(a, b))
    (h : (a b c d : α) → (h : Rel α (a, b) (c, d)) → Eq.ndrec (f a b) (Sym2.sound h) = f c d) :
    motive z :=
  Quot.recOn z (fun (a, b) ↦ f a b) (fun (a, b) (c, d) ↦ h a b c d)

/-- A dependent recursion principle for `Sym2` that uses heterogeneous equality. -/
@[elab_as_elim]
protected def hrec {motive : Sym2 α → Sort*}
    (f : (a b : α) → motive s(a, b))
    (h : (a b : α) → f a b ≍ f b a)
    (z : Sym2 α) : motive z :=
  Quot.hrecOn _ (fun (a, b) ↦ f a b) <| by
    simp only [rel_iff']
    rintro _ _ (rfl | rfl)
    exacts [HEq.rfl, h _ _]

/-- Dependent recursion principal for `Sym2` when the target is a `Subsingleton` type.
See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton {motive : Sym2 α → Sort*}
    [(a b : α) → Subsingleton (motive s(a, b))]
    (z : Sym2 α) (f : (a b : α) → motive s(a, b)) : motive z :=
  Quot.recOnSubsingleton z fun (a, b) ↦ f a b

theorem mk_surjective : (Sym2.mk (α := α)).uncurry.Surjective := Quot.mk_surjective

protected theorem «exists» {α : Sort _} {f : Sym2 α → Prop} :
    (∃ x : Sym2 α, f x) ↔ ∃ x y, f s(x, y) :=
  mk_surjective.exists.trans Prod.exists

protected theorem «forall» {α : Sort _} {f : Sym2 α → Prop} :
    (∀ x : Sym2 α, f x) ↔ ∀ x y, f s(x, y) :=
  mk_surjective.forall.trans Prod.forall

theorem eq_swap {a b : α} : s(a, b) = s(b, a) := Quot.sound (Rel.swap _ _)

@[deprecated (since := "2026-02-05")] alias mk_prod_swap_eq := eq_swap

theorem congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c := by
  simp +contextual

theorem congr_left {a b c : α} : s(b, a) = s(c, a) ↔ b = c := by
  simp +contextual

theorem eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

theorem mk_eq_mk_iff {p q : α × α} : s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swap := by
  simp

/-- The universal property of `Sym2`; symmetric functions of two arguments are equivalent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`Sym2.fromRel` instead. -/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β) where
  toFun f :=
    Quot.lift (uncurry ↑f) <| by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨fun a b ↦ F s(a, b), fun _ _ => congr_arg F eq_swap⟩
  right_inv _ := funext <| Sym2.ind fun _ _ => rfl

@[simp]
theorem lift_mk (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b : α) :
    lift f s(a, b) = (f : α → α → β) a b :=
  rfl

@[simp]
theorem coe_lift_symm_apply (F : Sym2 α → β) (a₁ a₂ : α) :
    (lift.symm F : α → α → β) a₁ a₂ = F s(a₁, a₂) :=
  rfl

/-- A two-argument version of `Sym2.lift`. -/
def lift₂ :
    { f : α → α → β → β → γ //
        ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ } ≃
      (Sym2 α → Sym2 β → γ) where
  toFun f :=
    Quotient.lift₂ (s₁ := Sym2.Rel.setoid α) (s₂ := Sym2.Rel.setoid β)
      (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F s(a₁, a₂) s(b₁, b₂), fun a₁ a₂ b₁ b₂ => by
      constructor
      exacts [congr_arg₂ F eq_swap rfl, congr_arg₂ F rfl eq_swap]⟩
  right_inv _ := funext₂ fun a b => Sym2.inductionOn₂ a b fun _ _ _ _ => rfl

@[simp]
theorem lift₂_mk
    (f :
    { f : α → α → β → β → γ //
      ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ })
    (a₁ a₂ : α) (b₁ b₂ : β) : lift₂ f s(a₁, a₂) s(b₁, b₂) = (f : α → α → β → β → γ) a₁ a₂ b₁ b₂ :=
  rfl

@[simp]
theorem coe_lift₂_symm_apply (F : Sym2 α → Sym2 β → γ) (a₁ a₂ : α) (b₁ b₂ : β) :
    (lift₂.symm F : α → α → β → β → γ) a₁ a₂ b₁ b₂ = F s(a₁, a₂) s(b₁, b₂) :=
  rfl

/-- The functor `Sym2` is functorial, and this function constructs the induced maps.
-/
def map (f : α → β) : Sym2 α → Sym2 β :=
  Quot.map (Prod.map f f)
    (by intro _ _ h; cases h <;> constructor)

@[simp]
theorem map_id : map (@id α) = id := by
  ext ⟨⟨x, y⟩⟩
  rfl

theorem map_comp {g : β → γ} {f : α → β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f := by
  ext ⟨⟨x, y⟩⟩
  rfl

theorem map_map {g : β → γ} {f : α → β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x := by
  induction x; aesop

@[simp]
theorem map_mk (f : α → β) (a b : α) : map f s(a, b) = s(f a, f b) := rfl

@[deprecated (since := "2026-02-05")] alias map_pair_eq := map_mk

theorem map.injective {f : α → β} (hinj : Injective f) : Injective (map f) := by
  intro z z'
  refine Sym2.inductionOn₂ z z' (fun x y x' y' => ?_)
  simp [hinj.eq_iff]

/-- `mk a` as an embedding. This is the symmetric version of `Function.Embedding.sectL`. -/
@[simps]
def mkEmbedding (a : α) : α ↪ Sym2 α where
  toFun b := s(a, b)
  inj' b₁ b₁ h := by
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at h
    obtain rfl | ⟨rfl, rfl⟩ := h <;> rfl

/-- `Sym2.map` as an embedding. -/
@[simps]
def _root_.Function.Embedding.sym2Map (f : α ↪ β) : Sym2 α ↪ Sym2 β where
  toFun := map f
  inj' := map.injective f.injective

lemma lift_comp_map {g : γ → α} (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) :
    lift f ∘ map g = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ :=
  lift.symm_apply_eq.mp rfl

lemma lift_map_apply {g : γ → α} (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) (p : Sym2 γ) :
    lift f (map g p) = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ p := by
  conv_rhs => rw [← lift_comp_map, comp_apply]

section Membership

/-! ### Membership and set coercion -/


/-- This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
protected def Mem (x : α) (z : Sym2 α) : Prop :=
  ∃ y : α, z = s(x, y)

@[aesop norm (rule_sets := [Sym2])]
theorem mem_iff' {a b c : α} : Sym2.Mem a s(b, c) ↔ a = b ∨ a = c :=
  { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      aesop
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }

instance : SetLike (Sym2 α) α where
  coe z := { x | z.Mem x }
  coe_injective' z z' h := by
    simp only [Set.ext_iff, Set.mem_setOf_eq] at h
    obtain ⟨x, y⟩ := z
    obtain ⟨x', y'⟩ := z'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff'] at hx hy hx' hy'
    aesop

instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α

@[simp]
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x ∈ z :=
  Iff.rfl

theorem mem_iff_exists {x : α} {z : Sym2 α} : x ∈ z ↔ ∃ y : α, z = s(x, y) :=
  Iff.rfl

@[ext]
theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

theorem mem_mk_left (x y : α) : x ∈ s(x, y) :=
  ⟨y, rfl⟩

theorem mem_mk_right (x y : α) : y ∈ s(x, y) :=
  eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2]), grind =]
theorem mem_iff {a b c : α} : a ∈ s(b, c) ↔ a = b ∨ a = c :=
  mem_iff'

theorem out_fst_mem (e : Sym2 α) : e.out.1 ∈ e :=
  ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩

theorem out_snd_mem (e : Sym2 α) : e.out.2 ∈ e :=
  ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩

theorem ball {p : α → Prop} {a b : α} : (∀ c ∈ s(a, b), p c) ↔ p a ∧ p b := by
  simp

@[simp] lemma coe_mk {x y : α} : (s(x, y) : Set α) = {x, y} := by ext z; simp

/-- Given an element of the unordered pair, give the other element using `Classical.choose`.
See also `Mem.other'` for the computable version.
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.choose h

@[simp]
theorem other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other h) = z :=
  (Classical.choose_spec h).symm

theorem other_mem {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other h ∈ z := by
  convert mem_mk_right a <| Mem.other h
  rw [other_spec h]

theorem mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = s(x, y) := by
  constructor
  · cases z
    rw [mem_iff, mem_iff]
    aesop
  · rintro rfl
    simp

theorem eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z')
    (h4 : y ∈ z') : z = z' :=
  ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm

instance Mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x ∈ z) :=
  z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mem_iff

end Membership

@[simp]
theorem mem_map {f : α → β} {b : β} {z : Sym2 α} : b ∈ Sym2.map f z ↔ ∃ a, a ∈ z ∧ f a = b := by
  cases z
  aesop

@[congr]
theorem map_congr {f g : α → β} {s : Sym2 α} (h : ∀ x ∈ s, f x = g x) : map f s = map g s := by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩

/-- Note: `Sym2.map_id` will not simplify `Sym2.map id z` due to `Sym2.map_congr`. -/
@[simp]
theorem map_id' : (map fun x : α => x) = id :=
  map_id

/--
Partial map. If `f : ∀ a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f s h` is essentially the same as `map f s` but is defined only when all members of `s`
satisfy `p`, using the proof to apply `f`.
-/
def pmap {P : α → Prop} (f : ∀ a, P a → β) (s : Sym2 α) : (∀ a ∈ s, P a) → Sym2 β :=
  let g (p : α × α) (H : ∀ a ∈ Sym2.mk p.1 p.2, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : ∀ a ∈ s(p.1, p.2), P a := fun a hmem =>
      Hq a (Sym2.mk_eq_mk_iff.2 hpq ▸ hmem : a ∈ s(q.1, q.2))
    have h : ∀ {s₂ e H}, Eq.ndrec (motive := fun s => (∀ a ∈ s, P a) → Sym2 β) (g p) (b := s₂) e H =
      g p Hp := by
      rintro s₂ rfl _
      rfl
    refine h.trans (Quot.sound ?_)
    rw [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    apply hpq.imp <;> rintro rfl <;> simp

theorem forall_mem_pair {P : α → Prop} {a b : α} : (∀ x ∈ s(a, b), P x) ↔ P a ∧ P b := by
  simp only [mem_iff, forall_eq_or_imp, forall_eq]

lemma pair_eq_pmap {P : α → Prop} (f : ∀ a, P a → β) (a b : α) (h : P a) (h' : P b) :
    s(f a h, f b h') = pmap f s(a, b) (forall_mem_pair.mpr ⟨h, h'⟩) := rfl

lemma pmap_pair {P : α → Prop} (f : ∀ a, P a → β) (a b : α) (h : ∀ x ∈ s(a, b), P x) :
    pmap f s(a, b) h = s(f a (h a (mem_mk_left a b)), f b (h b (mem_mk_right a b))) := rfl

@[simp]
lemma mem_pmap_iff {P : α → Prop} (f : ∀ a, P a → β) (z : Sym2 α) (h : ∀ a ∈ z, P a) (b : β) :
    b ∈ z.pmap f h ↔ ∃ (a : α) (ha : a ∈ z), b = f a (h a ha) := by
  obtain ⟨x, y⟩ := z
  rw [pmap_pair f x y h]
  aesop

lemma pmap_eq_map {P : α → Prop} (f : α → β) (z : Sym2 α) (h : ∀ a ∈ z, P a) :
    z.pmap (fun a _ => f a) h = z.map f := by
  cases z; rfl

lemma map_pmap {Q : β → Prop} (f : α → β) (g : ∀ b, Q b → γ) (z : Sym2 α) (h : ∀ b ∈ z.map f, Q b) :
    (z.map f).pmap g h =
    z.pmap (fun a ha => g (f a) (h (f a) (mem_map.mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha) := by
  cases z; rfl

lemma pmap_map {P : α → Prop} {Q : β → Prop} (f : ∀ a, P a → β) (g : β → γ)
    (z : Sym2 α) (h : ∀ a ∈ z, P a) (h' : ∀ b ∈ z.pmap f h, Q b) :
    (z.pmap f h).map g = z.pmap (fun a ha => g (f a (h a ha))) (fun _ ha ↦ ha) := by
  cases z; rfl

lemma pmap_pmap {P : α → Prop} {Q : β → Prop} (f : ∀ a, P a → β) (g : ∀ b, Q b → γ)
    (z : Sym2 α) (h : ∀ a ∈ z, P a) (h' : ∀ b ∈ z.pmap f h, Q b) :
    (z.pmap f h).pmap g h' = z.pmap (fun a ha => g (f a (h a ha))
    (h' _ ((mem_pmap_iff f z h _).mpr ⟨a, ha, rfl⟩))) (fun _ ha ↦ ha) := by
  cases z; rfl

@[simp]
lemma pmap_subtype_map_subtypeVal {P : α → Prop} (s : Sym2 α) (h : ∀ a ∈ s, P a) :
    (s.pmap Subtype.mk h).map Subtype.val = s := by
  cases s; rfl

/--
"Attach" a proof `P a` that holds for all the elements of `s` to produce a new Sym2 object
with the same elements but in the type `{x // P x}`.
-/
def attachWith {P : α → Prop} (s : Sym2 α) (h : ∀ a ∈ s, P a) : Sym2 {a // P a} :=
  pmap Subtype.mk s h

@[simp]
lemma attachWith_map_subtypeVal {s : Sym2 α} {P : α → Prop} (h : ∀ a ∈ s, P a) :
    (s.attachWith h).map Subtype.val = s := by
  cases s; rfl

/-! ### Diagonal -/

variable {z : Sym2 α} {f : α → β}

/-- A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `Sym2 α`.
-/
def diag (x : α) : Sym2 α := s(x, x)

theorem diag_injective : Function.Injective (Sym2.diag : α → Sym2 α) := fun x y h => by
  cases Sym2.exact h <;> rfl

/-- A predicate for testing whether an element of `Sym2 α` is on the diagonal.
-/
def IsDiag : Sym2 α → Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩

@[simp]
theorem mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias isDiag_iff_proj_eq := mk_isDiag_iff

protected lemma IsDiag.map : z.IsDiag → (z.map f).IsDiag := Sym2.ind (fun _ _ ↦ congr_arg f) z

lemma isDiag_map (hf : Injective f) : (z.map f).IsDiag ↔ z.IsDiag :=
  Sym2.ind (fun _ _ ↦ hf.eq_iff) z

@[simp]
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a

@[simp, nontriviality]
lemma isDiag_of_subsingleton [Subsingleton α] (z : Sym2 α) : z.IsDiag := z.ind Subsingleton.elim

/-- The set of all `Sym2 α` elements on the diagonal. -/
def diagSet : Set (Sym2 α) := {z | z.IsDiag}

@[simp] lemma mem_diagSet : z ∈ diagSet ↔ z.IsDiag := .rfl

@[deprecated mem_diagSet (since := "2025-12-10")]
theorem mem_diagSet_iff_isDiag (z : Sym2 α) : z ∈ diagSet ↔ z.IsDiag := .rfl

@[simp] lemma range_diag : .range (diag : α → Sym2 α) = diagSet := by
  ext ⟨a, b⟩; simp [diag, eq_comm]

@[deprecated (since := "2025-11-05")] alias ⟨_, IsDiag.mem_range_diag⟩ := mem_diagSet_iff_isDiag

@[deprecated range_diag (since := "2025-11-05")]
theorem isDiag_iff_mem_range_diag (z : Sym2 α) : IsDiag z ↔ z ∈ Set.range (@diag α) := by simp

@[deprecated mem_diagSet (since := "2025-11-05")]
theorem mem_diagSet_iff_eq {a b : α} : s(a, b) ∈ diagSet ↔ a = b := by simp

theorem diagSet_eq_setOf_isDiag : diagSet = {z : Sym2 α | z.IsDiag} := rfl

set_option linter.deprecated false in
@[deprecated Set.compl_setOf (since := "2025-12-10")]
theorem diagSet_compl_eq_setOf_not_isDiag : diagSetᶜ = {z : Sym2 α | ¬z.IsDiag} :=
  congrArg _ diagSet_eq_setOf_isDiag

theorem diagSet_eq_univ_of_subsingleton [Subsingleton α] : @diagSet α = Set.univ := by ext; simp

instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) :=
  fun z => z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mk_isDiag_iff

instance decidablePred_mem_diagSet (α : Type u) [DecidableEq α] : DecidablePred (· ∈ @diagSet α) :=
  IsDiag.decidablePred _

theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a ∈ z) : Mem.other h ≠ a := by
  contrapose! hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

section Relations

/-! ### Declarations about symmetric relations -/


variable {r r₁ r₂ : α → α → Prop}

/-- Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Symmetric r) : Set (Sym2 α) :=
  setOf (lift ⟨r, fun _ _ => propext ⟨(sym ·), (sym ·)⟩⟩)

@[simp]
theorem fromRel_prop {sym : Symmetric r} {a b : α} : s(a, b) ∈ fromRel sym ↔ r a b :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias fromRel_proj_prop := fromRel_prop

theorem fromRel_mono_iff (sym₁ : Symmetric r₁) (sym₂ : Symmetric r₂) :
    fromRel sym₁ ⊆ fromRel sym₂ ↔ r₁ ≤ r₂ :=
  ⟨fun hle a b ↦ @hle s(a, b), fun hle ↦ Sym2.ind hle⟩

alias ⟨_, fromRel_mono⟩ := fromRel_mono_iff

/-- `fromRel` induces an order embedding from symmetric relations to `Sym2` sets. -/
def fromRelOrderEmbedding : { r : α → α → Prop // Symmetric r } ↪o Set (Sym2 α) :=
  OrderEmbedding.ofMapLEIff (fun r ↦ Sym2.fromRel r.prop) fun _ _ ↦ fromRel_mono_iff ..

@[simp]
theorem fromRel_eq_fromRell_iff_eq {r₁ r₂ : α → α → Prop} (sym₁ : Symmetric r₁)
    (sym₂ : Symmetric r₂) : fromRel sym₁ = fromRel sym₂ ↔ r₁ = r₂ := by
  rw [← Subtype.mk.injEq r₁ sym₁ r₂ sym₂, ← fromRelOrderEmbedding.eq_iff_eq]
  rfl

theorem fromRel_bot : fromRel (α := α) (r := ⊥) (fun _ _ ↦ id) = ∅ :=
  Set.eq_empty_of_forall_notMem <| Sym2.ind <| by simp

@[simp]
theorem fromRel_bot_iff {sym : Symmetric r} : fromRel sym = ∅ ↔ r = ⊥ := by
  refine ⟨fun h ↦ ?_, (· ▸ fromRel_bot)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

theorem fromRel_top : fromRel (α := α) (r := ⊤) (fun _ _ ↦ id) = .univ :=
  Set.eq_univ_of_forall <| Sym2.ind <| by simp

@[simp]
theorem fromRel_top_iff {sym : Symmetric r} : fromRel sym = .univ ↔ r = ⊤ := by
  refine ⟨fun h ↦ ?_, (· ▸ fromRel_top)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

theorem fromRel_ne : fromRel (fun (_ _ : α) z => z.symm : Symmetric Ne) = {z | ¬IsDiag z} := by
  ext z; exact z.ind (by simp)

lemma diagSet_eq_fromRel_eq : diagSet = fromRel (α := α) eq_equivalence.symmetric := by
  ext ⟨a, b⟩; simp

lemma diagSet_compl_eq_fromRel_ne : diagSetᶜ = fromRel (α := α) (r := Ne) (fun _ _ ↦ Ne.symm) := by
  ext ⟨a, b⟩; simp

@[simp] lemma diagSet_subset_fromRel (hr : Symmetric r) : diagSet ⊆ fromRel hr ↔ Reflexive r := by
  simp [Set.subset_def, Sym2.forall, Reflexive]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma disjoint_diagSet_fromRel (hr : Symmetric r) :
    Disjoint diagSet (fromRel hr) ↔ Std.Irrefl r := by
  refine .trans ?_ ⟨(⟨·⟩), (·.irrefl)⟩
  simp [Set.disjoint_left, Sym2.forall]

@[simp] lemma fromRel_subset_compl_diagSet (hr : Symmetric r) :
    fromRel hr ⊆ diagSetᶜ ↔ Std.Irrefl r := by simp [Set.subset_compl_iff_disjoint_left]

@[deprecated diagSet_subset_fromRel (since := "2025-12-10")]
theorem reflexive_iff_diagSet_subset_fromRel (sym : Symmetric r) :
    Reflexive r ↔ diagSet ⊆ fromRel sym := by simp

@[deprecated fromRel_subset_compl_diagSet (since := "2025-12-10")]
theorem irreflexive_iff_fromRel_subset_diagSet_compl (sym : Symmetric r) :
    Std.Irrefl r ↔ fromRel sym ⊆ diagSetᶜ := by simp

theorem fromRel_irrefl {sym : Symmetric r} : Std.Irrefl r ↔ ∀ {z}, z ∈ fromRel sym → ¬IsDiag z where
  mp := by intro ⟨h⟩; apply Sym2.ind; aesop
  mpr h := ⟨fun _ hr ↦ h (fromRel_prop.mpr hr) rfl⟩

@[deprecated (since := "2026-02-12")] alias fromRel_irreflexive := fromRel_irrefl

theorem mem_fromRel_irrefl_other_ne {sym : Symmetric r} (irrefl : Std.Irrefl r) {a : α}
    {z : Sym2 α} (hz : z ∈ fromRel sym) (h : a ∈ z) : Mem.other h ≠ a :=
  other_ne (fromRel_irrefl.mp irrefl hz) h

instance fromRel.decidablePred (sym : Symmetric r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel sym) := fun z => z.recOnSubsingleton h

lemma fromRel_relationMap {r : α → α → Prop} (hr : Symmetric r) (f : α → β) :
    fromRel (Relation.map_symmetric hr f) = Sym2.map f '' Sym2.fromRel hr := by
  ext ⟨a, b⟩
  simp only [fromRel_prop, Relation.Map, Set.mem_image, Sym2.exists, map_mk, Sym2.eq,
    rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_or_left, exists_or, iff_self_or,
    forall_exists_index, and_imp]
  exact fun c d hcd hc hd ↦ ⟨d, c, hr hcd, hd, hc⟩

/-- The inverse to `Sym2.fromRel`. Given a set on `Sym2 α`, give a symmetric relation on `α`
(see `Sym2.toRel_symmetric`). -/
def ToRel (s : Set (Sym2 α)) (x y : α) : Prop :=
  s(x, y) ∈ s

@[simp]
theorem toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ s(x, y) ∈ s :=
  Iff.rfl

theorem toRel_symmetric (s : Set (Sym2 α)) : Symmetric (ToRel s) := fun x y => by simp [eq_swap]

theorem toRel_fromRel (sym : Symmetric r) : ToRel (fromRel sym) = r :=
  rfl

theorem fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symmetric s) = s :=
  Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z

end Relations

section ToMultiset

/-- Map an unordered pair to an unordered list. -/
def toMultiset {α : Type*} (z : Sym2 α) : Multiset α := by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

/-- Mapping an unordered pair to an unordered list produces a multiset of size `2`. -/
lemma card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2 := by
  induction z
  simp [Sym2.toMultiset]

/-- The members of an unordered pair are members of the corresponding unordered list. -/
@[simp]
theorem mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} :
    x ∈ (z.toMultiset : Multiset α) ↔ x ∈ z := by
  induction z
  simp [Sym2.toMultiset]

end ToMultiset

section ToFinset

variable [DecidableEq α]

/-- Map an unordered pair to a finite set. -/
def toFinset (z : Sym2 α) : Finset α := (z.toMultiset : Multiset α).toFinset

/-- The members of an unordered pair are members of the corresponding finite set. -/
@[simp]
theorem mem_toFinset {x : α} {z : Sym2 α} : x ∈ z.toFinset ↔ x ∈ z := by
  rw [← Sym2.mem_toMultiset, Sym2.toFinset, Multiset.mem_toFinset]

lemma toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y} := by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff]

/-- Mapping an unordered pair on the diagonal to a finite set produces a finset of size `1`. -/
theorem card_toFinset_of_isDiag (z : Sym2 α) (h : z.IsDiag) : #(z : Sym2 α).toFinset = 1 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair off the diagonal to a finite set produces a finset of size `2`. -/
theorem card_toFinset_of_not_isDiag (z : Sym2 α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair to a finite set produces a finset of size `1` if the pair is on the
diagonal, else of size `2` if the pair is off the diagonal. -/
theorem card_toFinset (z : Sym2 α) : #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2 := by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

end ToFinset

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] List.Vector.Perm.isSetoid

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private def fromVector : List.Vector α 2 → α × α
  | ⟨[a, b], _⟩ => (a, b)

private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .inr ⟨h₁, h₂⟩ => by
          rw [h₁, h₂]
          first | done | constructor }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The symmetric square is equivalent to length-2 vectors up to permutations. -/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2) where
  toFun :=
    Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; swap
        · exfalso
          simp at hx
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; swap
        · exfalso
          simp at hy
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · constructor
        apply Sym2.Rel.swap)
  left_inv := by apply Sym2.ind; aesop (add norm unfold [Sym2.fromVector])
  right_inv x := by
    refine x.recOnSubsingleton fun x => ?_
    obtain ⟨x, hx⟩ := x
    obtain - | ⟨-, x⟩ := x
    · simp at hx
    rcases x with - | ⟨_, x⟩
    · simp at hx
    rcases x with - | ⟨_, x⟩
    swap
    · exfalso
      simp at hx
    rfl

/-- The symmetric square is equivalent to the second symmetric power. -/
def equivSym (α : Type*) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm

/-- The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equivSym`, but it's provided
in case the definition for `Sym` changes.) -/
def equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s = 2 } :=
  equivSym α

end SymEquiv

section Decidable

/-- Given `[DecidableEq α]` and `[Fintype α]`, the following instance gives `Fintype (Sym2 α)`.
-/
instance instDecidableRel [DecidableEq α] : DecidableRel (Rel α) :=
  fun _ _ => decidable_of_iff' _ rel_iff

section
attribute [local instance] Sym2.Rel.setoid

instance instDecidableRel' [DecidableEq α] : DecidableRel (HasEquiv.Equiv (α := α × α)) :=
  instDecidableRel

end

instance [DecidableEq α] : DecidableEq (Sym2 α) :=
  inferInstanceAs% <| DecidableEq (Quotient (Sym2.Rel.setoid α))

/-! ### The other element of an element of the symmetric square -/

/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`. -/
@[aesop norm unfold (rule_sets := [Sym2])]
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Sym2.rec (fun b c _ => if a = b then c else b) (by
    clear h z
    intro b c d e h
    ext hy
    have {f g h} : @Eq.ndrec (Sym2 α) s(b, c)
      (fun x => a ∈ x → α) (fun _ => if a = b then c else b) f g h =
        if a = b then c else b := by subst g; rfl
    aesop)
    z h

@[simp]
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other' h) = z := by
  induction z
  aesop (add norm unfold [Sym2.rec, Quot.rec]) (rule_sets := [Sym2])

@[simp]
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) :
    Mem.other h = Mem.other' h := by rw [← congr_right, other_spec' h, other_spec]

theorem other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other' h ∈ z := by
  rw [← other_eq_other']
  exact other_mem h

theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other' ha ∈ z) :
    Mem.other' hb = a := by
  induction z
  aesop (rule_sets := [Sym2]) (add norm unfold [Sym2.rec, Quot.rec])

theorem other_invol {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other ha ∈ z) :
    Mem.other hb = a := by
  classical
    rw [other_eq_other'] at hb ⊢
    convert other_invol' ha hb using 2
    apply other_eq_other'

theorem filter_image_mk_isDiag [DecidableEq α] (s : Finset α) :
    {x ∈ (s ×ˢ s).image Sym2.mk.uncurry | x.IsDiag} = s.diag.image Sym2.mk.uncurry := by aesop

theorem filter_image_mk_not_isDiag [DecidableEq α] (s : Finset α) :
    {x ∈ (s ×ˢ s).image Sym2.mk.uncurry | ¬x.IsDiag} = s.offDiag.image Sym2.mk.uncurry := by aesop

end Decidable

instance [Subsingleton α] : Subsingleton (Sym2 α) :=
  (equivSym α).injective.subsingleton

instance [Unique α] : Unique (Sym2 α) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty (Sym2 α) :=
  (equivSym α).isEmpty

instance [Nontrivial α] : Nontrivial (Sym2 α) :=
  diag_injective.nontrivial

-- TODO: use a sort order if available, https://github.com/leanprover-community/mathlib/issues/18166
unsafe instance [Repr α] : Repr (Sym2 α) where
  reprPrec s _ := f!"s({repr s.unquot.1}, {repr s.unquot.2})"

lemma lift_smul_lift {α R N} [SMul R N] (f : { f : α → α → R // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ })
    (g : { g : α → α → N // ∀ a₁ a₂, g a₁ a₂ = g a₂ a₁ }) :
    lift f • lift g = lift ⟨f.val • g.val, fun _ _ => by
      rw [Pi.smul_apply', Pi.smul_apply', Pi.smul_apply', Pi.smul_apply', f.prop, g.prop]⟩ := by
  ext ⟨i, j⟩
  simp_all only [Pi.smul_apply', lift_mk]

/--
Multiplication as a function from `Sym2`.
-/
@[to_additive /-- Addition as a function from `Sym2`. -/]
def mul {M} [CommMagma M] : Sym2 M → M := lift ⟨(· * ·), mul_comm⟩

@[to_additive (attr := simp)]
lemma mul_mk {M} [CommMagma M] (a b : M) : mul s(a, b) = a * b := rfl

end Sym2

namespace Set

open Sym2

variable {s : Set α}

/--
For a set `s : Set α`, `s.sym2` is the set of all unordered pairs of elements from `s`.
-/
def sym2 (s : Set α) : Set (Sym2 α) := fromRel (r := fun x y ↦ x ∈ s ∧ y ∈ s) (fun _ _ => .symm)

@[simp] lemma mk_mem_sym2_iff {x y : α} : s(x, y) ∈ s.sym2 ↔ x ∈ s ∧ y ∈ s := Iff.rfl

@[deprecated (since := "2026-02-05")] alias mk'_mem_sym2_iff := mk_mem_sym2_iff

lemma mem_sym2_iff_subset {z : Sym2 α} : z ∈ s.sym2 ↔ (z : Set α) ⊆ s := by
  induction z using Sym2.inductionOn
  simp [pair_subset_iff]

lemma sym2_eq_mk_image : s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s := by ext ⟨x, y⟩; aesop

@[simp] lemma mk_preimage_sym2 : (Sym2.mk.uncurry) ⁻¹' s.sym2 = s ×ˢ s := rfl

@[simp] lemma sym2_empty : (∅ : Set α).sym2 = ∅ := by ext ⟨x, y⟩; simp
@[simp] lemma sym2_univ : (Set.univ : Set α).sym2 = Set.univ := by ext ⟨x, y⟩; simp

@[simp] lemma sym2_singleton (a : α) : ({a} : Set α).sym2 = {s(a, a)} := by ext ⟨x, y⟩; simp
lemma sym2_insert (a : α) (s : Set α) :
    (insert a s).sym2 = (fun b ↦ s(a, b)) '' insert a s ∪ s.sym2 := by
  ext ⟨x, y⟩; aesop

lemma sym2_preimage {f : α → β} {s : Set β} : (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s.sym2 := by
  ext ⟨x, y⟩
  simp

lemma sym2_image {f : α → β} {s : Set α} : (f '' s).sym2 = Sym2.map f '' s.sym2 := by
  simp_rw [sym2_eq_mk_image, prod_image_image_eq, image_image, uncurry, Sym2.map_mk]

lemma sym2_inter (s t : Set α) : (s ∩ t).sym2 = s.sym2 ∩ t.sym2 :=
  preimage_injective.mpr Sym2.mk_surjective <| Set.prod_inter_prod.symm

lemma sym2_iInter {ι : Type*} (f : ι → Set α) : (⋂ i, f i).sym2 = ⋂ i, (f i).sym2 := by
  ext ⟨x, y⟩; simp [forall_and]

end Set
