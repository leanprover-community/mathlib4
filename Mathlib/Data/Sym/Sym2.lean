/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Sym2.Init

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
def Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩

@[simp]
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
protected abbrev Sym2.mk {α : Type*} (p : α × α) : Sym2 α := Quot.mk (Sym2.Rel α) p

/-- `s(x, y)` is an unordered pair,
which is to say a pair modulo the action of the symmetric group.

It is equal to `Sym2.mk (x, y)`. -/
notation3 "s(" x ", " y ")" => Sym2.mk (x, y)

namespace Sym2

protected theorem sound {p p' : α × α} (h : Sym2.Rel α p p') : Sym2.mk p = Sym2.mk p' :=
  Quot.sound h

protected theorem exact {p p' : α × α} (h : Sym2.mk p = Sym2.mk p') : Sym2.Rel α p p' :=
  Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp]
protected theorem eq {p p' : α × α} : Sym2.mk p = Sym2.mk p' ↔ Sym2.Rel α p p' :=
  Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f s(x, y)) : ∀ i, f i :=
  Quot.ind <| Prod.rec <| h

theorem exists_eq (z : Sym2 α) : ∃ x y, z = s(x, y) :=
  z.ind fun x y => ⟨x, y, rfl⟩

@[elab_as_elim]
protected theorem inductionOn {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f s(x, y)) : f i :=
  i.ind hf

@[elab_as_elim]
protected theorem inductionOn₂ {f : Sym2 α → Sym2 β → Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : ∀ a₁ a₂ b₁ b₂, f s(a₁, a₂) s(b₁, b₂)) : f i j :=
  Quot.induction_on₂ i j <| by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _

/-- Dependent recursion principal for `Sym2`. See `Quot.rec`. -/
@[elab_as_elim]
protected def rec {motive : Sym2 α → Sort*}
    (f : (p : α × α) → motive (Sym2.mk p))
    (h : (p q : α × α) → (h : Sym2.Rel α p q) → Eq.ndrec (f p) (Sym2.sound h) = f q)
    (z : Sym2 α) : motive z :=
  Quot.rec f h z

/-- Dependent recursion principal for `Sym2` when the target is a `Subsingleton` type.
See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton {motive : Sym2 α → Sort*}
    [(p : α × α) → Subsingleton (motive (Sym2.mk p))]
    (z : Sym2 α) (f : (p : α × α) → motive (Sym2.mk p)) : motive z :=
  Quot.recOnSubsingleton z f

protected theorem «exists» {α : Sort _} {f : Sym2 α → Prop} :
    (∃ x : Sym2 α, f x) ↔ ∃ x y, f s(x, y) :=
  Quot.mk_surjective.exists.trans Prod.exists

protected theorem «forall» {α : Sort _} {f : Sym2 α → Prop} :
    (∀ x : Sym2 α, f x) ↔ ∀ x y, f s(x, y) :=
  Quot.mk_surjective.forall.trans Prod.forall

theorem eq_swap {a b : α} : s(a, b) = s(b, a) := Quot.sound (Rel.swap _ _)

@[simp]
theorem mk_prod_swap_eq {p : α × α} : Sym2.mk p.swap = Sym2.mk p := by
  cases p
  exact eq_swap

theorem congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c := by
  simp +contextual

theorem congr_left {a b c : α} : s(b, a) = s(c, a) ↔ b = c := by
  simp +contextual

theorem eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

theorem mk_eq_mk_iff {p q : α × α} : Sym2.mk p = Sym2.mk q ↔ p = q ∨ p = q.swap := by
  cases p
  cases q
  simp only [eq_iff, Prod.mk_inj, Prod.swap_prod_mk]

/-- The universal property of `Sym2`; symmetric functions of two arguments are equivalent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`Sym2.fromRel` instead. -/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β) where
  toFun f :=
    Quot.lift (uncurry ↑f) <| by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨curry (F ∘ Sym2.mk), fun _ _ => congr_arg F eq_swap⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext <| Sym2.ind fun _ _ => rfl

@[simp]
theorem lift_mk (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a₁ a₂ : α) :
    lift f s(a₁, a₂) = (f : α → α → β) a₁ a₂ :=
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
  left_inv _ := Subtype.ext rfl
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
theorem map_pair_eq (f : α → β) (x y : α) : map f s(x, y) = s(f x, f y) :=
  rfl

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
    simp only [mem_iff', eq_self_iff_true] at hx hy hx' hy'
    aesop

@[simp]
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x ∈ z :=
  Iff.rfl

@[simp] theorem setOf_mem_eq {z : Sym2 α} : {v | v ∈ z} = z := rfl

theorem mem_iff_exists {x : α} {z : Sym2 α} : x ∈ z ↔ ∃ y : α, z = s(x, y) :=
  Iff.rfl

@[ext]
theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

theorem mem_mk_left (x y : α) : x ∈ s(x, y) :=
  ⟨y, rfl⟩

theorem mem_mk_right (x y : α) : y ∈ s(x, y) :=
  eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2])]
theorem mem_iff {a b c : α} : a ∈ s(b, c) ↔ a = b ∨ a = c :=
  mem_iff'

@[simp] theorem coe_mk_eq {x y : α} : (s(x, y) : Set α) = {x, y} := by
  ext; simp

theorem out_fst_mem (e : Sym2 α) : e.out.1 ∈ e :=
  ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩

theorem out_snd_mem (e : Sym2 α) : e.out.2 ∈ e :=
  ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩

theorem ball {p : α → Prop} {a b : α} : (∀ c ∈ s(a, b), p c) ↔ p a ∧ p b := by
  refine ⟨fun h => ⟨h _ <| mem_mk_left _ _, h _ <| mem_mk_right _ _⟩, fun h c hc => ?_⟩
  obtain rfl | rfl := Sym2.mem_iff.1 hc
  · exact h.1
  · exact h.2

/-- Given an element of the unordered pair, give the other element using `Classical.choose`.
See also `Mem.other'` for the computable version.
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.choose h

@[simp]
theorem other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other h) = z := by
  erw [← Classical.choose_spec h]

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
  z.recOnSubsingleton fun ⟨_, _⟩ => decidable_of_iff' _ mem_iff

end Membership

@[simp]
theorem mem_map {f : α → β} {b : β} {z : Sym2 α} : b ∈ Sym2.map f z ↔ ∃ a, a ∈ z ∧ f a = b := by
  cases z
  simp only [map_pair_eq, mem_iff, exists_eq_or_imp, exists_eq_left]
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
  let g (p : α × α) (H : ∀ a ∈ Sym2.mk p, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : ∀ a ∈ Sym2.mk p, P a := fun a hmem =>
      Hq a (Sym2.mk_eq_mk_iff.2 hpq ▸ hmem : a ∈ Sym2.mk q)
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

lemma map_pmap {Q : β → Prop} (f : α → β) (g : ∀ b, Q b → γ) (z : Sym2 α) (h : ∀ b ∈ z.map f, Q b):
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

variable {e : Sym2 α} {f : α → β}

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

theorem mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y :=
  Iff.rfl

theorem isDiag_iff_exists {z : Sym2 α} : z.IsDiag ↔ ∃ x, z = s(x, x) := by
  induction z; rw [mk_isDiag_iff]; simp [eq_comm]

theorem not_isDiag_iff_exists {z : Sym2 α} : ¬ z.IsDiag ↔ ∃ x y, x ≠ y ∧ z = s(x, y) := by
  induction z with | _ x y =>
  rw [mk_isDiag_iff, not_iff_comm]
  push_neg
  constructor
  · intro h; simpa using h x y
  · aesop

@[simp]
theorem isDiag_iff_proj_eq (z : α × α) : IsDiag (Sym2.mk z) ↔ z.1 = z.2 :=
  Prod.recOn z fun _ _ => mk_isDiag_iff

protected lemma IsDiag.map : e.IsDiag → (e.map f).IsDiag := Sym2.ind (fun _ _ ↦ congr_arg f) e

lemma isDiag_map (hf : Injective f) : (e.map f).IsDiag ↔ e.IsDiag :=
  Sym2.ind (fun _ _ ↦ hf.eq_iff) e

@[simp]
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a

theorem IsDiag.mem_range_diag {z : Sym2 α} : IsDiag z → z ∈ Set.range (@diag α) := by
  obtain ⟨x, y⟩ := z
  rintro (rfl : x = y)
  exact ⟨_, rfl⟩

theorem isDiag_iff_mem_range_diag (z : Sym2 α) : IsDiag z ↔ z ∈ Set.range (@diag α) :=
  ⟨IsDiag.mem_range_diag, fun ⟨i, hi⟩ => hi ▸ diag_isDiag i⟩

instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) :=
  fun z => z.recOnSubsingleton fun a => decidable_of_iff' _ (isDiag_iff_proj_eq a)

theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a ∈ z) : Mem.other h ≠ a := by
  contrapose! hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

section Relations

/-! ### Declarations about symmetric relations -/


variable {r : α → α → Prop}

/-- Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Symmetric r) : Set (Sym2 α) :=
  setOf (lift ⟨r, fun _ _ => propext ⟨(sym ·), (sym ·)⟩⟩)

@[simp]
theorem fromRel_proj_prop {sym : Symmetric r} {z : α × α} : Sym2.mk z ∈ fromRel sym ↔ r z.1 z.2 :=
  Iff.rfl

theorem fromRel_prop {sym : Symmetric r} {a b : α} : s(a, b) ∈ fromRel sym ↔ r a b :=
  Iff.rfl

theorem fromRel_bot : fromRel (fun (_ _ : α) z => z : Symmetric ⊥) = ∅ := by
  apply Set.eq_empty_of_forall_not_mem fun e => _
  apply Sym2.ind
  simp [-Set.bot_eq_empty, Prop.bot_eq_false]

theorem fromRel_top : fromRel (fun (_ _ : α) z => z : Symmetric ⊤) = Set.univ := by
  apply Set.eq_univ_of_forall fun e => _
  apply Sym2.ind
  simp [-Set.top_eq_univ, Prop.top_eq_true]

theorem fromRel_ne : fromRel (fun (_ _ : α) z => z.symm : Symmetric Ne) = {z | ¬IsDiag z} := by
  ext z; exact z.ind (by simp)

theorem fromRel_irreflexive {sym : Symmetric r} :
    Irreflexive r ↔ ∀ {z}, z ∈ fromRel sym → ¬IsDiag z :=
  { mp := by intro h; apply Sym2.ind; aesop
    mpr := fun h _ hr => h (fromRel_prop.mpr hr) rfl }

theorem mem_fromRel_irrefl_other_ne {sym : Symmetric r} (irrefl : Irreflexive r) {a : α}
    {z : Sym2 α} (hz : z ∈ fromRel sym) (h : a ∈ z) : Mem.other h ≠ a :=
  other_ne (fromRel_irreflexive.mp irrefl hz) h

instance fromRel.decidablePred (sym : Symmetric r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel sym) := fun z => z.recOnSubsingleton fun _ => h _ _

lemma fromRel_relationMap {r : α → α → Prop} (hr : Symmetric r) (f : α → β) :
    fromRel (Relation.map_symmetric hr f) = Sym2.map f '' Sym2.fromRel hr := by
  ext ⟨a, b⟩
  simp only [fromRel_proj_prop, Relation.Map, Set.mem_image, Sym2.exists, map_pair_eq, Sym2.eq,
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

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] List.Vector.Perm.isSetoid

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
          first | done | apply List.Perm.swap'; rfl }

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
  inferInstanceAs <| DecidableEq (Quotient (Sym2.Rel.setoid α))

/-! ### Edge as a multiset/finset -/

section

/--
Interpret an unordered pair `z` as a multiset containing its elements.
This function is registered as a coercion from `Sym2 α` to `Multiset α`.
-/
@[coe]
protected def toMultiset (z : Sym2 α) : Multiset α :=
  Sym2.lift ⟨fun x y => {x, y}, Multiset.pair_comm⟩ z

instance : Coe (Sym2 α) (Multiset α) := ⟨Sym2.toMultiset⟩

@[simp] lemma toMultiset_mk {x y : α} : (s(x, y) : Multiset α) = {x, y} := rfl

variable [DecidableEq α]

/--
Interpret an unordered pair `z` as a finset containing its elements.
This function is registered as a coercion from `Sym2 α` to `Finset α`.
-/
@[coe]
protected def toFinset (z : Sym2 α) : Finset α := Multiset.toFinset z

instance : Coe (Sym2 α) (Finset α) := ⟨Sym2.toFinset⟩

@[simp] lemma toFinset_mk {x y : α} : (s(x, y) : Finset α) = {x, y} := by
  ext; rw [Sym2.toFinset, Sym2.toMultiset]; simp

@[simp] lemma toFinset_toMultiset {s : Sym2 α} : (s : Multiset α).toFinset = (s : Finset α) := rfl

@[simp] lemma mem_toFinset {z : Sym2 α} {x : α} : x ∈ (z : Finset α) ↔ x ∈ z := by
  induction z; simp

@[simp] lemma coe_toFinset {z : Sym2 α} : ((z : Finset α) : Set α) = z := by
  ext; simp

@[simp] lemma toFinset_eq [Fintype α] {e : Sym2 α} : (e : Finset α) = {v | v ∈ e}.toFinset := by
  ext; simp

lemma card_toFinset_of_isDiag {z : Sym2 α} (h : z.IsDiag) : (z : Finset α).card = 1 := by
  obtain ⟨x, rfl⟩ := isDiag_iff_exists.mp h
  simp [Finset.card_eq_one]

lemma card_toFinset_mk_of_ne {x y : α} (h : x ≠ y) : s(x, y).toFinset.card = 2 := by
  rw [card_eq_two]
  use x, y, h
  simp

lemma card_toFinset_of_not_isDiag {z : Sym2 α} (h : ¬z.IsDiag) : z.toFinset.card = 2 := by
  induction z with | _ x y => exact card_toFinset_mk_of_ne h

lemma one_le_card_toFinset {z : Sym2 α} : 1 ≤ z.toFinset.card := by
  induction z; simp

lemma card_toFinset_le_two {z : Sym2 α} : z.toFinset.card ≤ 2 := by
  by_cases z.IsDiag <;> simp [*, card_toFinset_of_isDiag, card_toFinset_of_not_isDiag]

end


/-! ### The other element of an element of the symmetric square -/


/--
A function that gives the other element of a pair given one of the elements.  Used in `Mem.other'`.
-/
@[aesop norm unfold (rule_sets := [Sym2])]
private def pairOther [DecidableEq α] (a : α) (z : α × α) : α :=
  if a = z.1 then z.2 else z.1


/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`. -/
@[aesop norm unfold (rule_sets := [Sym2])]
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Sym2.rec (fun s _ => pairOther a s) (by
    clear h z
    intro x y h
    ext hy
    convert_to Sym2.pairOther a x = _
    · have : ∀ {c e h}, @Eq.ndrec (Sym2 α) (Sym2.mk x)
          (fun x => a ∈ x → α) (fun _ => Sym2.pairOther a x) c e h = Sym2.pairOther a x := by
          intro _ e _; subst e; rfl
      apply this
    · rw [mem_iff] at hy
      aesop (add norm unfold [pairOther]))
    z h

@[simp]
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other' h) = z := by
  induction z
  have h' := mem_iff.mp h
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
    {a ∈ (s ×ˢ s).image Sym2.mk | a.IsDiag} = s.diag.image Sym2.mk := by
  ext ⟨x, y⟩
  simp only [mem_image, mem_diag, exists_prop, mem_filter, Prod.exists, mem_product]
  constructor
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
    rw [← h, Sym2.mk_isDiag_iff] at hab
    exact ⟨a, b, ⟨ha, hab⟩, h⟩
  · rintro ⟨a, b, ⟨ha, rfl⟩, h⟩
    rw [← h]
    exact ⟨⟨a, a, ⟨ha, ha⟩, rfl⟩, rfl⟩

theorem filter_image_mk_not_isDiag [DecidableEq α] (s : Finset α) :
    {a ∈ (s ×ˢ s).image Sym2.mk | ¬a.IsDiag} = s.offDiag.image Sym2.mk := by
  ext z
  induction z
  simp only [mem_image, mem_offDiag, mem_filter, Prod.exists, mem_product]
  constructor
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
    rw [← h, Sym2.mk_isDiag_iff] at hab
    exact ⟨a, b, ⟨ha, hb, hab⟩, h⟩
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, h⟩
    rw [Ne, ← Sym2.mk_isDiag_iff, h] at hab
    exact ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩

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
  ext ⟨i,j⟩
  simp_all only [Pi.smul_apply', lift_mk]

/--
Multiplication as a function from `Sym2`.
-/
def mul {M} [CommMagma M] : Sym2 M → M := lift ⟨(· * ·), mul_comm⟩

@[simp]
lemma mul_mk {M} [CommMagma M] (xy : M × M) :
    mul (.mk xy) = xy.1 * xy.2 := rfl

end Sym2
