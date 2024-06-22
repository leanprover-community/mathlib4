/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Set.Lattice

#align_import data.semiquot from "leanprover-community/mathlib"@"09597669f02422ed388036273d8848119699c22f"

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/


/-- A member of `Semiquot α` is classically a nonempty `Set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
  -- Porting note: removed universe parameter
structure Semiquot (α : Type*) where mk' ::
  /-- Set containing some element of `α`-/
  s : Set α
  /-- Assertion of non-emptiness via `Trunc`-/
  val : Trunc s
#align semiquot Semiquot

namespace Semiquot

variable {α : Type*} {β : Type*}

instance : Membership α (Semiquot α) :=
  ⟨fun a q => a ∈ q.s⟩

/-- Construct a `Semiquot α` from `h : a ∈ s` where `s : Set α`. -/
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩
#align semiquot.mk Semiquot.mk

theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s := by
  refine ⟨congr_arg _, fun h => ?_⟩
  cases' q₁ with _ v₁; cases' q₂ with _ v₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂
#align semiquot.ext_s Semiquot.ext_s

theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff
#align semiquot.ext Semiquot.ext

theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩
#align semiquot.exists_mem Semiquot.exists_mem

theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl
#align semiquot.eq_mk_of_mem Semiquot.eq_mk_of_mem

theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem
#align semiquot.nonempty Semiquot.nonempty

/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)
#align semiquot.pure Semiquot.pure

@[simp]
theorem mem_pure' {a b : α} : a ∈ Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff
#align semiquot.mem_pure' Semiquot.mem_pure'

/-- Replace `s` in a `Semiquot` with a superset. -/
def blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩
#align semiquot.blur' Semiquot.blur'

/-- Replace `s` in a `q : Semiquot α` with a union `s ∪ q.s` -/
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (s.subset_union_right (t := q.s))
#align semiquot.blur Semiquot.blur

theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s ⊆ s) : blur s q = blur' q h := by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h
#align semiquot.blur_eq_blur' Semiquot.blur_eq_blur'

@[simp]
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) {a : α} : a ∈ blur' q h ↔ a ∈ s :=
  Iff.rfl
#align semiquot.mem_blur' Semiquot.mem_blur'

/-- Convert a `Trunc α` to a `Semiquot α`. -/
def ofTrunc (q : Trunc α) : Semiquot α :=
  ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩
#align semiquot.of_trunc Semiquot.ofTrunc

/-- Convert a `Semiquot α` to a `Trunc α`. -/
def toTrunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val
#align semiquot.to_trunc Semiquot.toTrunc

/-- If `f` is a constant on `q.s`, then `q.liftOn f` is the value of `f`
at any point of `q`. -/
def liftOn (q : Semiquot α) (f : α → β) (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2
#align semiquot.lift_on Semiquot.liftOn

theorem liftOn_ofMem (q : Semiquot α) (f : α → β)
    (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) (a : α) (aq : a ∈ q) : liftOn q f h = f a := by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl
#align semiquot.lift_on_of_mem Semiquot.liftOn_ofMem

/-- Apply a function to the unknown value stored in a `Semiquot α`. -/
def map (f : α → β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩
#align semiquot.map Semiquot.map

@[simp]
theorem mem_map (f : α → β) (q : Semiquot α) (b : β) : b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b :=
  Set.mem_image _ _ _
#align semiquot.mem_map Semiquot.mem_map

/-- Apply a function returning a `Semiquot` to a `Semiquot`. -/
def bind (q : Semiquot α) (f : α → Semiquot β) : Semiquot β :=
  ⟨⋃ a ∈ q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩
#align semiquot.bind Semiquot.bind

@[simp]
theorem mem_bind (q : Semiquot α) (f : α → Semiquot β) (b : β) :
    b ∈ bind q f ↔ ∃ a ∈ q, b ∈ f a := by simp_rw [← exists_prop]; exact Set.mem_iUnion₂
#align semiquot.mem_bind Semiquot.mem_bind

instance : Monad Semiquot where
  pure := @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

@[simp]
theorem map_def {β} : ((· <$> ·) : (α → β) → Semiquot α → Semiquot β) = map :=
  rfl
#align semiquot.map_def Semiquot.map_def

@[simp]
theorem bind_def {β} : ((· >>= ·) : Semiquot α → (α → Semiquot β) → Semiquot β) = bind :=
  rfl
#align semiquot.bind_def Semiquot.bind_def

@[simp]
theorem mem_pure {a b : α} : a ∈ (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff
#align semiquot.mem_pure Semiquot.mem_pure

theorem mem_pure_self (a : α) : a ∈ (pure a : Semiquot α) :=
  Set.mem_singleton a
#align semiquot.mem_pure_self Semiquot.mem_pure_self

@[simp]
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff
#align semiquot.pure_inj Semiquot.pure_inj

instance : LawfulMonad Semiquot := LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
    ext.2 <| by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ext.2 <| by simp)
  (bind_pure_comp := fun {α β} f s => ext.2 <| by simp [eq_comm])

instance : LE (Semiquot α) :=
  ⟨fun s t => s.s ⊆ t.s⟩

instance partialOrder : PartialOrder (Semiquot α) where
  le s t := ∀ ⦃x⦄, x ∈ s → x ∈ t
  le_refl s := Set.Subset.refl _
  le_trans s t u := Set.Subset.trans
  le_antisymm s t h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)

instance : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }

@[simp]
theorem pure_le {a : α} {s : Semiquot α} : pure a ≤ s ↔ a ∈ s :=
  Set.singleton_subset_iff
#align semiquot.pure_le Semiquot.pure_le

/-- Assert that a `Semiquot` contains only one possible value. -/
def IsPure (q : Semiquot α) : Prop :=
  ∀ a ∈ q, ∀ b ∈ q, a = b
#align semiquot.is_pure Semiquot.IsPure

/-- Extract the value from an `IsPure` semiquotient. -/
def get (q : Semiquot α) (h : q.IsPure) : α :=
  liftOn q id h
#align semiquot.get Semiquot.get

theorem get_mem {q : Semiquot α} (p) : get q p ∈ q := by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h
#align semiquot.get_mem Semiquot.get_mem

theorem eq_pure {q : Semiquot α} (p) : q = pure (get q p) :=
  ext.2 fun a => by simp; exact ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩
#align semiquot.eq_pure Semiquot.eq_pure

@[simp]
theorem pure_isPure (a : α) : IsPure (pure a)
  | b, ab, c, ac => by
    rw [mem_pure] at ab ac
    rwa [← ac] at ab
#align semiquot.pure_is_pure Semiquot.pure_isPure

theorem isPure_iff {s : Semiquot α} : IsPure s ↔ ∃ a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩
#align semiquot.is_pure_iff Semiquot.isPure_iff

theorem IsPure.mono {s t : Semiquot α} (st : s ≤ t) (h : IsPure t) : IsPure s
  | _, as, _, bs => h _ (st as) _ (st bs)
#align semiquot.is_pure.mono Semiquot.IsPure.mono

theorem IsPure.min {s t : Semiquot α} (h : IsPure t) : s ≤ t ↔ s = t :=
  ⟨fun st =>
    le_antisymm st <| by
      rw [eq_pure h, eq_pure (h.mono st)]; simp; exact h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩
#align semiquot.is_pure.min Semiquot.IsPure.min

theorem isPure_of_subsingleton [Subsingleton α] (q : Semiquot α) : IsPure q
  | _, _, _, _ => Subsingleton.elim _ _
#align semiquot.is_pure_of_subsingleton Semiquot.isPure_of_subsingleton

/-- `univ : Semiquot α` represents an unspecified element of `univ : Set α`. -/
def univ [Inhabited α] : Semiquot α :=
  mk <| Set.mem_univ default
#align semiquot.univ Semiquot.univ

instance [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩

@[simp]
theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
  @Set.mem_univ α
#align semiquot.mem_univ Semiquot.mem_univ

@[congr]
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2 fun a => refl (a ∈ univ)
#align semiquot.univ_unique Semiquot.univ_unique

@[simp]
theorem isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩
#align semiquot.is_pure_univ Semiquot.isPure_univ

instance [Inhabited α] : OrderTop (Semiquot α) where
  top := univ
  le_top _ := Set.subset_univ _

end Semiquot
