/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Pi.Lex
import Mathlib.Data.Set.Intervals.Basic

#align_import data.fin.tuple.basic from "leanprover-community/mathlib"@"ef997baa41b5c428be3fb50089a7139bf4ee886b"

/-!
# Operation on tuples

We interpret maps `∀ i : Fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `Fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `Vector`s.

We define the following operations:

* `Fin.tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `Fin.cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `Fin.init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `Fin.snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `Fin.insertNth` : insert an element to a tuple at a given position.
* `Fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.
* `Fin.append a b` : append two tuples.
* `Fin.repeat n a` : repeat a tuple `n` times.

-/


universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example (α : Fin 0 → Sort u) : Unique (∀ i : Fin 0, α i) := by infer_instance
                                                               -- 🎉 no goals

theorem tuple0_le {α : ∀ _ : Fin 0, Type*} [∀ i, Preorder (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim
#align fin.tuple0_le Fin.tuple0_le

variable {α : Fin (n + 1) → Type u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : ∀ i, α i) : ∀ i : Fin n, α i.succ := fun i ↦ q i.succ
#align fin.tail Fin.tail

theorem tail_def {n : ℕ} {α : Fin (n + 1) → Type*} {q : ∀ i, α i} :
    (tail fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q k.succ :=
  rfl
#align fin.tail_def Fin.tail_def

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : ∀ i : Fin n, α i.succ) : ∀ i, α i := fun j ↦ Fin.cases x p j
#align fin.cons Fin.cons

@[simp]
theorem tail_cons : tail (cons x p) = p := by simp [tail, cons]
                                              -- 🎉 no goals
#align fin.tail_cons Fin.tail_cons

@[simp]
theorem cons_succ : cons x p i.succ = p i := by simp [cons]
                                                -- 🎉 no goals
#align fin.cons_succ Fin.cons_succ

@[simp]
theorem cons_zero : cons x p 0 = x := by simp [cons]
                                         -- 🎉 no goals
#align fin.cons_zero Fin.cons_zero

@[simp]
theorem cons_one {α : Fin (n + 2) → Type*} (x : α 0) (p : ∀ i : Fin n.succ, α i.succ) :
    cons x p 1 = p 0 := by
  rw [← cons_succ x p]; rfl
  -- ⊢ cons x p 1 = cons x p (succ 0)
                        -- 🎉 no goals

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y := by
  ext j
  -- ⊢ cons x (update p i y) j = update (cons x p) (succ i) y j
  by_cases h : j = 0
  -- ⊢ cons x (update p i y) j = update (cons x p) (succ i) y j
  · rw [h]
    -- ⊢ cons x (update p i y) 0 = update (cons x p) (succ i) y 0
    simp [Ne.symm (succ_ne_zero i)]
    -- 🎉 no goals
  · let j' := pred j h
    -- ⊢ cons x (update p i y) j = update (cons x p) (succ i) y j
    have : j'.succ = j := succ_pred j h
    -- ⊢ cons x (update p i y) j = update (cons x p) (succ i) y j
    rw [← this, cons_succ]
    -- ⊢ update p i y j' = update (cons x p) (succ i) y (succ j')
    by_cases h' : j' = i
    -- ⊢ update p i y j' = update (cons x p) (succ i) y (succ j')
    · rw [h']
      -- ⊢ update p i y i = update (cons x p) (succ i) y (succ i)
      simp
      -- 🎉 no goals
    · have : j'.succ ≠ i.succ := by rwa [Ne.def, succ_inj]
      -- ⊢ update p i y j' = update (cons x p) (succ i) y (succ j')
      rw [update_noteq h', update_noteq this, cons_succ]
      -- 🎉 no goals
#align fin.cons_update Fin.cons_update

/-- As a binary function, `Fin.cons` is injective. -/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h ↦
  ⟨congr_fun h 0, funext fun i ↦ by simpa using congr_fun h (Fin.succ i)⟩
                                    -- 🎉 no goals
#align fin.cons_injective2 Fin.cons_injective2

@[simp]
theorem cons_eq_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff
#align fin.cons_eq_cons Fin.cons_eq_cons

theorem cons_left_injective (x : ∀ i : Fin n, α i.succ) : Function.Injective fun x₀ ↦ cons x₀ x :=
  cons_injective2.left _
#align fin.cons_left_injective Fin.cons_left_injective

theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _
#align fin.cons_right_injective Fin.cons_right_injective

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_cons_zero : update (cons x p) 0 z = cons z p := by
  ext j
  -- ⊢ update (cons x p) 0 z j = cons z p j
  by_cases h : j = 0
  -- ⊢ update (cons x p) 0 z j = cons z p j
  · rw [h]
    -- ⊢ update (cons x p) 0 z 0 = cons z p 0
    simp
    -- 🎉 no goals
  · simp only [h, update_noteq, Ne.def, not_false_iff]
    -- ⊢ cons x p j = cons z p j
    let j' := pred j h
    -- ⊢ cons x p j = cons z p j
    have : j'.succ = j := succ_pred j h
    -- ⊢ cons x p j = cons z p j
    rw [← this, cons_succ, cons_succ]
    -- 🎉 no goals
#align fin.update_cons_zero Fin.update_cons_zero

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp, nolint simpNF] -- Porting note: linter claims LHS doesn't simplify
theorem cons_self_tail : cons (q 0) (tail q) = q := by
  ext j
  -- ⊢ cons (q 0) (tail q) j = q j
  by_cases h : j = 0
  -- ⊢ cons (q 0) (tail q) j = q j
  · rw [h]
    -- ⊢ cons (q 0) (tail q) 0 = q 0
    simp
    -- 🎉 no goals
  · let j' := pred j h
    -- ⊢ cons (q 0) (tail q) j = q j
    have : j'.succ = j := succ_pred j h
    -- ⊢ cons (q 0) (tail q) j = q j
    rw [← this]
    -- ⊢ cons (q 0) (tail q) (succ j') = q (succ j')
    unfold tail
    -- ⊢ cons (q 0) (fun i => q (succ i)) (succ j') = q (succ j')
    rw [cons_succ]
    -- 🎉 no goals
#align fin.cons_self_tail Fin.cons_self_tail

-- Porting note: Mathport removes `_root_`?
/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
def consCases {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x : ∀ i : Fin n.succ, α i) : P x :=
  _root_.cast (by rw [cons_self_tail]) <| h (x 0) (tail x)
                  -- 🎉 no goals
#align fin.cons_cases Fin.consCases

@[simp]
theorem consCases_cons {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x₀ : α 0) (x : ∀ i : Fin n, α i.succ) : @consCases _ _ _ h (cons x₀ x) = h x₀ x := by
  rw [consCases, cast_eq]
  -- ⊢ h (cons x₀ x 0) (tail (cons x₀ x)) = h x₀ x
  congr
  -- 🎉 no goals
#align fin.cons_cases_cons Fin.consCases_cons

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.cons`. -/
@[elab_as_elim]
def consInduction {α : Type*} {P : ∀ {n : ℕ}, (Fin n → α) → Sort v} (h0 : P Fin.elim0)
    (h : ∀ {n} (x₀) (x : Fin n → α), P x → P (Fin.cons x₀ x)) : ∀ {n : ℕ} (x : Fin n → α), P x
  | 0, x => by convert h0
               -- 🎉 no goals
  | n + 1, x => consCases (fun x₀ x ↦ h _ _ <| consInduction h0 h _) x
#align fin.cons_induction Fin.consInductionₓ -- Porting note: universes

theorem cons_injective_of_injective {α} {x₀ : α} {x : Fin n → α} (hx₀ : x₀ ∉ Set.range x)
    (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.succ → α) := by
  refine' Fin.cases _ _
  -- ⊢ ∀ ⦃a₂ : Fin (n + 1)⦄, cons x₀ x 0 = cons x₀ x a₂ → 0 = a₂
  · refine' Fin.cases _ _
    -- ⊢ cons x₀ x 0 = cons x₀ x 0 → 0 = 0
    · intro
      -- ⊢ 0 = 0
      rfl
      -- 🎉 no goals
    · intro j h
      -- ⊢ 0 = succ j
      rw [cons_zero, cons_succ] at h
      -- ⊢ 0 = succ j
      exact hx₀.elim ⟨_, h.symm⟩
      -- 🎉 no goals
  · intro i
    -- ⊢ ∀ ⦃a₂ : Fin (n + 1)⦄, cons x₀ x (succ i) = cons x₀ x a₂ → succ i = a₂
    refine' Fin.cases _ _
    -- ⊢ cons x₀ x (succ i) = cons x₀ x 0 → succ i = 0
    · intro h
      -- ⊢ succ i = 0
      rw [cons_zero, cons_succ] at h
      -- ⊢ succ i = 0
      exact hx₀.elim ⟨_, h⟩
      -- 🎉 no goals
    · intro j h
      -- ⊢ succ i = succ j
      rw [cons_succ, cons_succ] at h
      -- ⊢ succ i = succ j
      exact congr_arg _ (hx h)
      -- 🎉 no goals
#align fin.cons_injective_of_injective Fin.cons_injective_of_injective

theorem cons_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (cons x₀ x : Fin n.succ → α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x := by
  refine' ⟨fun h ↦ ⟨_, _⟩, fun h ↦ cons_injective_of_injective h.1 h.2⟩
  -- ⊢ ¬x₀ ∈ Set.range x
  · rintro ⟨i, hi⟩
    -- ⊢ False
    replace h := @h i.succ 0
    -- ⊢ False
    simp [hi, succ_ne_zero] at h
    -- 🎉 no goals
  · simpa [Function.comp] using h.comp (Fin.succ_injective _)
    -- 🎉 no goals
#align fin.cons_injective_iff Fin.cons_injective_iff

@[simp]
theorem forall_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∀ x, P x) ↔ P finZeroElim :=
  ⟨fun h ↦ h _, fun h x ↦ Subsingleton.elim finZeroElim x ▸ h⟩
#align fin.forall_fin_zero_pi Fin.forall_fin_zero_pi

@[simp]
theorem exists_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∃ x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ ↦ Subsingleton.elim x finZeroElim ▸ h, fun h ↦ ⟨_, h⟩⟩
#align fin.exists_fin_zero_pi Fin.exists_fin_zero_pi

theorem forall_fin_succ_pi {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ ∀ a v, P (Fin.cons a v) :=
  ⟨fun h a v ↦ h (Fin.cons a v), consCases⟩
#align fin.forall_fin_succ_pi Fin.forall_fin_succ_pi

theorem exists_fin_succ_pi {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ ∃ a v, P (Fin.cons a v) :=
  ⟨fun ⟨x, h⟩ ↦ ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ ↦ ⟨_, h⟩⟩
#align fin.exists_fin_succ_pi Fin.exists_fin_succ_pi

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
theorem tail_update_zero : tail (update q 0 z) = tail q := by
  ext j
  -- ⊢ tail (update q 0 z) j = tail q j
  simp [tail, Fin.succ_ne_zero]
  -- 🎉 no goals
#align fin.tail_update_zero Fin.tail_update_zero

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y := by
  ext j
  -- ⊢ tail (update q (succ i) y) j = update (tail q) i y j
  by_cases h : j = i
  -- ⊢ tail (update q (succ i) y) j = update (tail q) i y j
  · rw [h]
    -- ⊢ tail (update q (succ i) y) i = update (tail q) i y i
    simp [tail]
    -- 🎉 no goals
  · simp [tail, (Fin.succ_injective n).ne h, h]
    -- 🎉 no goals
#align fin.tail_update_succ Fin.tail_update_succ

theorem comp_cons {α : Type*} {β : Type*} (g : α → β) (y : α) (q : Fin n → α) :
    g ∘ cons y q = cons (g y) (g ∘ q) := by
  ext j
  -- ⊢ (g ∘ cons y q) j = cons (g y) (g ∘ q) j
  by_cases h : j = 0
  -- ⊢ (g ∘ cons y q) j = cons (g y) (g ∘ q) j
  · rw [h]
    -- ⊢ (g ∘ cons y q) 0 = cons (g y) (g ∘ q) 0
    rfl
    -- 🎉 no goals
  · let j' := pred j h
    -- ⊢ (g ∘ cons y q) j = cons (g y) (g ∘ q) j
    have : j'.succ = j := succ_pred j h
    -- ⊢ (g ∘ cons y q) j = cons (g y) (g ∘ q) j
    rw [← this, cons_succ, comp, comp, cons_succ]
    -- 🎉 no goals
#align fin.comp_cons Fin.comp_cons

theorem comp_tail {α : Type*} {β : Type*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ tail q = tail (g ∘ q) := by
  ext j
  -- ⊢ (g ∘ tail q) j = tail (g ∘ q) j
  simp [tail]
  -- 🎉 no goals
#align fin.comp_tail Fin.comp_tail

theorem le_cons [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans <| and_congr Iff.rfl <| forall_congr' fun j ↦ by simp [tail]
                                                                         -- 🎉 no goals
#align fin.le_cons Fin.le_cons

theorem cons_le [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i ↦ (α i)ᵒᵈ) _ x q p
#align fin.cons_le Fin.cons_le

theorem cons_le_cons [∀ i, Preorder (α i)] {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x ≤ cons y₀ y ↔ x₀ ≤ y₀ ∧ x ≤ y :=
  forall_fin_succ.trans <| and_congr_right' <| by simp only [cons_succ, Pi.le_def]
                                                  -- 🎉 no goals
#align fin.cons_le_cons Fin.cons_le_cons

theorem pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ}
    (s : ∀ {i : Fin n.succ}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Fin.cons x₀ x) (Fin.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (@fun i : Fin n ↦ @s i.succ) x y := by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  -- ⊢ (((0 < 0 → cons x₀ x 0 = cons y₀ y 0) ∧ ∀ (i : Fin n), succ i < 0 → cons x₀  …
  simp [and_assoc, exists_and_left]
  -- 🎉 no goals
#align fin.pi_lex_lt_cons_cons Fin.pi_lex_lt_cons_cons

theorem range_fin_succ {α} (f : Fin (n + 1) → α) :
    Set.range f = insert (f 0) (Set.range (Fin.tail f)) :=
  Set.ext fun _ ↦ exists_fin_succ.trans <| eq_comm.or Iff.rfl
#align fin.range_fin_succ Fin.range_fin_succ

@[simp]
theorem range_cons {α : Type*} {n : ℕ} (x : α) (b : Fin n → α) :
    Set.range (Fin.cons x b : Fin n.succ → α) = insert x (Set.range b) := by
  rw [range_fin_succ, cons_zero, tail_cons]
  -- 🎉 no goals
#align fin.range_cons Fin.range_cons

section Append

/-- Append a tuple of length `m` to a tuple of length `n` to get a tuple of length `m + n`.
This is a non-dependent version of `Fin.add_cases`. -/
def append {α : Type*} (a : Fin m → α) (b : Fin n → α) : Fin (m + n) → α :=
  @Fin.addCases _ _ (fun _ => α) a b
#align fin.append Fin.append

@[simp]
theorem append_left {α : Type*} (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i :=
  addCases_left _
#align fin.append_left Fin.append_left

@[simp]
theorem append_right {α : Type*} (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    append u v (natAdd m i) = v i :=
  addCases_right _
#align fin.append_right Fin.append_right

theorem append_right_nil {α : Type*} (u : Fin m → α) (v : Fin n → α) (hv : n = 0) :
    append u v = u ∘ Fin.castIso (by rw [hv, add_zero]) := by
                                     -- 🎉 no goals
  refine' funext (Fin.addCases (fun l => _) fun r => _)
  -- ⊢ append u v (castAdd n l) = (u ∘ ↑(castIso (_ : m + n = m))) (castAdd n l)
  · rw [append_left, Function.comp_apply]
    -- ⊢ u l = u (↑(castIso (_ : m + n = m)) (castAdd n l))
    refine' congr_arg u (Fin.ext _)
    -- ⊢ ↑l = ↑(↑(castIso (_ : m + n = m)) (castAdd n l))
    simp
    -- 🎉 no goals
  · exact (Fin.castIso hv r).elim0'
    -- 🎉 no goals
#align fin.append_right_nil Fin.append_right_nil

@[simp]
theorem append_elim0' {α : Type*} (u : Fin m → α) :
    append u Fin.elim0' = u ∘ Fin.castIso (add_zero _) :=
  append_right_nil _ _ rfl
#align fin.append_elim0' Fin.append_elim0'

theorem append_left_nil {α : Type*} (u : Fin m → α) (v : Fin n → α) (hu : m = 0) :
    append u v = v ∘ Fin.castIso (by rw [hu, zero_add]) := by
                                     -- 🎉 no goals
  refine' funext (Fin.addCases (fun l => _) fun r => _)
  -- ⊢ append u v (castAdd n l) = (v ∘ ↑(castIso (_ : m + n = n))) (castAdd n l)
  · exact (Fin.castIso hu l).elim0'
    -- 🎉 no goals
  · rw [append_right, Function.comp_apply]
    -- ⊢ v r = v (↑(castIso (_ : m + n = n)) (natAdd m r))
    refine' congr_arg v (Fin.ext _)
    -- ⊢ ↑r = ↑(↑(castIso (_ : m + n = n)) (natAdd m r))
    simp [hu]
    -- 🎉 no goals
#align fin.append_left_nil Fin.append_left_nil

@[simp]
theorem elim0'_append {α : Type*} (v : Fin n → α) :
    append Fin.elim0' v = v ∘ Fin.castIso (zero_add _) :=
  append_left_nil _ _ rfl
#align fin.elim0'_append Fin.elim0'_append

theorem append_assoc {p : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) :
    append (append a b) c = append a (append b c) ∘ Fin.castIso (add_assoc _ _ _) := by
  ext i
  -- ⊢ append (append a b) c i = (append a (append b c) ∘ ↑(castIso (_ : m + n + p  …
  rw [Function.comp_apply]
  -- ⊢ append (append a b) c i = append a (append b c) (↑(castIso (_ : m + n + p =  …
  refine' Fin.addCases (fun l => _) (fun r => _) i
  -- ⊢ append (append a b) c (castAdd p l) = append a (append b c) (↑(castIso (_ :  …
  · rw [append_left]
    -- ⊢ append a b l = append a (append b c) (↑(castIso (_ : m + n + p = m + (n + p) …
    refine' Fin.addCases (fun ll => _) (fun lr => _) l
    -- ⊢ append a b (castAdd n ll) = append a (append b c) (↑(castIso (_ : m + n + p  …
    · rw [append_left]
      -- ⊢ a ll = append a (append b c) (↑(castIso (_ : m + n + p = m + (n + p))) (cast …
      -- TODO: we need to decide the simp normal form here
      -- and potentially add `@[simp]` to `castIso_eq_cast`.
      simp [castAdd_castAdd, castIso_eq_cast]
      -- 🎉 no goals
    · rw [append_right]
      -- ⊢ b lr = append a (append b c) (↑(castIso (_ : m + n + p = m + (n + p))) (cast …
      simp [castAdd_natAdd, castIso_eq_cast]
      -- 🎉 no goals
  · rw [append_right]
    -- ⊢ c r = append a (append b c) (↑(castIso (_ : m + n + p = m + (n + p))) (natAd …
    simp [← natAdd_natAdd, castIso_eq_cast]
    -- 🎉 no goals
#align fin.append_assoc Fin.append_assoc

/-- Appending a one-tuple to the left is the same as `Fin.cons`. -/
theorem append_left_eq_cons {α : Type*} {n : ℕ} (x₀ : Fin 1 → α) (x : Fin n → α) :
    Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.castIso (add_comm _ _) := by
  ext i
  -- ⊢ append x₀ x i = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1 + n = n + 1))) i
  refine' Fin.addCases _ _ i <;> clear i
  -- ⊢ ∀ (i : Fin 1), append x₀ x (castAdd n i) = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1 …
                                 -- ⊢ ∀ (i : Fin 1), append x₀ x (castAdd n i) = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1 …
                                 -- ⊢ ∀ (i : Fin n), append x₀ x (natAdd 1 i) = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1  …
  · intro i
    -- ⊢ append x₀ x (castAdd n i) = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1 + n = n + 1))) …
    rw [Subsingleton.elim i 0, Fin.append_left, Function.comp_apply, eq_comm]
    -- ⊢ cons (x₀ 0) x (↑(castIso (_ : 1 + n = n + 1)) (castAdd n 0)) = x₀ 0
    exact Fin.cons_zero _ _
    -- 🎉 no goals
  · intro i
    -- ⊢ append x₀ x (natAdd 1 i) = (cons (x₀ 0) x ∘ ↑(castIso (_ : 1 + n = n + 1)))  …
    rw [Fin.append_right, Function.comp_apply, Fin.castIso_natAdd, eq_comm, Fin.addNat_one]
    -- ⊢ cons (x₀ 0) x (succ i) = x i
    exact Fin.cons_succ _ _ _
    -- 🎉 no goals
#align fin.append_left_eq_cons Fin.append_left_eq_cons

end Append

section Repeat

/-- Repeat `a` `m` times. For example `Fin.repeat 2 ![0, 3, 7] = ![0, 3, 7, 0, 3, 7]`. -/
-- Porting note: removed @[simp]
def «repeat» {α : Type*} (m : ℕ) (a : Fin n → α) : Fin (m * n) → α
  | i => a i.modNat
#align fin.repeat Fin.repeat

-- Porting note: added (leanprover/lean4#2042)
@[simp]
theorem repeat_apply {α : Type*} (a : Fin n → α) (i : Fin (m * n)) :
    Fin.repeat m a i = a i.modNat :=
  rfl

@[simp]
theorem repeat_zero {α : Type*} (a : Fin n → α) :
    Fin.repeat 0 a = Fin.elim0' ∘ castIso (zero_mul _) :=
  funext fun x => (castIso (zero_mul _) x).elim0'
#align fin.repeat_zero Fin.repeat_zero

@[simp]
theorem repeat_one {α : Type*} (a : Fin n → α) : Fin.repeat 1 a = a ∘ castIso (one_mul _) := by
  generalize_proofs h
  -- ⊢ repeat 1 a = a ∘ ↑(castIso h)
  apply funext
  -- ⊢ ∀ (x : Fin (1 * n)), repeat 1 a x = (a ∘ ↑(castIso h)) x
  rw [(Fin.castIso h.symm).surjective.forall]
  -- ⊢ ∀ (x : Fin n), repeat 1 a (↑(castIso (_ : n = 1 * n)) x) = (a ∘ ↑(castIso h) …
  intro i
  -- ⊢ repeat 1 a (↑(castIso (_ : n = 1 * n)) i) = (a ∘ ↑(castIso h)) (↑(castIso (_ …
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]
  -- 🎉 no goals
#align fin.repeat_one Fin.repeat_one

theorem repeat_succ {α : Type*} (a : Fin n → α) (m : ℕ) :
    Fin.repeat m.succ a =
      append a (Fin.repeat m a) ∘ castIso ((Nat.succ_mul _ _).trans (add_comm _ _)) := by
  generalize_proofs h
  -- ⊢ repeat (Nat.succ m) a = append a (repeat m a) ∘ ↑(castIso h)
  apply funext
  -- ⊢ ∀ (x : Fin (Nat.succ m * n)), repeat (Nat.succ m) a x = (append a (repeat m  …
  rw [(Fin.castIso h.symm).surjective.forall]
  -- ⊢ ∀ (x : Fin (n + m * n)), repeat (Nat.succ m) a (↑(castIso (_ : n + m * n = N …
  refine' Fin.addCases (fun l => _) fun r => _
  -- ⊢ repeat (Nat.succ m) a (↑(castIso (_ : n + m * n = Nat.succ m * n)) (castAdd  …
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
    -- 🎉 no goals
  · simp [modNat]
    -- 🎉 no goals
#align fin.repeat_succ Fin.repeat_succ

@[simp]
theorem repeat_add {α : Type*} (a : Fin n → α) (m₁ m₂ : ℕ) : Fin.repeat (m₁ + m₂) a =
    append (Fin.repeat m₁ a) (Fin.repeat m₂ a) ∘ castIso (add_mul _ _ _) := by
  generalize_proofs h
  -- ⊢ repeat (m₁ + m₂) a = append (repeat m₁ a) (repeat m₂ a) ∘ ↑(castIso h)
  apply funext
  -- ⊢ ∀ (x : Fin ((m₁ + m₂) * n)), repeat (m₁ + m₂) a x = (append (repeat m₁ a) (r …
  rw [(Fin.castIso h.symm).surjective.forall]
  -- ⊢ ∀ (x : Fin (m₁ * n + m₂ * n)), repeat (m₁ + m₂) a (↑(castIso (_ : m₁ * n + m …
  refine' Fin.addCases (fun l => _) fun r => _
  -- ⊢ repeat (m₁ + m₂) a (↑(castIso (_ : m₁ * n + m₂ * n = (m₁ + m₂) * n)) (castAd …
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
    -- 🎉 no goals
  · simp [modNat, Nat.add_mod]
    -- 🎉 no goals
#align fin.repeat_add Fin.repeat_add

end Repeat

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `Fin (n+1)` is constructed
inductively from `Fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

-- Porting note: `i.castSucc` does not work like it did in Lean 3;
-- `(castSucc i)` must be used.
variable {α : Fin (n + 1) → Type u} (x : α (last n)) (q : ∀ i, α i)
  (p : ∀ i : Fin n, α (castSucc i)) (i : Fin n) (y : α (castSucc i)) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : ∀ i, α i) (i : Fin n) : α (castSucc i) :=
  q (castSucc i)
#align fin.init Fin.init

theorem init_def {n : ℕ} {α : Fin (n + 1) → Type*} {q : ∀ i, α i} :
    (init fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q (castSucc k) :=
  rfl
#align fin.init_def Fin.init_def

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : ∀ i : Fin n, α (castSucc i)) (x : α (last n)) (i : Fin (n + 1)) : α i :=
  if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
                                        -- 🎉 no goals
  else _root_.cast (by rw [eq_last_of_not_lt h]) x
                       -- 🎉 no goals
#align fin.snoc Fin.snoc

@[simp]
theorem init_snoc : init (snoc p x) = p := by
  ext i
  -- ⊢ init (snoc p x) i = p i
  simp only [init, snoc, coe_castSucc, is_lt, cast_eq, dite_true]
  -- ⊢ p (castLT (castSucc i) (_ : ↑i < n)) = p i
  convert cast_eq rfl (p i)
  -- 🎉 no goals
#align fin.init_snoc Fin.init_snoc

@[simp]
theorem snoc_castSucc : snoc p x (castSucc i) = p i := by
  simp only [snoc, coe_castSucc, is_lt, cast_eq, dite_true]
  -- ⊢ p (castLT (castSucc i) (_ : ↑i < n)) = p i
  convert cast_eq rfl (p i)
  -- 🎉 no goals
#align fin.snoc_cast_succ Fin.snoc_castSucc

@[simp]
theorem snoc_comp_castSucc {n : ℕ} {α : Sort _} {a : α} {f : Fin n → α} :
    (snoc f a : Fin (n + 1) → α) ∘ castSucc = f :=
  funext fun i ↦ by rw [Function.comp_apply, snoc_castSucc]
                    -- 🎉 no goals
#align fin.snoc_comp_cast_succ Fin.snoc_comp_castSucc

@[simp]
theorem snoc_last : snoc p x (last n) = x := by simp [snoc]
                                                -- 🎉 no goals
#align fin.snoc_last Fin.snoc_last

@[simp]
theorem snoc_comp_nat_add {n m : ℕ} {α : Sort _} (f : Fin (m + n) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ (natAdd m : Fin (n + 1) → Fin (m + n + 1)) =
      snoc (f ∘ natAdd m) a := by
  ext i
  -- ⊢ (snoc f a ∘ natAdd m) i = snoc (f ∘ natAdd m) a i
  refine' Fin.lastCases _ (fun i ↦ _) i
  -- ⊢ (snoc f a ∘ natAdd m) (last n) = snoc (f ∘ natAdd m) a (last n)
  · simp only [Function.comp_apply]
    -- ⊢ snoc f a (natAdd m (last n)) = snoc (f ∘ natAdd m) a (last n)
    rw [snoc_last, natAdd_last, snoc_last]
    -- 🎉 no goals
  · simp only [comp_apply, snoc_castSucc]
    -- ⊢ snoc f a (natAdd m (castSucc i)) = f (natAdd m i)
    rw [natAdd_castSucc, snoc_castSucc]
    -- 🎉 no goals
#align fin.snoc_comp_nat_add Fin.snoc_comp_nat_add

@[simp]
theorem snoc_cast_add {α : Fin (n + m + 1) → Type*} (f : ∀ i : Fin (n + m), α (castSucc i))
    (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _
#align fin.snoc_cast_add Fin.snoc_cast_add

-- Porting note: Had to `unfold comp`
@[simp]
theorem snoc_comp_cast_add {n m : ℕ} {α : Sort _} (f : Fin (n + m) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (by unfold comp; exact snoc_cast_add _ _)
             -- ⊢ ∀ (x : Fin n), snoc f a (castAdd (m + 1) x) = f (castAdd m x)
                          -- 🎉 no goals
#align fin.snoc_comp_cast_add Fin.snoc_comp_cast_add

/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
theorem snoc_update : snoc (update p i y) x = update (snoc p x) (castSucc i) y := by
  ext j
  -- ⊢ snoc (update p i y) x j = update (snoc p x) (castSucc i) y j
  by_cases h : j.val < n
  -- ⊢ snoc (update p i y) x j = update (snoc p x) (castSucc i) y j
  · rw [snoc]
    -- ⊢ (if h : ↑j < n then _root_.cast (_ : α (castSucc (castLT j h)) = α j) (updat …
    simp only [h]
    -- ⊢ (if h_1 : True then _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) =  …
    simp only [dif_pos]
    -- ⊢ _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) = α j) (update p i y ( …
    by_cases h' : j = castSucc i
    -- ⊢ _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) = α j) (update p i y ( …
    · have C1 : α (castSucc i) = α j := by rw [h']
      -- ⊢ _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) = α j) (update p i y ( …
      have E1 : update (snoc p x) (castSucc i) y j = _root_.cast C1 y := by
        have : update (snoc p x) j (_root_.cast C1 y) j = _root_.cast C1 y := by simp
        convert this
        · exact h'.symm
        · exact heq_of_cast_eq (congr_arg α (Eq.symm h')) rfl
      have C2 : α (castSucc i) = α (castSucc (castLT j h)) := by rw [castSucc_castLT, h']
      -- ⊢ _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) = α j) (update p i y ( …
      have E2 : update p i y (castLT j h) = _root_.cast C2 y := by
        have : update p (castLT j h) (_root_.cast C2 y) (castLT j h) = _root_.cast C2 y := by simp
        convert this
        · simp [h, h']
        · exact heq_of_cast_eq C2 rfl
      rw [E1, E2]
      -- ⊢ _root_.cast (_ : α (castSucc (castLT j (_ : ↑j < n))) = α j) (_root_.cast C2 …
      exact eq_rec_compose (Eq.trans C2.symm C1) C2 y
      -- 🎉 no goals
    · have : ¬castLT j h = i := by
        intro E
        apply h'
        rw [← E, castSucc_castLT]
      simp [h', this, snoc, h]
      -- 🎉 no goals
  · rw [eq_last_of_not_lt h]
    -- ⊢ snoc (update p i y) x (last n) = update (snoc p x) (castSucc i) y (last n)
    simp [Ne.symm (ne_of_lt (castSucc_lt_last i))]
    -- 🎉 no goals
#align fin.snoc_update Fin.snoc_update

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z := by
  ext j
  -- ⊢ update (snoc p x) (last n) z j = snoc p z j
  by_cases h : j.val < n
  -- ⊢ update (snoc p x) (last n) z j = snoc p z j
  · have : j ≠ last n := ne_of_lt h
    -- ⊢ update (snoc p x) (last n) z j = snoc p z j
    simp [h, update_noteq, this, snoc]
    -- 🎉 no goals
  · rw [eq_last_of_not_lt h]
    -- ⊢ update (snoc p x) (last n) z (last n) = snoc p z (last n)
    simp
    -- 🎉 no goals
#align fin.update_snoc_last Fin.update_snoc_last

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem snoc_init_self : snoc (init q) (q (last n)) = q := by
  ext j
  -- ⊢ snoc (init q) (q (last n)) j = q j
  by_cases h : j.val < n
  -- ⊢ snoc (init q) (q (last n)) j = q j
  · simp only [init, snoc, h, cast_eq, dite_true]
    -- ⊢ q (castSucc (castLT j (_ : ↑j < n))) = q j
    have _ : castSucc (castLT j h) = j := castSucc_castLT _ _
    -- ⊢ q (castSucc (castLT j (_ : ↑j < n))) = q j
    rw [← cast_eq rfl (q j)]
    -- ⊢ q (castSucc (castLT j (_ : ↑j < n))) = _root_.cast (_ : α j = α j) (q j)
    congr
    -- 🎉 no goals
  · rw [eq_last_of_not_lt h]
    -- ⊢ snoc (init q) (q (last n)) (last n) = q (last n)
    simp
    -- 🎉 no goals
#align fin.snoc_init_self Fin.snoc_init_self

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
theorem init_update_last : init (update q (last n) z) = init q := by
  ext j
  -- ⊢ init (update q (last n) z) j = init q j
  simp [init, ne_of_lt, castSucc_lt_last]
  -- 🎉 no goals
#align fin.init_update_last Fin.init_update_last

/-- Updating an element and taking the beginning commute. -/
@[simp]
theorem init_update_castSucc : init (update q (castSucc i) y) = update (init q) i y := by
  ext j
  -- ⊢ init (update q (castSucc i) y) j = update (init q) i y j
  by_cases h : j = i
  -- ⊢ init (update q (castSucc i) y) j = update (init q) i y j
  · rw [h]
    -- ⊢ init (update q (castSucc i) y) i = update (init q) i y i
    simp [init]
    -- 🎉 no goals
  · simp [init, h, castSucc_inj]
    -- 🎉 no goals
#align fin.init_update_cast_succ Fin.init_update_castSucc

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {β : Type*} (q : Fin (n + 2) → β) :
    tail (init q) = init (tail q) := by
  ext i
  -- ⊢ tail (init q) i = init (tail q) i
  simp [tail, init, castSucc_fin_succ]
  -- 🎉 no goals
#align fin.tail_init_eq_init_tail Fin.tail_init_eq_init_tail

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons {β : Type*} (a : β) (q : Fin n → β) (b : β) :
    @cons n.succ (fun _ ↦ β) a (snoc q b) = snoc (cons a q) b := by
  ext i
  -- ⊢ cons a (snoc q b) i = snoc (cons a q) b i
  by_cases h : i = 0
  -- ⊢ cons a (snoc q b) i = snoc (cons a q) b i
  · rw [h]
    -- ⊢ cons a (snoc q b) 0 = snoc (cons a q) b 0
    -- Porting note: `refl` finished it here in Lean 3, but I had to add more.
    simp [snoc, castLT]
    -- 🎉 no goals
  set j := pred i h with ji
  -- ⊢ cons a (snoc q b) i = snoc (cons a q) b i
  have : i = j.succ := by rw [ji, succ_pred]
  -- ⊢ cons a (snoc q b) i = snoc (cons a q) b i
  rw [this, cons_succ]
  -- ⊢ snoc q b j = snoc (cons a q) b (succ j)
  by_cases h' : j.val < n
  -- ⊢ snoc q b j = snoc (cons a q) b (succ j)
  · set k := castLT j h' with jk
    -- ⊢ snoc q b j = snoc (cons a q) b (succ j)
    have : j = castSucc k := by rw [jk, castSucc_castLT]
    -- ⊢ snoc q b j = snoc (cons a q) b (succ j)
    rw [this, ← castSucc_fin_succ, snoc]
    -- ⊢ (if h : ↑(castSucc k) < n then _root_.cast (_ : (fun x => β) (succ (castSucc …
    simp [pred, snoc, cons]
    -- ⊢ (if h_1 : ↑i - 1 < n then q (castLT (subNat 1 i (_ : 0 < ↑i)) (_ : ↑(subNat  …
    rfl
    -- 🎉 no goals
  rw [eq_last_of_not_lt h', succ_last]
  -- ⊢ snoc q b (last n) = snoc (cons a q) b (last (Nat.succ n))
  simp
  -- 🎉 no goals
#align fin.cons_snoc_eq_snoc_cons Fin.cons_snoc_eq_snoc_cons

theorem comp_snoc {α : Type*} {β : Type*} (g : α → β) (q : Fin n → α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) := by
  ext j
  -- ⊢ (g ∘ snoc q y) j = snoc (g ∘ q) (g y) j
  by_cases h : j.val < n
  -- ⊢ (g ∘ snoc q y) j = snoc (g ∘ q) (g y) j
  · simp [h, snoc, castSucc_castLT]
    -- 🎉 no goals
  · rw [eq_last_of_not_lt h]
    -- ⊢ (g ∘ snoc q y) (last n) = snoc (g ∘ q) (g y) (last n)
    simp
    -- 🎉 no goals
#align fin.comp_snoc Fin.comp_snoc

/-- Appending a one-tuple to the right is the same as `Fin.snoc`. -/
theorem append_right_eq_snoc {α : Type*} {n : ℕ} (x : Fin n → α) (x₀ : Fin 1 → α) :
    Fin.append x x₀ = Fin.snoc x (x₀ 0) := by
  ext i
  -- ⊢ append x x₀ i = snoc x (x₀ 0) i
  refine' Fin.addCases _ _ i <;> clear i
  -- ⊢ ∀ (i : Fin n), append x x₀ (castAdd 1 i) = snoc x (x₀ 0) (castAdd 1 i)
                                 -- ⊢ ∀ (i : Fin n), append x x₀ (castAdd 1 i) = snoc x (x₀ 0) (castAdd 1 i)
                                 -- ⊢ ∀ (i : Fin 1), append x x₀ (natAdd n i) = snoc x (x₀ 0) (natAdd n i)
  · intro i
    -- ⊢ append x x₀ (castAdd 1 i) = snoc x (x₀ 0) (castAdd 1 i)
    rw [Fin.append_left]
    -- ⊢ x i = snoc x (x₀ 0) (castAdd 1 i)
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
    -- 🎉 no goals
  · intro i
    -- ⊢ append x x₀ (natAdd n i) = snoc x (x₀ 0) (natAdd n i)
    rw [Subsingleton.elim i 0, Fin.append_right]
    -- ⊢ x₀ 0 = snoc x (x₀ 0) (natAdd n 0)
    exact (@snoc_last _ (fun _ => α) _ _).symm
    -- 🎉 no goals
#align fin.append_right_eq_snoc Fin.append_right_eq_snoc

theorem comp_init {α : Type*} {β : Type*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ init q = init (g ∘ q) := by
  ext j
  -- ⊢ (g ∘ init q) j = init (g ∘ q) j
  simp [init]
  -- 🎉 no goals
#align fin.comp_init Fin.comp_init

end TupleRight

section InsertNth

variable {α : Fin (n + 1) → Type u} {β : Type v}

/- Porting note: Lean told me `(fun x x_1 ↦ α x)` was an invalid motive, but disabling
automatic insertion and specifying that motive seems to work. -/
/-- Define a function on `Fin (n + 1)` from a value on `i : Fin (n + 1)` and values on each
`Fin.succAbove i j`, `j : Fin n`. This version is elaborated as eliminator and works for
propositions, see also `Fin.insertNth` for a version without an `@[elab_as_elim]`
attribute. -/
@[elab_as_elim]
def succAboveCases {α : Fin (n + 1) → Sort u} (i : Fin (n + 1)) (x : α i)
    (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) : α j :=
  if hj : j = i then Eq.rec x hj.symm
  else
    if hlt : j < i then @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_castLT hlt) (p _)
    else @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_pred <| (Ne.lt_or_lt hj).resolve_left hlt) (p _)
#align fin.succ_above_cases Fin.succAboveCases

theorem forall_iff_succAbove {p : Fin (n + 1) → Prop} (i : Fin (n + 1)) :
    (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succAbove j) :=
  ⟨fun h ↦ ⟨h _, fun _ ↦ h _⟩, fun h ↦ succAboveCases i h.1 h.2⟩
#align fin.forall_iff_succ_above Fin.forall_iff_succAbove

/-- Insert an element into a tuple at a given position. For `i = 0` see `Fin.cons`,
for `i = Fin.last n` see `Fin.snoc`. See also `Fin.succAboveCases` for a version elaborated
as an eliminator. -/
def insertNth (i : Fin (n + 1)) (x : α i) (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) :
    α j :=
  succAboveCases i x p j
#align fin.insert_nth Fin.insertNth

@[simp]
theorem insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p i = x := by simp [insertNth, succAboveCases]
                                -- 🎉 no goals
#align fin.insert_nth_apply_same Fin.insertNth_apply_same

@[simp]
theorem insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j))
    (j : Fin n) : insertNth i x p (i.succAbove j) = p j := by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff]
  -- ⊢ (if h : castSucc j < i then (_ : succAbove i (castLT (succAbove i j) (_ : ↑( …
  split_ifs with hlt
  -- ⊢ (_ : succAbove i (castLT (succAbove i j) (_ : ↑(succAbove i j) < n)) = succA …
  · generalize_proofs H₁ H₂; revert H₂
    -- ⊢ H₂ ▸ p (castLT (succAbove i j) H₁) = p j
                             -- ⊢ ∀ (H₂ : succAbove i (castLT (succAbove i j) (_ : ↑(succAbove i j) < n)) = su …
    generalize hk : castLT ((succAbove i) j) H₁ = k
    -- ⊢ ∀ (H₂ : succAbove i k = succAbove i j), H₂ ▸ p k = p j
    rw [castLT_succAbove hlt] at hk; cases hk
    -- ⊢ ∀ (H₂ : succAbove i k = succAbove i j), H₂ ▸ p k = p j
                                     -- ⊢ ∀ (H₂ : succAbove i j = succAbove i j), H₂ ▸ p j = p j
    intro; rfl
    -- ⊢ H₂✝ ▸ p j = p j
           -- 🎉 no goals
  · generalize_proofs H₁ H₂; revert H₂
    -- ⊢ H₂ ▸ p (pred (succAbove i j) H₁) = p j
                             -- ⊢ ∀ (H₂ : succAbove i (pred (succAbove i j) (_ : succAbove i j ≠ 0)) = succAbo …
    generalize hk : pred ((succAboveEmb i).toEmbedding j) H₁ = k
    -- ⊢ ∀ (H₂ : succAbove i k = succAbove i j), H₂ ▸ p k = p j
    erw [pred_succAbove (le_of_not_lt hlt)] at hk; cases hk
    -- ⊢ ∀ (H₂ : succAbove i k = succAbove i j), H₂ ▸ p k = p j
                                                   -- ⊢ ∀ (H₂ : succAbove i j = succAbove i j), H₂ ▸ p j = p j
    intro; rfl
    -- ⊢ H₂✝ ▸ p j = p j
           -- 🎉 no goals
#align fin.insert_nth_apply_succ_above Fin.insertNth_apply_succAbove

@[simp]
theorem succAbove_cases_eq_insertNth : @succAboveCases.{u + 1} = @insertNth.{u} :=
  rfl
#align fin.succ_above_cases_eq_insert_nth Fin.succAbove_cases_eq_insertNth

/- Porting note: Had to `unfold comp`. Sometimes, when I use a placeholder, if I try to insert
what Lean says it synthesized, it gives me a type error anyway. In this case, it's `x` and `p`. -/
@[simp]
theorem insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    insertNth i x p ∘ i.succAbove = p :=
  funext (by unfold comp; exact insertNth_apply_succAbove i _ _)
             -- ⊢ ∀ (x_1 : Fin n), insertNth i x p (succAbove i x_1) = p x_1
                          -- 🎉 no goals
#align fin.insert_nth_comp_succ_above Fin.insertNth_comp_succAbove

theorem insertNth_eq_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p = q ↔ q i = x ∧ p = fun j ↦ q (i.succAbove j) := by
  simp [funext_iff, forall_iff_succAbove i, eq_comm]
  -- 🎉 no goals
#align fin.insert_nth_eq_iff Fin.insertNth_eq_iff

theorem eq_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q = i.insertNth x p ↔ q i = x ∧ p = fun j ↦ q (i.succAbove j) :=
  eq_comm.trans insertNth_eq_iff
#align fin.eq_insert_nth_iff Fin.eq_insertNth_iff

/- Porting note: Once again, Lean told me `(fun x x_1 ↦ α x)` was an invalid motive, but disabling
automatic insertion and specifying that motive seems to work. -/
theorem insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_castLT h) (p <| j.castLT _) := by
  rw [insertNth, succAboveCases, dif_neg h.ne, dif_pos h]
  -- 🎉 no goals
#align fin.insert_nth_apply_below Fin.insertNth_apply_below

/- Porting note: Once again, Lean told me `(fun x x_1 ↦ α x)` was an invalid motive, but disabling
automatic insertion and specifying that motive seems to work. -/
theorem insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_pred h) (p <| j.pred _) := by
  rw [insertNth, succAboveCases, dif_neg h.ne', dif_neg h.not_lt]
  -- 🎉 no goals
#align fin.insert_nth_apply_above Fin.insertNth_apply_above

theorem insertNth_zero (x : α 0) (p : ∀ j : Fin n, α (succAbove 0 j)) :
    insertNth 0 x p =
      cons x fun j ↦ _root_.cast (congr_arg α (congr_fun succAbove_zero j)) (p j) := by
  refine' insertNth_eq_iff.2 ⟨by simp, _⟩
  -- ⊢ p = fun j => cons x (fun j => _root_.cast (_ : α (succAbove 0 j) = α (succ j …
  ext j
  -- ⊢ p j = cons x (fun j => _root_.cast (_ : α (succAbove 0 j) = α (succ j)) (p j …
  convert (cons_succ x p j).symm
  -- 🎉 no goals
#align fin.insert_nth_zero Fin.insertNth_zero

@[simp]
theorem insertNth_zero' (x : β) (p : Fin n → β) : @insertNth _ (fun _ ↦ β) 0 x p = cons x p := by
  simp [insertNth_zero]
  -- 🎉 no goals
#align fin.insert_nth_zero' Fin.insertNth_zero'

theorem insertNth_last (x : α (last n)) (p : ∀ j : Fin n, α ((last n).succAbove j)) :
    insertNth (last n) x p =
      snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x := by
  refine' insertNth_eq_iff.2 ⟨by simp, _⟩
  -- ⊢ p = fun j => snoc (fun j => _root_.cast (_ : α (succAbove (last n) j) = α (c …
  ext j
  -- ⊢ p j = snoc (fun j => _root_.cast (_ : α (succAbove (last n) j) = α (castSucc …
  apply eq_of_heq
  -- ⊢ HEq (p j) (snoc (fun j => _root_.cast (_ : α (succAbove (last n) j) = α (cas …
  trans snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x (castSucc j)
  -- ⊢ HEq (p j) (snoc (fun j => _root_.cast (_ : α (succAbove (last n) j) = α (cas …
  · rw [snoc_castSucc]
    -- ⊢ HEq (p j) (_root_.cast (_ : α (succAbove (last n) j) = α (castSucc j)) (p j))
    exact (cast_heq _ _).symm
    -- 🎉 no goals
  · apply congr_arg_heq
    -- ⊢ castSucc j = succAbove (last n) j
    rw [succAbove_last]
    -- 🎉 no goals
#align fin.insert_nth_last Fin.insertNth_last

@[simp]
theorem insertNth_last' (x : β) (p : Fin n → β) :
    @insertNth _ (fun _ ↦ β) (last n) x p = snoc p x := by simp [insertNth_last]
                                                           -- 🎉 no goals
#align fin.insert_nth_last' Fin.insertNth_last'

@[simp]
theorem insertNth_zero_right [∀ j, Zero (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 0 = Pi.single i x :=
  insertNth_eq_iff.2 <| by simp [succAbove_ne, Pi.zero_def]
                           -- 🎉 no goals
#align fin.insert_nth_zero_right Fin.insertNth_zero_right

theorem insertNth_binop (op : ∀ j, α j → α j → α j) (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j ↦ op _ (p j) (q j)) = fun j ↦
      op j (i.insertNth x p j) (i.insertNth y q j) :=
  insertNth_eq_iff.2 <| by simp
                           -- 🎉 no goals
#align fin.insert_nth_binop Fin.insertNth_binop

@[simp]
theorem insertNth_mul [∀ j, Mul (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· * ·)) i x y p q
#align fin.insert_nth_mul Fin.insertNth_mul

@[simp]
theorem insertNth_add [∀ j, Add (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x + y) (p + q) = i.insertNth x p + i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· + ·)) i x y p q
#align fin.insert_nth_add Fin.insertNth_add

@[simp]
theorem insertNth_div [∀ j, Div (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· / ·)) i x y p q
#align fin.insert_nth_div Fin.insertNth_div

@[simp]
theorem insertNth_sub [∀ j, Sub (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x - y) (p - q) = i.insertNth x p - i.insertNth y q :=
  insertNth_binop (fun _ ↦ Sub.sub) i x y p q
#align fin.insert_nth_sub Fin.insertNth_sub

@[simp]
theorem insertNth_sub_same [∀ j, AddGroup (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p - i.insertNth y p = Pi.single i (x - y) := by
  simp_rw [← insertNth_sub, ← insertNth_zero_right, Pi.sub_def, sub_self, Pi.zero_def]
  -- 🎉 no goals
#align fin.insert_nth_sub_same Fin.insertNth_sub_same

variable [∀ i, Preorder (α i)]

theorem insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j ↦ q (i.succAbove j) := by
  simp [Pi.le_def, forall_iff_succAbove i]
  -- 🎉 no goals
#align fin.insert_nth_le_iff Fin.insertNth_le_iff

theorem le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q ≤ i.insertNth x p ↔ q i ≤ x ∧ (fun j ↦ q (i.succAbove j)) ≤ p := by
  simp [Pi.le_def, forall_iff_succAbove i]
  -- 🎉 no goals
#align fin.le_insert_nth_iff Fin.le_insertNth_iff

open Set

theorem insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)}
    {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) := by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x ≤ q₂ i)]
  -- 🎉 no goals
#align fin.insert_nth_mem_Icc Fin.insertNth_mem_Icc

theorem preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j ↦ q₁ (i.succAbove j)) fun j ↦ q₂ (i.succAbove j) :=
  Set.ext fun p ↦ by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and_iff]
                     -- 🎉 no goals
#align fin.preimage_insert_nth_Icc_of_mem Fin.preimage_insertNth_Icc_of_mem

theorem preimage_insertNth_Icc_of_not_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p ↦ by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and_iff, mem_empty_iff_false]
    -- 🎉 no goals
#align fin.preimage_insert_nth_Icc_of_not_mem Fin.preimage_insertNth_Icc_of_not_mem

end InsertNth

section Find

/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p], Option (Fin n)
  | 0, _p, _ => none
  | n + 1, p, _ => by
    exact
      Option.casesOn (@find n (fun i ↦ p (i.castLT (Nat.lt_succ_of_lt i.2))) _)
        (if _ : p (Fin.last n) then some (Fin.last n) else none) fun i ↦
        some (i.castLT (Nat.lt_succ_of_lt i.2))
#align fin.find Fin.find

/-- If `find p = some i`, then `p i` holds -/
theorem find_spec :
    ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {i : Fin n} (_ : i ∈ Fin.find p), p i
  | 0, p, I, i, hi => Option.noConfusion hi
  | n + 1, p, I, i, hi => by
    rw [find] at hi
    -- ⊢ p i
    cases' h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with j
    -- ⊢ p i
    · rw [h] at hi
      -- ⊢ p i
      dsimp at hi
      -- ⊢ p i
      split_ifs at hi with hl
      -- ⊢ p i
      · simp only [Option.mem_def, Option.some.injEq] at hi
        -- ⊢ p i
        exact hi ▸ hl
        -- 🎉 no goals
      · exact (Option.not_mem_none _ hi).elim
        -- 🎉 no goals
    · rw [h] at hi
      -- ⊢ p i
      dsimp at hi
      -- ⊢ p i
      rw [← Option.some_inj.1 hi]
      -- ⊢ p (castLT j (_ : ↑j < Nat.succ n))
      refine @find_spec n (fun i ↦ p (i.castLT (Nat.lt_succ_of_lt i.2))) _ _ h
      -- 🎉 no goals
#align fin.find_spec Fin.find_spec

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem isSome_find_iff :
    ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p], (find p).isSome ↔ ∃ i, p i
  | 0, p, _ => iff_of_false (fun h ↦ Bool.noConfusion h) fun ⟨i, _⟩ ↦ Fin.elim0' i
  | n + 1, p, _ =>
    ⟨fun h ↦ by
      rw [Option.isSome_iff_exists] at h
      -- ⊢ ∃ i, p i
      cases' h with i hi
      -- ⊢ ∃ i, p i
      exact ⟨i, find_spec _ hi⟩, fun ⟨⟨i, hin⟩, hi⟩ ↦ by
      -- 🎉 no goals
      dsimp [find]
      -- ⊢ Option.isSome (Option.rec (if p (last n) then some (last n) else none) (fun  …
      cases' h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with j
      -- ⊢ Option.isSome (Option.rec (if p (last n) then some (last n) else none) (fun  …
      · split_ifs with hl
        -- ⊢ Option.isSome (Option.rec (some (last n)) (fun val => some (castLT val (_ :  …
        · exact Option.isSome_some
          -- 🎉 no goals
        · have := (@isSome_find_iff n (fun x ↦ p (x.castLT (Nat.lt_succ_of_lt x.2))) _).2
              ⟨⟨i, lt_of_le_of_ne (Nat.le_of_lt_succ hin) fun h ↦ by cases h; exact hl hi⟩, hi⟩
          rw [h] at this
          -- ⊢ Option.isSome (Option.rec none (fun val => some (castLT val (_ : ↑val < Nat. …
          exact this
          -- 🎉 no goals
      · simp⟩
        -- 🎉 no goals
#align fin.is_some_find_iff Fin.isSome_find_iff

/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : Fin n → Prop} [DecidablePred p] :
    find p = none ↔ ∀ i, ¬p i := by rw [← not_exists, ← isSome_find_iff]; cases find p <;> simp
                                    -- ⊢ find p = none ↔ ¬Option.isSome (find fun x => p x) = true
                                                                          -- ⊢ none = none ↔ ¬Option.isSome none = true
                                                                                           -- 🎉 no goals
                                                                                           -- 🎉 no goals
#align fin.find_eq_none_iff Fin.find_eq_none_iff

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min :
    ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (_ : i ∈ Fin.find p) {j : Fin n}
      (_ : j < i), ¬p j
  | 0, p, _, i, hi, _, _, _ => Option.noConfusion hi
  | n + 1, p, _, i, hi, ⟨j, hjn⟩, hj, hpj => by
    rw [find] at hi
    -- ⊢ False
    cases' h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with k
    -- ⊢ False
    · simp only [h] at hi
      -- ⊢ False
      split_ifs at hi with hl
      -- ⊢ False
      · cases hi
        -- ⊢ False
        rw [find_eq_none_iff] at h
        -- ⊢ False
        refine h ⟨j, hj⟩ hpj
        -- 🎉 no goals
      · exact Option.not_mem_none _ hi
        -- 🎉 no goals
    · rw [h] at hi
      -- ⊢ False
      dsimp at hi
      -- ⊢ False
      obtain rfl := Option.some_inj.1 hi
      -- ⊢ False
      exact find_min h (show (⟨j, lt_trans hj k.2⟩ : Fin n) < k from hj) hpj
      -- 🎉 no goals
#align fin.find_min Fin.find_min

theorem find_min' {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (h : i ∈ Fin.find p) {j : Fin n}
    (hj : p j) : i ≤ j :=
  le_of_not_gt fun hij ↦ find_min h hij hj
#align fin.find_min' Fin.find_min'

theorem nat_find_mem_find {p : Fin n → Prop} [DecidablePred p]
    (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
    (⟨Nat.find h, (Nat.find_spec h).fst⟩ : Fin n) ∈ find p := by
  let ⟨i, hin, hi⟩ := h
  -- ⊢ { val := Nat.find (_ : ∃ i hin, p { val := i, isLt := hin }), isLt := (_ : N …
  cases' hf : find p with f
  -- ⊢ { val := Nat.find (_ : ∃ i hin, p { val := i, isLt := hin }), isLt := (_ : N …
  · rw [find_eq_none_iff] at hf
    -- ⊢ { val := Nat.find (_ : ∃ i hin, p { val := i, isLt := hin }), isLt := (_ : N …
    exact (hf ⟨i, hin⟩ hi).elim
    -- 🎉 no goals
  · refine' Option.some_inj.2 (le_antisymm _ _)
    -- ⊢ f ≤ { val := Nat.find (_ : ∃ i hin, p { val := i, isLt := hin }), isLt := (_ …
    · exact find_min' hf (Nat.find_spec h).snd
      -- 🎉 no goals
    · exact Nat.find_min' _ ⟨f.2, by convert find_spec p hf⟩
      -- 🎉 no goals
#align fin.nat_find_mem_find Fin.nat_find_mem_find

theorem mem_find_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    i ∈ Fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
  ⟨fun hi ↦ ⟨find_spec _ hi, fun _ ↦ find_min' hi⟩, by
    rintro ⟨hpi, hj⟩
    -- ⊢ i ∈ find p
    cases hfp : Fin.find p
    -- ⊢ i ∈ none
    · rw [find_eq_none_iff] at hfp
      -- ⊢ i ∈ none
      exact (hfp _ hpi).elim
      -- 🎉 no goals
    · exact Option.some_inj.2 (le_antisymm (find_min' hfp hpi) (hj _ (find_spec _ hfp)))⟩
      -- 🎉 no goals
#align fin.mem_find_iff Fin.mem_find_iff

theorem find_eq_some_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    Fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
  mem_find_iff
#align fin.find_eq_some_iff Fin.find_eq_some_iff

theorem mem_find_of_unique {p : Fin n → Prop} [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    {i : Fin n} (hi : p i) : i ∈ Fin.find p :=
  mem_find_iff.2 ⟨hi, fun j hj ↦ le_of_eq <| h i j hi hj⟩
#align fin.mem_find_of_unique Fin.mem_find_of_unique

end Find

section ContractNth

variable {α : Type*}

/-- Sends `(g₀, ..., gₙ)` to `(g₀, ..., op gⱼ gⱼ₊₁, ..., gₙ)`. -/
def contractNth (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n) : α :=
  if (k : ℕ) < j then g (Fin.castSucc k)
  else if (k : ℕ) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ
#align fin.contract_nth Fin.contractNth

theorem contractNth_apply_of_lt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) < j) : contractNth j op g k = g (Fin.castSucc k) :=
  if_pos h
#align fin.contract_nth_apply_of_lt Fin.contractNth_apply_of_lt

theorem contractNth_apply_of_eq (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) = j) : contractNth j op g k = op (g (Fin.castSucc k)) (g k.succ) := by
  have : ¬(k : ℕ) < j := not_lt.2 (le_of_eq h.symm)
  -- ⊢ contractNth j op g k = op (g (castSucc k)) (g (succ k))
  rw [contractNth, if_neg this, if_pos h]
  -- 🎉 no goals
#align fin.contract_nth_apply_of_eq Fin.contractNth_apply_of_eq

theorem contractNth_apply_of_gt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (j : ℕ) < k) : contractNth j op g k = g k.succ := by
  rw [contractNth, if_neg (not_lt_of_gt h), if_neg (Ne.symm <| ne_of_lt h)]
  -- 🎉 no goals
#align fin.contract_nth_apply_of_gt Fin.contractNth_apply_of_gt

theorem contractNth_apply_of_ne (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (hjk : (j : ℕ) ≠ k) : contractNth j op g k = g (j.succAbove k) := by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [j.succAbove_below, contractNth_apply_of_lt]
    -- ⊢ castSucc k < j
    · rwa [Fin.lt_iff_val_lt_val]
      -- 🎉 no goals
  · exact False.elim (hjk h.symm)
    -- 🎉 no goals
  · rwa [j.succAbove_above, contractNth_apply_of_gt]
    -- ⊢ j ≤ castSucc k
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)
      -- 🎉 no goals
#align fin.contract_nth_apply_of_ne Fin.contractNth_apply_of_ne

end ContractNth

/-- To show two sigma pairs of tuples agree, it to show the second elements are related via
`Fin.castIso`. -/
theorem sigma_eq_of_eq_comp_castIso {α : Type*} :
    ∀ {a b : Σii, Fin ii → α} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.castIso h → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    -- ⊢ { fst := ai, snd := a } = { fst := bi, snd := b }
    subst hi
    -- ⊢ { fst := ai, snd := a } = { fst := ai, snd := b }
    simpa using h
    -- 🎉 no goals
#align fin.sigma_eq_of_eq_comp_cast Fin.sigma_eq_of_eq_comp_castIso

/-- `Fin.sigma_eq_of_eq_comp_castIso` as an `iff`. -/
theorem sigma_eq_iff_eq_comp_castIso {α : Type*} {a b : Σii, Fin ii → α} :
    a = b ↔ ∃ h : a.fst = b.fst, a.snd = b.snd ∘ Fin.castIso h :=
  ⟨fun h ↦ h ▸ ⟨rfl, funext <| Fin.rec fun _ _ ↦ rfl⟩, fun ⟨_, h'⟩ ↦
    sigma_eq_of_eq_comp_castIso _ h'⟩
#align fin.sigma_eq_iff_eq_comp_cast Fin.sigma_eq_iff_eq_comp_castIso

end Fin
