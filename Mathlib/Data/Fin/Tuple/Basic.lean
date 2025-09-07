/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes, Antoine Chambert-Loir
-/
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic

/-!
# Operation on tuples

We interpret maps `∀ i : Fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `Fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `Vector`s.

## Main declarations

There are three (main) ways to consider `Fin n` as a subtype of `Fin (n + 1)`, hence three (main)
ways to move between tuples of length `n` and of length `n + 1` by adding/removing an entry.

### Adding at the start

* `Fin.succ`: Send `i : Fin n` to `i + 1 : Fin (n + 1)`. This is defined in Core.
* `Fin.cases`: Induction/recursion principle for `Fin`: To prove a property/define a function for
  all `Fin (n + 1)`, it is enough to prove/define it for `0` and for `i.succ` for all `i : Fin n`.
  This is defined in Core.
* `Fin.cons`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.cons a f : Fin (n + 1) → α` by adding `a` at the start. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.succ` and `a : α 0`. This is a special case of
  `Fin.cases`.
* `Fin.tail`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.tail f : Fin n → α` by forgetting
  the start. In general, tuples can be dependent functions,
  in which case `Fin.tail f : ∀ i : Fin n, α i.succ`.

### Adding at the end

* `Fin.castSucc`: Send `i : Fin n` to `i : Fin (n + 1)`. This is defined in Core.
* `Fin.lastCases`: Induction/recursion principle for `Fin`: To prove a property/define a function
  for all `Fin (n + 1)`, it is enough to prove/define it for `last n` and for `i.castSucc` for all
  `i : Fin n`. This is defined in Core.
* `Fin.snoc`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.snoc f a : Fin (n + 1) → α` by adding `a` at the end. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.castSucc` and `a : α (last n)`. This is a
  special case of `Fin.lastCases`.
* `Fin.init`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.init f : Fin n → α` by forgetting
  the end. In general, tuples can be dependent functions,
  in which case `Fin.init f : ∀ i : Fin n, α i.castSucc`.

### Adding in the middle

For a **pivot** `p : Fin (n + 1)`,
* `Fin.succAbove`: Send `i : Fin n` to
  * `i : Fin (n + 1)` if `i < p`,
  * `i + 1 : Fin (n + 1)` if `p ≤ i`.
* `Fin.succAboveCases`: Induction/recursion principle for `Fin`: To prove a property/define a
  function for all `Fin (n + 1)`, it is enough to prove/define it for `p` and for `p.succAbove i`
  for all `i : Fin n`.
* `Fin.insertNth`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.insertNth f a : Fin (n + 1) → α` by adding `a` in position `p`. In general, tuples can be
  dependent functions, in which case `f : ∀ i : Fin n, α (p.succAbove i)` and `a : α p`. This is a
  special case of `Fin.succAboveCases`.
* `Fin.removeNth`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.removeNth p f : Fin n → α`
  by forgetting the `p`-th value. In general, tuples can be dependent functions,
  in which case `Fin.removeNth f : ∀ i : Fin n, α (succAbove p i)`.

`p = 0` means we add at the start. `p = last n` means we add at the end.

### Miscellaneous

* `Fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.
* `Fin.append a b` : append two tuples.
* `Fin.repeat n a` : repeat a tuple `n` times.

-/

assert_not_exists Monoid

universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example (α : Fin 0 → Sort u) : Unique (∀ i : Fin 0, α i) := by infer_instance

theorem tuple0_le {α : Fin 0 → Type*} [∀ i, Preorder (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim

variable {α : Fin (n + 1) → Sort u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : ∀ i, α i) : ∀ i : Fin n, α i.succ := fun i ↦ q i.succ

theorem tail_def {n : ℕ} {α : Fin (n + 1) → Sort*} {q : ∀ i, α i} :
    (tail fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q k.succ :=
  rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : ∀ i : Fin n, α i.succ) : ∀ i, α i := fun j ↦ Fin.cases x p j

@[simp]
theorem tail_cons : tail (cons x p) = p := by
  simp +unfoldPartialApp [tail, cons]

@[simp]
theorem cons_succ : cons x p i.succ = p i := by simp [cons]

@[simp]
theorem cons_zero : cons x p 0 = x := by simp [cons]

@[simp]
theorem cons_one {α : Fin (n + 2) → Sort*} (x : α 0) (p : ∀ i : Fin n.succ, α i.succ) :
    cons x p 1 = p 0 := by
  rw [← cons_succ x p]; rfl

@[simp]
theorem cons_last {α : Fin (n + 2) → Sort*} (x : α 0) (p : ∀ i : Fin n.succ, α i.succ) :
    cons x p (.last _) = p (.last _) := by
  rw [← cons_succ x p]; rfl

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y := by
  ext j
  cases j using Fin.cases <;> simp [Ne.symm, update_apply_of_injective _ (succ_injective _)]

/-- As a binary function, `Fin.cons` is injective. -/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h ↦
  ⟨congr_fun h 0, funext fun i ↦ by simpa using congr_fun h (Fin.succ i)⟩

@[simp]
theorem cons_inj {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff

theorem cons_left_injective (x : ∀ i : Fin n, α i.succ) : Function.Injective fun x₀ ↦ cons x₀ x :=
  cons_injective2.left _

theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
@[simp]
theorem update_cons_zero : update (cons x p) 0 z = cons z p := by
  ext j
  cases j using Fin.cases <;> simp

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem cons_self_tail : cons (q 0) (tail q) = q := by
  ext j
  cases j using Fin.cases <;> simp [tail]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the first element of the tuple.

This is `Fin.cons` as an `Equiv`. -/
@[simps]
def consEquiv (α : Fin (n + 1) → Type*) : α 0 × (∀ i, α (succ i)) ≃ ∀ i, α i where
  toFun f := cons f.1 f.2
  invFun f := (f 0, tail f)
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
def consCases {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x : ∀ i : Fin n.succ, α i) : P x :=
  _root_.cast (by rw [cons_self_tail]) <| h (x 0) (tail x)

@[simp]
theorem consCases_cons {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x₀ : α 0) (x : ∀ i : Fin n, α i.succ) : consCases h (cons x₀ x) = h x₀ x := by
  rw [consCases, cast_eq]
  congr

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.cons`. -/
@[elab_as_elim]
def consInduction {α : Sort*} {P : ∀ {n : ℕ}, (Fin n → α) → Sort v} (h0 : P Fin.elim0)
    (h : ∀ {n} (x₀) (x : Fin n → α), P x → P (Fin.cons x₀ x)) : ∀ {n : ℕ} (x : Fin n → α), P x
  | 0, x => by convert h0
  | _ + 1, x => consCases (fun _ _ ↦ h _ _ <| consInduction h0 h _) x

theorem cons_injective_of_injective {α} {x₀ : α} {x : Fin n → α} (hx₀ : x₀ ∉ Set.range x)
    (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.succ → α) := by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> aesop (add simp [hx.eq_iff])

theorem cons_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (cons x₀ x : Fin n.succ → α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simp [hi] at h
  · simpa [Function.comp] using h.comp (Fin.succ_injective _)

@[simp]
theorem forall_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∀ x, P x) ↔ P finZeroElim :=
  ⟨fun h ↦ h _, fun h x ↦ Subsingleton.elim finZeroElim x ▸ h⟩

@[simp]
theorem exists_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∃ x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ ↦ Subsingleton.elim x finZeroElim ▸ h, fun h ↦ ⟨_, h⟩⟩

theorem forall_fin_succ_pi {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ ∀ a v, P (Fin.cons a v) :=
  ⟨fun h a v ↦ h (Fin.cons a v), consCases⟩

theorem exists_fin_succ_pi {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ ∃ a v, P (Fin.cons a v) :=
  ⟨fun ⟨x, h⟩ ↦ ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ ↦ ⟨_, h⟩⟩

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
theorem tail_update_zero : tail (update q 0 z) = tail q := by
  ext j
  simp [tail]

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [tail]
  · simp [tail, (Fin.succ_injective n).ne h, h]

theorem comp_cons {α : Sort*} {β : Sort*} (g : α → β) (y : α) (q : Fin n → α) :
    g ∘ cons y q = cons (g y) (g ∘ q) := by
  ext j
  by_cases h : j = 0
  · rw [h]
    rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, comp_apply, comp_apply, cons_succ]

theorem comp_tail {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ tail q = tail (g ∘ q) := by
  ext j
  simp [tail]

section Preorder

variable {α : Fin (n + 1) → Type*}

theorem le_cons [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans <| and_congr Iff.rfl <| forall_congr' fun j ↦ by simp [tail]

theorem cons_le [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i ↦ (α i)ᵒᵈ) _ x q p

theorem cons_le_cons [∀ i, Preorder (α i)] {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x ≤ cons y₀ y ↔ x₀ ≤ y₀ ∧ x ≤ y :=
  forall_fin_succ.trans <| and_congr_right' <| by simp only [cons_succ, Pi.le_def]

end Preorder

theorem range_fin_succ {α} (f : Fin (n + 1) → α) :
    Set.range f = insert (f 0) (Set.range (Fin.tail f)) :=
  Set.ext fun _ ↦ exists_fin_succ.trans <| eq_comm.or Iff.rfl

@[simp]
theorem range_cons {α} {n : ℕ} (x : α) (b : Fin n → α) :
    Set.range (Fin.cons x b : Fin n.succ → α) = insert x (Set.range b) := by
  rw [range_fin_succ, cons_zero, tail_cons]

section Append

variable {α : Sort*}

/-- Append a tuple of length `m` to a tuple of length `n` to get a tuple of length `m + n`.
This is a non-dependent version of `Fin.add_cases`. -/
def append (a : Fin m → α) (b : Fin n → α) : Fin (m + n) → α :=
  @Fin.addCases _ _ (fun _ => α) a b

@[simp]
theorem append_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i :=
  addCases_left _

/-- Variant of `append_left` using `Fin.castLE` instead of `Fin.castAdd`. -/
@[simp]
theorem append_left' (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castLE (by omega) i) = u i :=
  addCases_left _

@[simp]
theorem append_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    append u v (natAdd m i) = v i :=
  addCases_right _

theorem append_right_nil (u : Fin m → α) (v : Fin n → α) (hv : n = 0) :
    append u v = u ∘ Fin.cast (by rw [hv, Nat.add_zero]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [append_left, Function.comp_apply]
    refine congr_arg u (Fin.ext ?_)
    simp
  · exact (Fin.cast hv r).elim0

@[simp]
theorem append_elim0 (u : Fin m → α) :
    append u Fin.elim0 = u ∘ Fin.cast (Nat.add_zero _) :=
  append_right_nil _ _ rfl

theorem append_left_nil (u : Fin m → α) (v : Fin n → α) (hu : m = 0) :
    append u v = v ∘ Fin.cast (by rw [hu, Nat.zero_add]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · exact (Fin.cast hu l).elim0
  · rw [append_right, Function.comp_apply]
    refine congr_arg v (Fin.ext ?_)
    simp [hu]

@[simp]
theorem elim0_append (v : Fin n → α) :
    append Fin.elim0 v = v ∘ Fin.cast (Nat.zero_add _) :=
  append_left_nil _ _ rfl

theorem append_assoc {p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) :
    append (append a b) c = append a (append b c) ∘ Fin.cast (Nat.add_assoc ..) := by
  ext i
  rw [Function.comp_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [append_left]
    refine Fin.addCases (fun ll => ?_) (fun lr => ?_) l
    · rw [append_left]
      simp [castAdd_castAdd]
    · rw [append_right]
      simp [castAdd_natAdd]
  · rw [append_right]
    simp [← natAdd_natAdd]

/-- Appending a one-tuple to the left is the same as `Fin.cons`. -/
theorem append_left_eq_cons {n : ℕ} (x₀ : Fin 1 → α) (x : Fin n → α) :
    Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm ..) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_left, Function.comp_apply, eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right, Function.comp_apply, Fin.cast_natAdd, eq_comm, Fin.addNat_one]
    exact Fin.cons_succ _ _ _

/-- `Fin.cons` is the same as appending a one-tuple to the left. -/
theorem cons_eq_append (x : α) (xs : Fin n → α) :
    cons x xs = append (cons x Fin.elim0) xs ∘ Fin.cast (Nat.add_comm ..) := by
  funext i; simp [append_left_eq_cons]

@[simp] lemma append_cast_left {n m} (xs : Fin n → α) (ys : Fin m → α) (n' : ℕ)
    (h : n' = n) :
    Fin.append (xs ∘ Fin.cast h) ys = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp

@[simp] lemma append_cast_right {n m} (xs : Fin n → α) (ys : Fin m → α) (m' : ℕ)
    (h : m' = m) :
    Fin.append xs (ys ∘ Fin.cast h) = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp

lemma append_rev {m n} (xs : Fin m → α) (ys : Fin n → α) (i : Fin (m + n)) :
    append xs ys (rev i) = append (ys ∘ rev) (xs ∘ rev) (i.cast (Nat.add_comm ..)) := by
  rcases rev_surjective i with ⟨i, rfl⟩
  rw [rev_rev]
  induction i using Fin.addCases
  · simp [rev_castAdd]
  · simp [cast_rev, rev_addNat]

lemma append_comp_rev {m n} (xs : Fin m → α) (ys : Fin n → α) :
    append xs ys ∘ rev = append (ys ∘ rev) (xs ∘ rev) ∘ Fin.cast (Nat.add_comm ..) :=
  funext <| append_rev xs ys

theorem append_castAdd_natAdd {f : Fin (m + n) → α} :
    append (fun i ↦ f (castAdd n i)) (fun i ↦ f (natAdd m i)) = f := by
  unfold append addCases
  simp

/-- Splitting a dependent finite sequence v into an initial part and a final part,
and then concatenating these components, produces an identical sequence. -/
theorem addCases_castAdd_natAdd {γ : Fin (m + n) → Sort*} (v : ∀ i, γ i) :
    addCases (fun i ↦ v (castAdd n i)) (fun j ↦ v (natAdd m j)) = v := by
  ext i
  cases i using addCases <;> simp

theorem append_comp_sumElim {xs : Fin m → α} {ys : Fin n → α} :
    Fin.append xs ys ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _) = Sum.elim xs ys := by
  ext (i | j) <;> simp

theorem append_injective_iff {xs : Fin m → α} {ys : Fin n → α} :
    Function.Injective (Fin.append xs ys) ↔
      Function.Injective xs ∧ Function.Injective ys ∧ ∀ i j, xs i ≠ ys j := by
  -- TODO: move things around so we can just import this.
  -- We inline it because it's still shorter than proving from scratch.
  let finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
    left_inv x := by rcases x with y | y <;> simp
    right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp }
  rw [← Sum.elim_injective, ← append_comp_sumElim, ← finSumFinEquiv.injective_comp,
    Equiv.coe_fn_mk]

end Append

section Repeat

variable {α : Sort*}

/-- Repeat `a` `m` times. For example `Fin.repeat 2 ![0, 3, 7] = ![0, 3, 7, 0, 3, 7]`. -/
def «repeat» (m : ℕ) (a : Fin n → α) : Fin (m * n) → α
  | i => a i.modNat

@[simp]
theorem repeat_apply (a : Fin n → α) (i : Fin (m * n)) :
    Fin.repeat m a i = a i.modNat :=
  rfl

@[simp]
theorem repeat_zero (a : Fin n → α) :
    Fin.repeat 0 a = Fin.elim0 ∘ Fin.cast (Nat.zero_mul _) :=
  funext fun x => (x.cast (Nat.zero_mul _)).elim0

@[simp]
theorem repeat_one (a : Fin n → α) : Fin.repeat 1 a = a ∘ Fin.cast (Nat.one_mul _) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  intro i
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]

theorem repeat_succ (a : Fin n → α) (m : ℕ) :
    Fin.repeat m.succ a =
      append a (Fin.repeat m a) ∘ Fin.cast ((Nat.succ_mul _ _).trans (Nat.add_comm ..)) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
  · simp [modNat]

@[simp]
theorem repeat_add (a : Fin n → α) (m₁ m₂ : ℕ) : Fin.repeat (m₁ + m₂) a =
    append (Fin.repeat m₁ a) (Fin.repeat m₂ a) ∘ Fin.cast (Nat.add_mul ..) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat]
  · simp [modNat, Nat.add_mod]

theorem repeat_rev (a : Fin n → α) (k : Fin (m * n)) :
    Fin.repeat m a k.rev = Fin.repeat m (a ∘ Fin.rev) k :=
  congr_arg a k.modNat_rev

theorem repeat_comp_rev (a : Fin n → α) :
    Fin.repeat m a ∘ Fin.rev = Fin.repeat m (a ∘ Fin.rev) :=
  funext <| repeat_rev a

end Repeat

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `Fin (n+1)` is constructed
inductively from `Fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

variable {α : Fin (n + 1) → Sort*} (x : α (last n)) (q : ∀ i, α i)
  (p : ∀ i : Fin n, α i.castSucc) (i : Fin n) (y : α i.castSucc) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : ∀ i, α i) (i : Fin n) : α i.castSucc :=
  q i.castSucc

theorem init_def {q : ∀ i, α i} :
    (init fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q k.castSucc :=
  rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : ∀ i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1)) : α i :=
  if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else _root_.cast (by rw [eq_last_of_not_lt h]) x

@[simp]
theorem init_snoc : init (snoc p x) = p := by
  ext i
  simp only [init, snoc, coe_castSucc, is_lt, cast_eq, dite_true]
  convert cast_eq rfl (p i)

@[simp]
theorem snoc_castSucc : snoc p x i.castSucc = p i := by
  simp only [snoc, coe_castSucc, is_lt, cast_eq, dite_true]
  convert cast_eq rfl (p i)

@[simp]
theorem snoc_apply_zero [NeZero n] : snoc p x 0 = p 0 := snoc_castSucc x p 0

@[simp]
theorem snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin n → α} :
    (snoc f a : Fin (n + 1) → α) ∘ castSucc = f :=
  funext fun i ↦ by rw [Function.comp_apply, snoc_castSucc]

@[simp]
theorem snoc_last : snoc p x (last n) = x := by simp [snoc]

lemma snoc_zero {α : Sort*} (p : Fin 0 → α) (x : α) :
    Fin.snoc p x = fun _ ↦ x := by
  ext y
  have : Subsingleton (Fin (0 + 1)) := Fin.subsingleton_one
  simp only [Subsingleton.elim y (Fin.last 0), snoc_last]

@[simp]
theorem snoc_comp_natAdd {n m : ℕ} {α : Sort*} (f : Fin (m + n) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ (natAdd m : Fin (n + 1) → Fin (m + n + 1)) =
      snoc (f ∘ natAdd m) a := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [Function.comp_apply]
    rw [snoc_last, natAdd_last, snoc_last]
  · simp only [comp_apply, snoc_castSucc]
    rw [natAdd_castSucc, snoc_castSucc]

@[deprecated (since := "2025-07-04")] alias snoc_comp_nat_add := snoc_comp_natAdd

@[simp]
theorem snoc_castAdd {α : Fin (n + m + 1) → Sort*} (f : ∀ i : Fin (n + m), α i.castSucc)
    (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _

@[deprecated (since := "2025-07-04")] alias snoc_cast_add := snoc_castAdd

@[simp]
theorem snoc_comp_castAdd {n m : ℕ} {α : Sort*} (f : Fin (n + m) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (snoc_castAdd _ _)

@[deprecated (since := "2025-07-04")] alias snoc_comp_cast_add := snoc_comp_castAdd

/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
theorem snoc_update : snoc (update p i y) x = update (snoc p x) i.castSucc y := by
  ext j
  cases j using lastCases with
  | cast j => rcases eq_or_ne j i with rfl | hne <;> simp [*]
  | last => simp [Ne.symm]

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z := by
  ext j
  cases j using lastCases <;> simp

@[simp]
lemma range_snoc {α : Type*} (f : Fin n → α) (x : α) :
    Set.range (snoc f x) = insert x (Set.range f) := by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

/-- As a binary function, `Fin.snoc` is injective. -/
theorem snoc_injective2 : Function.Injective2 (@snoc n α) := fun x y xₙ yₙ h ↦
  ⟨funext fun i ↦ by simpa using congr_fun h (castSucc i), by simpa using congr_fun h (last n)⟩

@[simp]
theorem snoc_inj {x y : ∀ i : Fin n, α i.castSucc} {xₙ yₙ : α (last n)} :
    snoc x xₙ = snoc y yₙ ↔ x = y ∧ xₙ = yₙ :=
  snoc_injective2.eq_iff

theorem snoc_right_injective (x : ∀ i : Fin n, α i.castSucc) :
    Function.Injective (snoc x) :=
  snoc_injective2.right _

theorem snoc_left_injective (xₙ : α (last n)) : Function.Injective (snoc · xₙ) :=
  snoc_injective2.left _

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem snoc_init_self : snoc (init q) (q (last n)) = q := by
  ext j
  cases j using Fin.lastCases <;> simp [init]

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
theorem init_update_last : init (update q (last n) z) = init q := by
  ext j
  simp [init, Fin.ne_of_lt]

/-- Updating an element and taking the beginning commute. -/
@[simp]
theorem init_update_castSucc : init (update q i.castSucc y) = update (init q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [init]
  · simp [init, h, castSucc_inj]

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {β : Sort*} (q : Fin (n + 2) → β) :
    tail (init q) = init (tail q) := by
  ext i
  simp [tail, init]

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons {β : Sort*} (a : β) (q : Fin n → β) (b : β) :
    @cons n.succ (fun _ ↦ β) a (snoc q b) = snoc (cons a q) b := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [cons_succ]
      simp [← castSucc_succ]

theorem comp_snoc {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n → α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) := by
  ext j
  by_cases h : j.val < n
  · simp [h, snoc, castSucc_castLT]
  · rw [eq_last_of_not_lt h]
    simp

/-- Appending a one-tuple to the right is the same as `Fin.snoc`. -/
theorem append_right_eq_snoc {α : Sort*} {n : ℕ} (x : Fin n → α) (x₀ : Fin 1 → α) :
    Fin.append x x₀ = Fin.snoc x (x₀ 0) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm

/-- `Fin.snoc` is the same as appending a one-tuple -/
theorem snoc_eq_append {α : Sort*} (xs : Fin n → α) (x : α) :
    snoc xs x = append xs (cons x Fin.elim0) :=
  (append_right_eq_snoc xs (cons x Fin.elim0)).symm

theorem append_left_snoc {n m} {α : Sort*} (xs : Fin n → α) (x : α) (ys : Fin m → α) :
    Fin.append (Fin.snoc xs x) ys =
      Fin.append xs (Fin.cons x ys) ∘ Fin.cast (Nat.succ_add_eq_add_succ ..) := by
  rw [snoc_eq_append, append_assoc, append_left_eq_cons, append_cast_right]; rfl

theorem append_right_cons {n m} {α : Sort*} (xs : Fin n → α) (y : α) (ys : Fin m → α) :
    Fin.append xs (Fin.cons y ys) =
      Fin.append (Fin.snoc xs y) ys ∘ Fin.cast (Nat.succ_add_eq_add_succ ..).symm := by
  rw [append_left_snoc]; rfl

theorem append_cons {α : Sort*} (a : α) (as : Fin n → α) (bs : Fin m → α) :
    Fin.append (cons a as) bs
    = cons a (Fin.append as bs) ∘ (Fin.cast <| Nat.add_right_comm n 1 m) := by
  funext i
  rcases i with ⟨i, -⟩
  simp only [append, addCases, cons, castLT, comp_apply]
  rcases i with - | i
  · simp
  · split_ifs with h
    · have : i < n := Nat.lt_of_succ_lt_succ h
      simp [addCases, this]
    · have : ¬i < n := Nat.not_le.mpr <| Nat.lt_succ.mp <| Nat.not_le.mp h
      simp [addCases, this]

theorem append_snoc {α : Sort*} (as : Fin n → α) (bs : Fin m → α) (b : α) :
    Fin.append as (snoc bs b) = snoc (Fin.append as bs) b := by
  funext i
  rcases i with ⟨i, isLt⟩
  simp only [append, addCases, castLT, cast_mk, subNat_mk, natAdd_mk, cast, snoc.eq_1,
    eq_rec_constant, Nat.add_eq, castLT_mk]
  split_ifs with lt_n lt_add sub_lt nlt_add lt_add <;> (try rfl)
  · have := Nat.lt_add_right m lt_n
    contradiction
  · obtain rfl := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp nlt_add) isLt
    simp [Nat.add_comm n m] at sub_lt
  · have := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp lt_n) lt_add
    contradiction

theorem comp_init {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ init q = init (g ∘ q) := by
  ext j
  simp [init]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the last element of the tuple.

This is `Fin.snoc` as an `Equiv`. -/
@[simps]
def snocEquiv (α : Fin (n + 1) → Type*) : α (last n) × (∀ i, α (castSucc i)) ≃ ∀ i, α i where
  toFun f _ := Fin.snoc f.2 f.1 _
  invFun f := ⟨f _, Fin.init f⟩
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it its initial `n`-tuple and its last element. -/
@[elab_as_elim, inline]
def snocCases {P : (∀ i : Fin n.succ, α i) → Sort*}
    (h : ∀ xs x, P (Fin.snoc xs x))
    (x : ∀ i : Fin n.succ, α i) : P x :=
  _root_.cast (by rw [Fin.snoc_init_self]) <| h (Fin.init x) (x <| Fin.last _)

@[simp] lemma snocCases_snoc
    {P : (∀ i : Fin (n + 1), α i) → Sort*} (h : ∀ x x₀, P (Fin.snoc x x₀))
    (x : ∀ i : Fin n, (Fin.init α) i) (x₀ : α (Fin.last _)) :
    snocCases h (Fin.snoc x x₀) = h x x₀ := by
  rw [snocCases, cast_eq_iff_heq, Fin.init_snoc, Fin.snoc_last]

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.snoc`. -/
@[elab_as_elim]
def snocInduction {α : Sort*}
    {P : ∀ {n : ℕ}, (Fin n → α) → Sort*}
    (h0 : P Fin.elim0)
    (h : ∀ {n} (x : Fin n → α) (x₀), P x → P (Fin.snoc x x₀)) : ∀ {n : ℕ} (x : Fin n → α), P x
  | 0, x => by convert h0
  | _ + 1, x => snocCases (fun _ _ ↦ h _ _ <| snocInduction h0 h _) x

theorem snoc_injective_of_injective {α} {x₀ : α} {x : Fin n → α}
    (hx : Function.Injective x) (hx₀ : x₀ ∉ Set.range x) :
    Function.Injective (snoc x x₀ : Fin n.succ → α) := fun i j h ↦ by
  induction i using lastCases with
  | cast i =>
    induction j using lastCases with
    | cast j =>
      simpa only [castSucc_inj, ← Injective.eq_iff hx, snoc_castSucc] using h
    | last =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [← h] at hx₀
      apply hx₀.elim (Set.mem_range_self i)
  | last =>
    induction j using lastCases with
    | cast j =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [h] at hx₀
      apply hx₀.elim (Set.mem_range_self j)
    | last => simp

theorem snoc_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (snoc x x₀ : Fin n.succ → α) ↔ Function.Injective x ∧ x₀ ∉ Set.range x := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ snoc_injective_of_injective h.1 h.2⟩
  · simpa [Function.comp] using h.comp (Fin.castSucc_injective _)
  · rintro ⟨i, hi⟩
    rw [← @snoc_last n (fun i ↦ α) x₀ x, ← @snoc_castSucc n (fun i ↦ α) x₀ x i,
      h.eq_iff] at hi
    exact ne_last_of_lt i.castSucc_lt_last hi

end TupleRight

section InsertNth

variable {α : Fin (n + 1) → Sort*} {β : Sort*}

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
    if hlt : j < i then @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_castPred_of_lt _ _ hlt) (p _)
    else @Eq.recOn _ _ (fun x _ ↦ α x) _ (succAbove_pred_of_lt _ _ <|
    (Fin.lt_or_lt_of_ne hj).resolve_left hlt) (p _)

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias forall_iff_succ := forall_fin_succ

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias exists_iff_succ := exists_fin_succ

lemma forall_iff_castSucc {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ P (last n) ∧ ∀ i : Fin n, P i.castSucc :=
  ⟨fun h ↦ ⟨h _, fun _ ↦ h _⟩, fun h ↦ lastCases h.1 h.2⟩

/-- A finite sequence of properties P holds for {0 , ... , m + n - 1} iff
it holds separately for both {0 , ... , m - 1} and {m, ..., m + n - 1}. -/
theorem forall_fin_add {m n} (P : Fin (m + n) → Prop) :
    (∀ i, P i) ↔ (∀ i, P (castAdd _ i)) ∧ (∀ j, P (natAdd _ j)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hm, hn⟩ => Fin.addCases hm hn⟩

/-- A property holds for all dependent finite sequence of length m + n iff
it holds for the concatenation of all pairs of length m sequences and length n sequences. -/
theorem forall_fin_add_pi {γ : Fin (m + n) → Sort*} {P : (∀ i, γ i) → Prop} :
    (∀ v, P v) ↔
      (∀ (vₘ : ∀ i, γ (castAdd n i)) (vₙ : ∀ j, γ (natAdd m j)), P (addCases vₘ vₙ)) where
  mp hv vm vn := hv (addCases vm vn)
  mpr h v := by
    convert h (fun i => v (castAdd n i)) (fun j => v (natAdd m j))
    exact (addCases_castAdd_natAdd v).symm

lemma exists_iff_castSucc {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ P (last n) ∨ ∃ i : Fin n, P i.castSucc where
  mp := by
    rintro ⟨i, hi⟩
    cases i using lastCases with
    | last => exact .inl hi
    | cast _ => exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

theorem forall_iff_succAbove {P : Fin (n + 1) → Prop} (p : Fin (n + 1)) :
    (∀ i, P i) ↔ P p ∧ ∀ i, P (p.succAbove i) :=
  ⟨fun h ↦ ⟨h _, fun _ ↦ h _⟩, fun h ↦ succAboveCases p h.1 h.2⟩

lemma exists_iff_succAbove {P : Fin (n + 1) → Prop} (p : Fin (n + 1)) :
    (∃ i, P i) ↔ P p ∨ ∃ i, P (p.succAbove i) where
  mp := by
    rintro ⟨i, hi⟩
    induction' i using p.succAboveCases
    · exact .inl hi
    · exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

/-- Analogue of `Fin.eq_zero_or_eq_succ` for `succAbove`. -/
theorem eq_self_or_eq_succAbove (p i : Fin (n + 1)) : i = p ∨ ∃ j, i = p.succAbove j :=
  succAboveCases p (.inl rfl) (fun j => .inr ⟨j, rfl⟩) i

/-- Remove the `p`-th entry of a tuple. -/
def removeNth (p : Fin (n + 1)) (f : ∀ i, α i) : ∀ i, α (p.succAbove i) := fun i ↦ f (p.succAbove i)

/-- Insert an element into a tuple at a given position. For `i = 0` see `Fin.cons`,
for `i = Fin.last n` see `Fin.snoc`. See also `Fin.succAboveCases` for a version elaborated
as an eliminator. -/
def insertNth (i : Fin (n + 1)) (x : α i) (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) :
    α j :=
  succAboveCases i x p j

@[simp]
theorem insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p i = x := by simp [insertNth, succAboveCases]

@[simp]
theorem insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j))
    (j : Fin n) : insertNth i x p (i.succAbove j) = p j := by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff_castSucc_lt]
  split_ifs with hlt
  · generalize_proofs H₁ H₂; revert H₂
    generalize hk : castPred ((succAbove i) j) H₁ = k
    rw [castPred_succAbove _ _ hlt] at hk; cases hk
    intro; rfl
  · generalize_proofs H₀ H₁ H₂; revert H₂
    generalize hk : pred (succAbove i j) H₁ = k
    rw [pred_succAbove _ _ (Fin.not_lt.1 hlt)] at hk; cases hk
    intro; rfl

@[simp]
theorem succAbove_cases_eq_insertNth : @succAboveCases = @insertNth :=
  rfl

lemma removeNth_apply (p : Fin (n + 1)) (f : ∀ i, α i) (i : Fin n) :
    p.removeNth f i = f (p.succAbove i) :=
  rfl

@[simp] lemma removeNth_insertNth (p : Fin (n + 1)) (a : α p) (f : ∀ i, α (succAbove p i)) :
    removeNth p (insertNth p a f) = f := by ext; unfold removeNth; simp

@[simp] lemma removeNth_zero (f : ∀ i, α i) : removeNth 0 f = tail f := by
  ext; simp [tail, removeNth]

@[simp] lemma removeNth_last {α : Type*} (f : Fin (n + 1) → α) : removeNth (last n) f = init f := by
  ext; simp [init, removeNth]

@[simp]
theorem insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    insertNth i x p ∘ i.succAbove = p :=
  funext (insertNth_apply_succAbove i _ _)

theorem insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : ∀ i, α (p.succAbove i)} {g : ∀ j, α j} :
    insertNth p a f = g ↔ a = g p ∧ f = removeNth p g := by
  simp [funext_iff, forall_iff_succAbove p, removeNth]

theorem eq_insertNth_iff {p : Fin (n + 1)} {a : α p} {f : ∀ i, α (p.succAbove i)} {g : ∀ j, α j} :
    g = insertNth p a f ↔ g p = a ∧ removeNth p g = f := by
  simpa [eq_comm] using insertNth_eq_iff

/-- As a binary function, `Fin.insertNth` is injective. -/
theorem insertNth_injective2 {p : Fin (n + 1)} :
    Function.Injective2 (@insertNth n α p) := fun xₚ yₚ x y h ↦
  ⟨by simpa using congr_fun h p, funext fun i ↦ by simpa using congr_fun h (succAbove p i)⟩

@[simp]
theorem insertNth_inj {p : Fin (n + 1)} {x y : ∀ i, α (succAbove p i)} {xₚ yₚ : α p} :
    insertNth p xₚ x = insertNth p yₚ y ↔ xₚ = yₚ ∧ x = y :=
  insertNth_injective2.eq_iff

theorem insertNth_left_injective {p : Fin (n + 1)} (x : ∀ i, α (succAbove p i)) :
    Function.Injective (insertNth p · x) :=
  insertNth_injective2.left _

theorem insertNth_right_injective {p : Fin (n + 1)} (x : α p) :
    Function.Injective (insertNth p x) :=
  insertNth_injective2.right _

/- Porting note: Once again, Lean told me `(fun x x_1 ↦ α x)` was an invalid motive, but disabling
automatic insertion and specifying that motive seems to work. -/
theorem insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = @Eq.recOn _ _ (fun x _ ↦ α x) _
    (succAbove_castPred_of_lt _ _ h) (p <| j.castPred _) := by
  rw [insertNth, succAboveCases, dif_neg (Fin.ne_of_lt h), dif_pos h]

/- Porting note: Once again, Lean told me `(fun x x_1 ↦ α x)` was an invalid motive, but disabling
automatic insertion and specifying that motive seems to work. -/
theorem insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = @Eq.recOn _ _ (fun x _ ↦ α x) _
    (succAbove_pred_of_lt _ _ h) (p <| j.pred _) := by
  rw [insertNth, succAboveCases, dif_neg (Fin.ne_of_gt h), dif_neg (Fin.lt_asymm h)]

theorem insertNth_zero (x : α 0) (p : ∀ j : Fin n, α (succAbove 0 j)) :
    insertNth 0 x p =
      cons x fun j ↦ _root_.cast (congr_arg α (congr_fun succAbove_zero j)) (p j) := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  convert (cons_succ x p j).symm

@[simp]
theorem insertNth_zero' (x : β) (p : Fin n → β) : @insertNth _ (fun _ ↦ β) 0 x p = cons x p := by
  simp [insertNth_zero]

theorem insertNth_last (x : α (last n)) (p : ∀ j : Fin n, α ((last n).succAbove j)) :
    insertNth (last n) x p =
      snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x j.castSucc
  · rw [snoc_castSucc]
    exact (cast_heq _ _).symm
  · apply congr_arg_heq
    rw [succAbove_last]

@[simp]
theorem insertNth_last' (x : β) (p : Fin n → β) :
    @insertNth _ (fun _ ↦ β) (last n) x p = snoc p x := by simp [insertNth_last]

lemma insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (f : Fin n → α) (j : Fin (n + 1)) :
    insertNth (α := fun _ ↦ α) i a f (rev j) = insertNth (α := fun _ ↦ α) i.rev a (f ∘ rev) j := by
  induction j using Fin.succAboveCases
  · exact rev i
  · simp
  · simp [rev_succAbove]

theorem insertNth_comp_rev {α} (i : Fin (n + 1)) (x : α) (p : Fin n → α) :
    (Fin.insertNth i x p) ∘ Fin.rev = Fin.insertNth (Fin.rev i) x (p ∘ Fin.rev) := by
  funext x
  apply insertNth_rev

theorem cons_rev {α n} (a : α) (f : Fin n → α) (i : Fin <| n + 1) :
    cons (α := fun _ => α) a f i.rev = snoc (α := fun _ => α) (f ∘ Fin.rev : Fin _ → α) a i := by
  simpa using insertNth_rev 0 a f i

theorem cons_comp_rev {α n} (a : α) (f : Fin n → α) :
    Fin.cons a f ∘ Fin.rev = Fin.snoc (f ∘ Fin.rev) a := by
  funext i; exact cons_rev ..

theorem snoc_rev {α n} (a : α) (f : Fin n → α) (i : Fin <| n + 1) :
    snoc (α := fun _ => α) f a i.rev = cons (α := fun _ => α) a (f ∘ Fin.rev : Fin _ → α) i := by
  simpa using insertNth_rev (last n) a f i

theorem snoc_comp_rev {α n} (a : α) (f : Fin n → α) :
    Fin.snoc f a ∘ Fin.rev = Fin.cons a (f ∘ Fin.rev) :=
  funext <| snoc_rev a f

theorem insertNth_binop (op : ∀ j, α j → α j → α j) (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j ↦ op _ (p j) (q j)) = fun j ↦
      op j (i.insertNth x p j) (i.insertNth y q j) :=
  insertNth_eq_iff.2 <| by unfold removeNth; simp

section Preorder

variable {α : Fin (n + 1) → Type*} [∀ i, Preorder (α i)]

theorem insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j ↦ q (i.succAbove j) := by
  simp [Pi.le_def, forall_iff_succAbove i]

theorem le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q ≤ i.insertNth x p ↔ q i ≤ x ∧ (fun j ↦ q (i.succAbove j)) ≤ p := by
  simp [Pi.le_def, forall_iff_succAbove i]

end Preorder

open Set

@[simp] lemma removeNth_update (p : Fin (n + 1)) (x) (f : ∀ j, α j) :
    removeNth p (update f p x) = removeNth p f := by ext i; simp [removeNth]

@[simp]
lemma removeNth_update_succAbove (p : Fin (n + 1)) (i : Fin n) (x : α (p.succAbove i))
    (f : ∀ j, α j) :
    removeNth p (update f (p.succAbove i) x) = update (removeNth p f) i x := by
  ext j
  rcases eq_or_ne j i with rfl | hne <;> simp [removeNth, *]

@[simp] lemma insertNth_removeNth (p : Fin (n + 1)) (x) (f : ∀ j, α j) :
    insertNth p x (removeNth p f) = update f p x := by simp [Fin.insertNth_eq_iff]

lemma insertNth_self_removeNth (p : Fin (n + 1)) (f : ∀ j, α j) :
    insertNth p (f p) (removeNth p f) = f := by simp

@[simp]
theorem update_insertNth (p : Fin (n + 1)) (x y : α p) (f : ∀ i, α (p.succAbove i)) :
    update (p.insertNth x f) p y = p.insertNth y f := by
  simp [eq_insertNth_iff]

@[simp]
theorem insertNth_update (p : Fin (n + 1)) (x : α p) (i : Fin n) (y : α (p.succAbove i))
    (f : ∀ j, α (p.succAbove j)) :
    p.insertNth x (update f i y) = update (p.insertNth x f) (p.succAbove i) y := by
  simp [insertNth_eq_iff]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `Equiv`. -/
@[simps]
def insertNthEquiv (α : Fin (n + 1) → Type u) (p : Fin (n + 1)) :
    α p × (∀ i, α (p.succAbove i)) ≃ ∀ i, α i where
  toFun f := insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp

@[simp] lemma insertNthEquiv_zero (α : Fin (n + 1) → Type*) : insertNthEquiv α 0 = consEquiv α :=
  Equiv.symm_bijective.injective <| by ext <;> rfl

/-- Note this lemma can only be written about non-dependent tuples as `insertNth (last n) = snoc` is
not a definitional equality. -/
@[simp] lemma insertNthEquiv_last (n : ℕ) (α : Type*) :
    insertNthEquiv (fun _ ↦ α) (last n) = snocEquiv (fun _ ↦ α) := by ext; simp

/-- A `HEq` version of `Fin.removeNth_removeNth_eq_swap`. -/
theorem removeNth_removeNth_heq_swap {α : Fin (n + 2) → Sort*} (m : ∀ i, α i)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) ≍
      (i.predAbove j).removeNth ((j.succAbove i).removeNth m) := by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

/-- Given an `(n + 2)`-tuple `m` and two indexes `i : Fin (n + 1)` and `j : Fin (n + 2)`,
one can remove `j`th element from `m`, then remove `i`th element from the result,
or one can remove `(j.succAbove i)`th element from `m`,
then remove `(i.predAbove j)`th element from the result.

These two operations correspond to removing the same two elements in a different order,
so they result in the same `n`-tuple. -/
theorem removeNth_removeNth_eq_swap {α : Sort*} (m : Fin (n + 2) → α)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) = (i.predAbove j).removeNth ((j.succAbove i).removeNth m) :=
  heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

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

/-- If `find p = some i`, then `p i` holds -/
theorem find_spec :
    ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {i : Fin n} (_ : i ∈ Fin.find p), p i
  | 0, _, _, _, hi => Option.noConfusion hi
  | n + 1, p, I, i, hi => by
    rw [find] at hi
    rcases h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with - | j
    · rw [h] at hi
      dsimp at hi
      split_ifs at hi with hl
      · simp only [Option.mem_def, Option.some.injEq] at hi
        exact hi ▸ hl
      · exact (Option.not_mem_none _ hi).elim
    · rw [h] at hi
      dsimp at hi
      rw [← Option.some_inj.1 hi]
      exact @find_spec n (fun i ↦ p (i.castLT (Nat.lt_succ_of_lt i.2))) _ _ h

/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem isSome_find_iff :
    ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p], (find p).isSome ↔ ∃ i, p i
  | 0, _, _ => iff_of_false (fun h ↦ Bool.noConfusion h) fun ⟨i, _⟩ ↦ Fin.elim0 i
  | n + 1, p, _ =>
    ⟨fun h ↦ by
      rw [Option.isSome_iff_exists] at h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, find_spec _ hi⟩, fun ⟨⟨i, hin⟩, hi⟩ ↦ by
      dsimp [find]
      rcases h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with - | j
      · split_ifs with hl
        · exact Option.isSome_some
        · have := (@isSome_find_iff n (fun x ↦ p (x.castLT (Nat.lt_succ_of_lt x.2))) _).2
              ⟨⟨i, lt_of_le_of_ne (Nat.le_of_lt_succ hin) fun h ↦ by cases h; exact hl hi⟩, hi⟩
          rw [h] at this
          exact this
      · simp⟩

/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : Fin n → Prop} [DecidablePred p] :
    find p = none ↔ ∀ i, ¬p i := by rw [← not_exists, ← isSome_find_iff]; cases find p <;> simp

/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min :
    ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (_ : i ∈ Fin.find p) {j : Fin n}
      (_ : j < i), ¬p j
  | 0, _, _, _, hi, _, _, _ => Option.noConfusion hi
  | n + 1, p, _, i, hi, ⟨j, hjn⟩, hj, hpj => by
    rw [find] at hi
    rcases h : find fun i : Fin n ↦ p (i.castLT (Nat.lt_succ_of_lt i.2)) with - | k
    · simp only [h] at hi
      split_ifs at hi with hl
      · cases hi
        rw [find_eq_none_iff] at h
        exact h ⟨j, hj⟩ hpj
      · exact Option.not_mem_none _ hi
    · rw [h] at hi
      dsimp at hi
      obtain rfl := Option.some_inj.1 hi
      exact find_min h (show (⟨j, lt_trans hj k.2⟩ : Fin n) < k from hj) hpj

theorem find_min' {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (h : i ∈ Fin.find p) {j : Fin n}
    (hj : p j) : i ≤ j := Fin.not_lt.1 fun hij ↦ find_min h hij hj

theorem nat_find_mem_find {p : Fin n → Prop} [DecidablePred p]
    (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
    (⟨Nat.find h, (Nat.find_spec h).fst⟩ : Fin n) ∈ find p := by
  let ⟨i, hin, hi⟩ := h
  rcases hf : find p with - | f
  · rw [find_eq_none_iff] at hf
    exact (hf ⟨i, hin⟩ hi).elim
  · refine Option.some_inj.2 (Fin.le_antisymm ?_ ?_)
    · exact find_min' hf (Nat.find_spec h).snd
    · exact Nat.find_min' _ ⟨f.2, by convert find_spec p hf⟩

theorem mem_find_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    i ∈ Fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
  ⟨fun hi ↦ ⟨find_spec _ hi, fun _ ↦ find_min' hi⟩, by
    rintro ⟨hpi, hj⟩
    cases hfp : Fin.find p
    · rw [find_eq_none_iff] at hfp
      exact (hfp _ hpi).elim
    · exact Option.some_inj.2 (Fin.le_antisymm (find_min' hfp hpi) (hj _ (find_spec _ hfp)))⟩

theorem find_eq_some_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    Fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
  mem_find_iff

theorem mem_find_of_unique {p : Fin n → Prop} [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    {i : Fin n} (hi : p i) : i ∈ Fin.find p :=
  mem_find_iff.2 ⟨hi, fun j hj ↦ Fin.le_of_eq <| h i j hi hj⟩

end Find

section ContractNth

variable {α : Sort*}

/-- Sends `(g₀, ..., gₙ)` to `(g₀, ..., op gⱼ gⱼ₊₁, ..., gₙ)`. -/
def contractNth (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n) : α :=
  if (k : ℕ) < j then g (Fin.castSucc k)
  else if (k : ℕ) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ

theorem contractNth_apply_of_lt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) < j) : contractNth j op g k = g (Fin.castSucc k) :=
  if_pos h

theorem contractNth_apply_of_eq (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) = j) : contractNth j op g k = op (g (Fin.castSucc k)) (g k.succ) := by
  have : ¬(k : ℕ) < j := not_lt.2 (le_of_eq h.symm)
  rw [contractNth, if_neg this, if_pos h]

theorem contractNth_apply_of_gt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (j : ℕ) < k) : contractNth j op g k = g k.succ := by
  rw [contractNth, if_neg (not_lt_of_gt h), if_neg (Ne.symm <| ne_of_lt h)]

theorem contractNth_apply_of_ne (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (hjk : (j : ℕ) ≠ k) : contractNth j op g k = g (j.succAbove k) := by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [j.succAbove_of_castSucc_lt, contractNth_apply_of_lt]
    · rwa [Fin.lt_iff_val_lt_val]
  · exact False.elim (hjk h.symm)
  · rwa [j.succAbove_of_le_castSucc, contractNth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)

lemma comp_contractNth {β : Sort*} (opα : α → α → α) (opβ : β → β → β) {f : α → β}
    (hf : ∀ x y, f (opα x y) = opβ (f x) (f y)) (j : Fin (n + 1)) (g : Fin (n + 1) → α) :
    f ∘ contractNth j opα g = contractNth j opβ (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, contractNth_apply_of_eq, h, hf]
  · simp only [Function.comp_apply, contractNth_apply_of_gt, h]

end ContractNth

/-- To show two sigma pairs of tuples agree, it to show the second elements are related via
`Fin.cast`. -/
theorem sigma_eq_of_eq_comp_cast {α : Type*} :
    ∀ {a b : Σ ii, Fin ii → α} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.cast h → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    subst hi
    simpa using h

/-- `Fin.sigma_eq_of_eq_comp_cast` as an `iff`. -/
theorem sigma_eq_iff_eq_comp_cast {α : Type*} {a b : Σ ii, Fin ii → α} :
    a = b ↔ ∃ h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast h :=
  ⟨fun h ↦ h ▸ ⟨rfl, funext <| Fin.rec fun _ _ ↦ rfl⟩, fun ⟨_, h'⟩ ↦
    sigma_eq_of_eq_comp_cast _ h'⟩

end Fin

/-- `Π i : Fin 2, α i` is equivalent to `α 0 × α 1`. See also `finTwoArrowEquiv` for a
non-dependent version and `prodEquivPiFinTwo` for a version with inputs `α β : Type u`. -/
@[simps -fullyApplied]
def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1 where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
