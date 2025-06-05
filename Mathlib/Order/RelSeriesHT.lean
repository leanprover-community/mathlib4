/-
Copyright (c) 2025 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Destutter
import Mathlib.Data.Rel

/-!
# Series of a relation

If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type*} (r : α → α → Sort*)

/-- `a -[r]→* b` is a type of nonempty lists of elements such that adjacent elements are
  related by `r`, and such that the list starts/ends with `a`/`b` respectively. -/
inductive RelSeriesHT {α : Type*} (r :α → α → Sort*):
  (a : α) → (b : α) → Sort (max (u_3 + 1) u_4) where
| singleton (a : α) : RelSeriesHT r a a
| cons (a : α) {b c: α} (l : RelSeriesHT r b c) (hab : r a b) : RelSeriesHT r a c

variable {r}
namespace RelSeriesHT
/-- notation for `RelSeriesHT` -/
scoped notation3 l " -[" rel "]→* " r:(arg-1) => RelSeriesHT rel l r


/-- the first element of an `r`-series -/
def head {a _b : α} (_l :a -[r]→* _b) : α := a
-- (a,b)[r]

@[simp]
lemma head_singleton {a : α} : head (.singleton (r := r) a) = a := rfl

@[simp]
lemma head_cons {a b c : α} (l : b -[r]→* c) (hab : r a b) :
  head (.cons a l hab) = a := rfl

/-- End of a series, i.e. for `a₀ -r→ a₁ -r→ ... -r→ aₙ`, its last element is `aₙ`.
  Since a relation series is assumed to be non-empty, this is well defined. -/
def getLast {a b : α} (_l : a -[r]→* b) : α := b

@[simp]
lemma getLast_singleton {a : α} : getLast (.singleton (r := r) a) = a := rfl

@[simp]
lemma getLast_cons {a b c : α} (l : b -[r]→* c) (hab : r a b) :
  getLast (.cons a l hab) = getLast l := rfl

/-- the coercion of an `r`-series given by listing the elements -/
def toList {a b : α} (l : a -[r]→* b) : List α :=
  match l with
  | .singleton a => [a]
  | .cons a l' h => a::toList l'

@[simp]
lemma toList_singleton {a : α} : toList (.singleton (r := r) a) = [a] := rfl

@[simp]
lemma toList_cons (a : α) {b c : α} (l : b -[r]→* c) (hab : r a b) :
    toList (.cons a l hab) = a::toList l := rfl

@[simp]
lemma toList_ne_nil {a b : α} (l : a -[r]→* b) : l.toList ≠ [] := by
  cases l <;> simp

@[simp]
lemma head_toList {a b : α} (l : a -[r]→* b) (hl : toList l ≠ [] := l.toList_ne_nil) :
    l.toList.head hl = a := by
  cases l <;> rfl

@[simp]
lemma head?_toList {a b : α} (l : a-[r]→* b) : l.toList.head? = .some a := by
  cases l <;> rfl

@[simp]
lemma getLast_toList {a b : α} (l : a -[r]→* b) (hl : toList l ≠ [] := l.toList_ne_nil) :
    l.toList.getLast hl = b := by
  induction l <;> simp_all

@[simp]
lemma getLast?_toList {a b : α} (l : a -[r]→* b) :
    l.toList.getLast? = .some b := by
  induction l with
  | singleton a => rfl
  | cons a l hab ih => simp_all [List.getLast?_cons]

lemma chain'_toList {r : Rel α α} {a b : α} (l : a -[r]→* b) : l.toList.Chain' r := by
  induction l with
  | singleton a => simp
  | cons a l hab ih => simp_all [List.chain'_cons', List.head?_eq_head l.toList_ne_nil]

-- @[ext] doesn't work here
lemma ext {r : Rel α α} {a a' b b' : α} (l : a -[r]→* b) (l' : a' -[r]→* b') :
  (l.toList = l'.toList) → (a = a' ∧ b = b' ∧ HEq l l') := by
  induction l generalizing l' a' with
  | singleton a => cases l' with
    | singleton _ => simp only [toList_singleton, List.cons.injEq, and_true] ; rintro rfl; simp
    | cons _ _ _ => simp
  | cons _ _ _ hl =>
    cases l' with
    | singleton _ => simp
    | cons _ l' _ =>
      simp only [toList_cons, List.cons.injEq, and_imp]
      rintro rfl heq
      rename_i l _ _ _
      specialize hl _ heq
      obtain ⟨rfl,rfl,hl⟩ := hl
      simp only [heq_eq_eq] at hl
      simp only [heq_eq_eq, cons.injEq, true_and]
      tauto

instance [IsEmpty α] {a b : α} : IsEmpty (a -[r]→* b) where
  false _ := IsEmpty.false a

-- doesn't work
-- instance [Inhabited α] {a b : α} : Inhabited (a -[r]→* b) where
--   default := singleton default

/-- The length of an `r`-series is defined by the number of *steps* in the series.
  This means the shortest series has *length* 0, but *one* element. -/
def length {a b : α} (l : a -[r]→* b) : ℕ := match l with
  | .singleton a => 0
  | .cons a b hab => length b + 1

@[simp]
lemma length_singleton (a : α) : (singleton (r := r) a).length = 0 := rfl

@[simp]
lemma length_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) :
  (l.cons a hab).length = l.length + 1 := rfl

lemma length_nonneg {a b : α} (x : a -[r]→* b) : 0 ≤ x.length := by
  cases x <;> simp_all

lemma length_pos_of_ne {a b : α} (hne : a ≠ b) (x : a -[r]→* b) :
  0 < x.length := by
  cases x <;> simp_all

@[simp]
lemma length_toList {a b : α} (l : a -[r]→* b) : l.toList.length = l.length + 1 := by
  induction l <;> simp_all

/-- the coercion of an `r`-series to a function returning the value of the series at an index -/
def toFun {a b : α} (p : a -[r]→* b) : Fin (p.length + 1) → α := match p with
  | .singleton c => fun _ => c
  | .cons a l _ => fun
    | ⟨0,_⟩ => a
    | ⟨n+1,h⟩ => toFun l ⟨n,by simp_all⟩

instance {a b : α}: CoeFun (a -[r]→* b) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeriesHT.toFun}

@[simp]
lemma toFun_zero {a b : α} (p : a -[r]→* b) : p 0 = a := by
  cases p <;> rfl

@[simp]
lemma toFun_singleton (a : α) (x : Fin ((singleton (r := r) a).length + 1)) :
  (singleton a).toFun x = a := rfl

-- not quite sure how to make this simp
lemma toFun_cons_succ (a : α) {b b': α} (p : b -[r]→* b') (hab : r a b)
    (n : Fin ((cons a p hab).length)) : (cons a p hab) (n.succ) = p (n.castLT n.prop) := by
  simp only [length_cons]
  rfl

lemma toFun_length {a b : α} (p : a -[r]→* b) : p p.length = b := by
  induction p with
  | singleton a => rfl
  | cons a l hab ih => simp_all [Fin.last,toFun]

section ofLE

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
def ofLE {a b : α} (x : a -[r]→* b) {s : α → α → Sort*} (f : ∀ {a b}, r a b → s a b) : a -[s]→* b :=
  match x with
  | .singleton a => .singleton a
  | .cons a l hab => .cons a (l.ofLE f) (f hab)

@[simp]
lemma ofLE_singleton (a : α) {s : α → α → Sort*} (f : ∀ {a b}, r a b → s a b):
    ofLE (singleton a) f = singleton (r := s) a := rfl

@[simp]
lemma ofLE_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) {s : α → α → Sort*}
    (f : ∀ {a b}, r a b → s a b):
  ofLE (cons a l hab) f = cons a (ofLE l f) (f hab) := rfl

@[simp]
lemma head_ofLE {a b : α} (x : a -[r]→* b) {s : α → α → Sort*} (f : ∀ {a b}, r a b → s a b) :
  head (ofLE x f) = a := rfl

@[simp]
lemma getLast_ofLE {a b : α} (x : a -[r]→* b) {s : α → α → Sort*} (f : ∀ {a b}, r a b → s a b) :
  getLast (ofLE x f) = b := rfl


@[simp]
lemma toList_ofLe {a b : α} (x : a -[r]→* b) {s : α → α → Sort*} (f : ∀ {a b}, r a b → s a b) :
    toList (ofLE x f) = toList x := by
  induction x <;> simp_all

end ofLE

section fromListChain'
variable {r : Rel α α}
/-- any nonempty `List` that satisfies `List.Chain' r` induces an `r`-series
  given by its elements -/
def fromListChain' (x : List α) (x_ne_nil : x ≠ []) (hx : x.Chain' r) :
    RelSeriesHT r (x.head x_ne_nil) (x.getLast x_ne_nil) := match x with
  | [] => (x_ne_nil rfl).elim
  | [a] => .singleton a
  | a::b::xs => .cons a (fromListChain' (b::xs) (List.cons_ne_nil b xs)
    (List.chain'_cons.mp hx).right)
    (List.chain'_cons.mp hx |>.left)

@[simp]
lemma fromListChain'_singleton (a : α) (ne_nil : [a] ≠ [] := List.cons_ne_nil a [])
    (hchain : [a].Chain' r := List.chain'_singleton a) :
    fromListChain' [a] ne_nil hchain = singleton a := rfl

@[simp]
lemma fromListChain'_cons_cons (a b : α) (l : List α)
    (cons_l_ne_nil : (b::l) ≠ [] := List.cons_ne_nil b l) (cons_l_chain' : (b::l).Chain' r)
    (hab : r a b) (hchain : (a::b::l).Chain' r := List.Chain'.cons hab cons_l_chain')
    (h_ne_nil : (a::b::l) ≠ [] := List.cons_ne_nil a (b :: l)) :
    fromListChain' (a::b::l) h_ne_nil hchain =
      cons a (fromListChain' (b::l) cons_l_ne_nil cons_l_chain') hab := rfl

@[simp]
lemma head_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r):
  head (fromListChain' l l_ne_nil hl_chain') = l.head l_ne_nil := rfl

@[simp]
lemma getLast_fromListChain' (l : List α) (l_ne_nil : l ≠ []) (hl_chain' : l.Chain' r):
  getLast (fromListChain' l l_ne_nil hl_chain') = l.getLast l_ne_nil := rfl

@[simp]
lemma length_fromListChain' (l : List α) (ne_nil : l ≠ []) (hchain' : l.Chain' r) :
  (fromListChain' l ne_nil hchain').length + 1 = l.length := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons head' tail =>
      rw [fromListChain'_cons_cons head head' tail (List.cons_ne_nil head' tail)
        (List.chain'_cons.mp hchain').right (List.chain'_cons.mp hchain').left, length_cons head,
        ih (List.cons_ne_nil _ tail)]
      rfl

@[simp]
lemma toList_fromListChain' (l : List α) (ne_nil : l ≠ []) (hchain' : l.Chain' r) :
    toList (fromListChain' l ne_nil hchain') = l := by
  fun_induction fromListChain' l ne_nil hchain' <;> simp_all

end fromListChain'

variable {r : Rel α α} in
lemma toList_injective {a b : α} : Function.Injective (@RelSeriesHT.toList α r a b) :=
  fun _ _ h ↦ eq_of_heq (ext _ _ h).right.right

section ofRel

/-- `ofRel` gives the length 1 `r`-series induced by the relation `r a b`. -/
def ofRel {a b : α} (hr : r a b) : a -[r]→* b := .cons a (.singleton b) hr

@[simp]
lemma length_ofRel {a b : α} (hr : r a b) : length (ofRel hr) = 1 := rfl

@[simp]
lemma head_ofRel {a b : α} (hr : r a b) : head (ofRel hr) = a := rfl

@[simp]
lemma getLast_ofRel {a b : α} (hr : r a b) : getLast (ofRel hr) = b := rfl

@[simp]
lemma toList_ofRel {a b : α} (hr : r a b) : toList (ofRel hr) = [a,b] := rfl

lemma nonempty_of_rel {a b : α} (hr : r a b) : Nonempty (a -[r]→* b) :=
  ⟨ofRel hr⟩


end ofRel

section snoc

/-- `snoc` is a variation on the `cons` operation, which puts
  the extra element on the end of the series (as opposed on the head end). -/
@[match_pattern]
def snoc {a b : α} (x : a -[r]→* b) (b' : α) (hr : r b b') : a -[r]→* b' :=
  match x with
  | .singleton a => .cons a (.singleton b') hr
  | .cons a b hr' => .cons a (snoc b b' hr) hr'

@[simp]
lemma snoc_singleton (a b : α) (hr : r a b) :
  snoc (.singleton a) b hr = .cons a (.singleton b) hr := rfl

@[simp]
lemma snoc_cons (a : α) {b b' : α} (l : b -[r]→* b') (hab : r a b) (c : α) (hr : r b' c) :
  snoc (.cons a l hab) c hr = .cons a (snoc l c hr) hab := rfl

@[simp]
lemma head_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  head (snoc x c hr) = a := rfl

@[simp]
lemma getLast_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  getLast (snoc x c hr) = c := rfl

@[simp]
lemma toList_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    toList (snoc x c hr) = (toList x) ++ [c] := by
  induction x <;> simp_all

@[simp]
lemma length_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r  b c) :
    length (snoc x c hr) = length x + 1 := by
  induction x <;> simp_all


lemma snoc_injective {a b : α} (c : α) (hr : r b c) :
    Function.Injective (snoc (a := a) · c hr) := by
  intro x x' heq
  induction x with
  | singleton a => cases x' with
    | singleton a => rfl
    | cons a l hab =>
      simp only [snoc_singleton, snoc_cons, cons.injEq] at heq
      cases heq.left
      cases l <;> simp_all
  | cons a l hab ih =>
    cases x' with
    | singleton a =>
      simp_all only [forall_true_left, snoc_cons, snoc_singleton, cons.injEq, heq_eq_eq, and_true]
      cases heq.left
      cases l <;> simp_all
    | cons a l hab =>
      simp_all only [forall_true_left, snoc_cons, cons.injEq, heq_eq_eq, and_true, true_and]
      cases heq.left
      exact heq_of_eq (ih _ (eq_of_heq heq.right.left))

end snoc

section copy

/--
Change the endpoints of an `r`-series using equalities. This is useful for relaxing
definitional equality constraints, as well as allowing us to state more complicated lemmas.
simp normal form is moving the copy *outwards* , to enable computation within the "copy" context.
-/
def copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
  a' -[r]→* b' := cast (ha ▸ hb ▸ rfl) x

@[simp]
lemma copy_rfl_rfl {a b : α} (x : a -[r]→* b) :
  x.copy rfl rfl = x := rfl

@[simp]
lemma copy_singleton {a b : α} (h : a = b) :
    (singleton (r := r) a).copy h h = singleton (r := r) b := by
  aesop

lemma copy_cons {a a' : α} (ha : a = a') {b b' c c' : α} (hb : b = b')
    (hc : c = c') {x : b -[r]→* c} (hab : r a b) :
    (cons a x hab).copy ha hc = cons a' (x.copy hb hc) (ha ▸ hb ▸ hab) := by
  aesop

@[simp]
lemma cons_copy (c : α) {a b a' b' : α} (x : a -[r]→* b) (hr : r c a')
    (ha : a = a') (hb : b = b') :
    cons c (copy x ha hb) hr = copy (.cons c x (ha ▸ hr)) rfl hb := by
  cases ha; cases hb; rfl

@[simp]
lemma snoc_copy {a b a' b'} (x : a -[r]→* b) (c : α) (hr : r b' c)
    (ha : a = a') (hb : b = b') :
    snoc (copy x ha hb) c hr = copy (.snoc x c (hb ▸ hr)) ha rfl := by
  cases ha; cases hb; rfl

@[simp]
lemma toList_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
  toList (copy x ha hb) = toList x := by
  cases ha; cases hb; rfl

@[simp]
lemma length_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b') :
    length (copy x ha hb) = length x := by
  cases ha; cases hb; rfl

end copy

section append

/--
If `a₀ -r→ a₁ -r→ ... -r→ aₙ` and `b₀ -r→ b₁ -r→ ... -r→ bₘ` are two strict series
such that `aₙ = b₀`, then there is a chain of length `n + m` given by
`a₀ -r→ a₁ -r→ ... -r→ aₙ = b₀ -r→ b₁ -r→ ... -r→ bₘ`.
-/
@[match_pattern]
def append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) : a -[r]→* c :=
  match x with
  | .singleton a => y
  | .cons a l hl => .cons a (append l y) hl

instance {r : α → α → Type*} {a b b' : α}: HAppend (a -[r]→* b) (b -[r]→* b') (a -[r]→* b') where
  hAppend l r := append l r

instance {r : Rel α α} {a b b' : α}: HAppend (a -[r]→* b) (b -[r]→* b') (a -[r]→* b') where
  hAppend l r := append l r

section prop

variable {r : Rel α α}
@[simp]
lemma singleton_append {a b : α} (x : a -[r]→* b) :
  (singleton (r := r) a) ++ x = x := rfl

@[simp]
lemma cons_append (a : α) {b b' c: α} (x : b -[r]→* b') (hr : r a b) (y : b' -[r]→* c) :
  (cons a x hr) ++ y = .cons a (x ++ y) hr := rfl

@[simp]
lemma append_singleton {a b : α} (x : a -[r]→* b) :
  x ++ (singleton (r := r) b) = x := by
  induction x <;> simp_all

@[simp]
lemma append_snoc {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') (c : α)
    (hr : r b' c) :
    x ++ (snoc y c hr) = snoc (x ++ y) c hr := by
  induction x <;> simp_all

@[simp]
lemma snoc_append {a b : α} (x : a -[r]→* b) (b' : α) (hr : r b b') {c : α} (y : b' -[r]→* c):
    snoc x b' hr ++ y = x ++ cons b y hr := by
      induction x <;> simp_all

@[simp]
lemma length_append {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    length (x ++ y) = length x + length y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [cons_append, length_cons]
    exact Nat.add_right_comm l.length y.length 1

@[simp]
lemma append_assoc {a b c d : α} (x : a -[r]→* b) (y : b -[r]→* c)
    (z : c -[r]→* d):
  (x ++ y) ++ z = x ++ (y ++ z) := by
  induction x <;> simp_all

@[simp]
lemma toList_append {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = toList x ++ (toList y).tail := by
  induction x with
  | singleton a =>
    simp
    cases h:y.toList with
    | nil => exact ((toList_ne_nil y) h).elim
    | cons head tail =>
      simp only [List.tail_cons, List.cons.injEq, and_true]
      change (head :: tail).head (List.cons_ne_nil head tail) = y.head
      simp_rw [← h,head_toList]
      rfl
  | cons a l hab ih => simp_all

lemma toList_append' {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = (toList x).dropLast ++ (toList y) := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [toList_append, cons_append, toList_cons]
    cases l <;> simp

lemma exists_eq_append_of_toList_eq_append {a b : α} (l : a -[r]→* b) (x y : List α) (hx : x ≠ []):
  l.toList = x ++ y → ∃ (c : α), ∃ m : a -[r]→* c, ∃ (n : c -[r]→* b),
    l = m ++ n ∧ m.toList = x ∧ n.toList.tail = y := by
  induction l generalizing x hx y with
  | singleton a =>
    cases x <;> cases y <;> simp_all only [ne_eq, not_true_eq_false, toList_singleton,
      List.append_nil, List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff]
    · rintro ⟨rfl, rfl⟩
      use a, singleton a, singleton a, rfl,rfl
      rfl
    · simp only [reduceCtorEq, and_false, IsEmpty.forall_iff]
  | cons a l hab ih =>
    simp_all only [ne_eq, toList_cons]
    obtain ⟨head,tail,rfl⟩ := List.ne_nil_iff_exists_cons.mp hx
    clear hx
    simp only [List.cons_append, List.cons.injEq, and_imp]
    rintro rfl hl
    cases tail with
    | nil =>
      simp only [List.nil_append] at hl
      use a, singleton a, (cons a l hab)
      simp_all
    | cons head tail =>
      simp_all only [List.cons_append]
      specialize ih (head :: tail) y (List.cons_ne_nil head tail) rfl
      obtain ⟨c',m',n',rfl,hm',rfl⟩ := ih
      use c', (cons a m' hab),n'
      simp_all

lemma exists_eq_append_of_toList_eq_append' {a b : α} (l : a -[r]→* b) (x y : List α) (hy : y ≠ []):
  l.toList = x ++ y → ∃ (c : α), ∃ m : a -[r]→* c, ∃ (n : c -[r]→* b),
    l = m ++ n ∧ m.toList.dropLast = x ∧ n.toList = y := by
  induction l generalizing x hy y with
  | singleton a =>
    simp_all only [ne_eq, toList_singleton]
    cases y <;> cases x <;> simp [not_true_eq_false,List.nil_append, List.cons_append,
      List.cons.injEq, List.nil_eq, and_imp, List.append_eq_nil_iff, and_false, IsEmpty.forall_iff]
        <;> try contradiction
    rintro rfl rfl
    use a, (singleton a), singleton a,rfl,rfl
    rfl
  | cons a l hab ih =>
    simp only [toList_cons]
    cases x with
    | nil =>
      rintro rfl
      use a, singleton a, cons a l hab,rfl,rfl
      rfl
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq, and_imp]
      rintro rfl hl
      obtain ⟨z,ll,lr,rfl,rfl,rfl⟩ := ih tail y hy hl
      use z, cons a ll hab, lr, rfl
      simp only [toList_cons, and_true]
      exact List.dropLast_cons_of_ne_nil (toList_ne_nil ll)

lemma append_right_injective {a b c : α} (l : a -[r]→* b):
    Function.Injective (α := b -[r]→* c) (l ++ ·) := by
  intro x y h
  induction l with
  | singleton a =>
    exact h
  | cons a l hab ih =>
    simp_all only [cons_append, cons.injEq, heq_eq_eq, and_true, true_and]
    exact ih h

lemma append_left_injective {a b c : α} (l : b -[r]→* c) :
    Function.Injective (α := a -[r]→* b) (· ++ l) := by
  intro x y hxy
  induction l with
  | singleton a => simpa using hxy
  | cons a l hab ih =>
    simp_all only [← snoc_append]
    exact snoc_injective _ _ (ih hxy)

@[simp]
lemma ofRel_append (a : α) {b c: α} (x : b -[r]→* c) (hr : r a b) :
  ofRel hr ++ x = cons a x hr := rfl

@[simp]
lemma append_ofRel {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    x ++ ofRel hr = snoc x c hr := by
  induction x <;> simp_all ; rfl

end prop
section type

variable {r : α → α → Type*}
@[simp]
lemma singleton_appendₜ {a b : α} (x : a -[r]→* b) :
  (singleton (r := r) a) ++ x = x := rfl

@[simp]
lemma cons_appendₜ (a : α) {b b' c: α} (x : b -[r]→* b') (hr : r a b) (y : b' -[r]→* c) :
  (cons a x hr) ++ y = .cons a (x ++ y) hr := rfl

@[simp]
lemma append_singletonₜ {a b : α} (x : a -[r]→* b) :
  x ++ (singleton (r := r) b) = x := by
  induction x <;> simp_all

@[simp]
lemma append_snocₜ {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') (c : α)
    (hr : r b' c) :
    x ++ (snoc y c hr) = snoc (x ++ y) c hr := by
  induction x <;> simp_all

@[simp]
lemma snoc_appendₜ {a b : α} (x : a -[r]→* b) (b' : α) (hr : r b b') {c : α} (y : b' -[r]→* c):
    snoc x b' hr ++ y = x ++ cons b y hr := by
      induction x <;> simp_all

@[simp]
lemma length_appendₜ {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    length (x ++ y) = length x + length y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [cons_appendₜ, length_cons]
    exact Nat.add_right_comm l.length y.length 1

@[simp]
lemma append_assocₜ {a b c d : α} (x : a -[r]→* b) (y : b -[r]→* c)
    (z : c -[r]→* d):
  (x ++ y) ++ z = x ++ (y ++ z) := by
  induction x <;> simp_all

@[simp]
lemma toList_appendₜ {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = toList x ++ (toList y).tail := by
  induction x with
  | singleton a =>
    simp
    cases h:y.toList with
    | nil => exact ((toList_ne_nil y) h).elim
    | cons head tail =>
      simp only [List.tail_cons, List.cons.injEq, and_true]
      change (head :: tail).head (List.cons_ne_nil head tail) = y.head
      simp_rw [← h,head_toList]
      rfl
  | cons a l hab ih => simp_all

lemma toList_appendₜ' {a b b' : α} (x : a -[r]→* b) (y : b -[r]→* b') :
    toList (x ++ y) = (toList x).dropLast ++ (toList y) := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [toList_appendₜ, cons_appendₜ, toList_cons]
    cases l <;> simp

lemma exists_eq_append_of_toList_eq_appendₜ {a b : α} (l : a -[r]→* b) (x y : List α) (hx : x ≠ []):
  l.toList = x ++ y →
    ∃ (c : α), ∃ m : a -[r]→* c, ∃ (n : c -[r]→* b),
      l = m ++ n ∧ m.toList = x ∧ n.toList.tail = y := by
  induction l generalizing x hx y with
  | singleton a =>
    cases x <;> cases y <;> simp_all only [ne_eq, not_true_eq_false, toList_singleton,
      List.append_nil, List.cons_append, List.cons.injEq, List.nil_eq, List.append_eq_nil_iff]
    · rintro ⟨rfl, rfl⟩
      use a, singleton a, singleton a, rfl,rfl
      rfl
    · simp only [reduceCtorEq, and_false, IsEmpty.forall_iff]
  | cons a l hab ih =>
    simp_all only [ne_eq, toList_cons]
    obtain ⟨head,tail,rfl⟩ := List.ne_nil_iff_exists_cons.mp hx
    clear hx
    simp only [List.cons_append, List.cons.injEq, and_imp]
    rintro rfl hl
    cases tail with
    | nil =>
      simp only [List.nil_append] at hl
      use a, singleton a, (cons a l hab)
      simp_all
    | cons head tail =>
      simp_all only [List.cons_append]
      specialize ih (head :: tail) y (List.cons_ne_nil head tail) rfl
      obtain ⟨c',m',n',rfl,hm',rfl⟩ := ih
      use c', (cons a m' hab),n'
      simp_all

lemma exists_eq_append_of_toList_eq_appendₜ' {a b : α} (l : a -[r]→* b) (x y : List α) (hy : y ≠ [])
  :
  l.toList = x ++ y → ∃ (c : α), ∃ m : a -[r]→* c, ∃ (n : c -[r]→* b),
    l = m ++ n ∧ m.toList.dropLast = x ∧ n.toList = y := by
  induction l generalizing x hy y with
  | singleton a =>
    simp_all only [ne_eq, toList_singleton]
    cases y <;> cases x <;> simp [not_true_eq_false,List.nil_append, List.cons_append,
      List.cons.injEq, List.nil_eq, and_imp, List.append_eq_nil_iff, and_false, IsEmpty.forall_iff]
        <;> try contradiction
    rintro rfl rfl
    use a, (singleton a), singleton a,rfl,rfl
    rfl
  | cons a l hab ih =>
    simp only [toList_cons]
    cases x with
    | nil =>
      rintro rfl
      use a, singleton a, cons a l hab,rfl,rfl
      rfl
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq, and_imp]
      rintro rfl hl
      obtain ⟨z,ll,lr,rfl,rfl,rfl⟩ := ih tail y hy hl
      use z, cons a ll hab, lr, rfl
      simp only [toList_cons, and_true]
      exact List.dropLast_cons_of_ne_nil (toList_ne_nil ll)

lemma append_right_injectiveₜ {a b c : α} (l : a -[r]→* b):
    Function.Injective (α := b -[r]→* c) (l ++ ·) := by
  intro x y h
  induction l with
  | singleton a =>
    exact h
  | cons a l hab ih =>
    simp_all only [cons_appendₜ, cons.injEq, heq_eq_eq, and_true, true_and]
    exact ih h

lemma append_left_injectiveₜ {a b c : α} (l : b -[r]→* c) :
    Function.Injective (α := a -[r]→* b) (· ++ l) := by
  intro x y hxy
  induction l with
  | singleton a => simpa using hxy
  | cons a l hab ih =>
    rename_i b _
    simp_all only [← snoc_appendₜ]
    exact snoc_injective _ hab (ih hxy)

@[simp]
lemma ofRel_appendₜ (a : α) {b c: α} (x : b -[r]→* c) (hr : r a b) :
  ofRel hr ++ x = cons a x hr := rfl

@[simp]
lemma append_ofRelₜ {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    x ++ ofRel hr = snoc x c hr := by
  induction x <;> simp_all ; rfl

end type

end append

section reverse

/--
A relation series `a₀ -r→ a₁ -r→ ... -r→ aₙ` of `r` gives a relation series of the reverse of `r`
by reversing the series `aₙ ←r- aₙ₋₁ ←r- ... ←r- a₁ ←r- a₀`.
-/
def reverse {a b : α} (x : a -[r]→* b) : b -[(Function.swap r)]→* a := match x with
  | .singleton a => .singleton a
  | .cons a b hr => .snoc (reverse b) a hr

variable (r) in
@[simp]
lemma reverse_singleton (a : α) : reverse (.singleton (r := r) a) = .singleton a := rfl

@[simp]
lemma reverse_cons (a : α) {b b' : α} (x : b -[r]→* b') (hr : r a b) :
  reverse (.cons a x hr) = snoc (reverse x) a hr := rfl

@[simp]
lemma reverse_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
  reverse (snoc x c hr) = .cons c (reverse x) hr := by
  induction x <;> simp_all


@[simp]
lemma toList_reverse {a b : α} (x : a -[r]→* b) :
    toList (reverse x) = .reverse (toList x) := by
  induction x <;> simp_all

@[simp]
lemma reverse_copy {a b a' b' : α} (x : a -[r]→* b) (ha : a = a') (hb : b = b'):
    reverse (copy x ha hb) = copy (reverse x) hb ha := by
  cases ha; cases hb; rfl

lemma fromListChain'_reverse {r : Rel α α} (l : List α) (l_ne_nil : l ≠ [])
  (hl_chain' : l.Chain' r) :
  fromListChain' (r := fun x y => r y x) (l.reverse) (List.reverse_ne_nil_iff.mpr l_ne_nil)
    (List.chain'_reverse.mpr hl_chain') =
      copy (reverse (fromListChain' l l_ne_nil hl_chain'))
      (List.getLast_eq_head_reverse l_ne_nil) (List.head_eq_getLast_reverse l_ne_nil) := by
  refine eq_of_heq (ext _ _ ?_).right.right
  simp

lemma reverse_fromListChain' {r : Rel α α} (l : List α) (l_ne_nil : l ≠ [])
    (hl_chain' : l.Chain' r) :
    (fromListChain' l l_ne_nil hl_chain').reverse
      = copy (fromListChain' (l.reverse) (List.reverse_ne_nil_iff.mpr l_ne_nil)
          (List.chain'_reverse.mpr hl_chain'))
        (List.head_reverse (List.reverse_ne_nil_iff.mpr l_ne_nil)) (List.getLast_reverse _) := by
  refine eq_of_heq (ext _ _ ?_).right.right
  simp_all

@[simp]
lemma reverse_reverse {a b : α} (x : a -[r]→* b) :
  x.reverse.reverse = x := by
  induction x <;> simp_all

@[simp]
lemma reverse_append {r : Rel α α} {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
  (x ++ y).reverse = y.reverse ++ x.reverse := by
  induction x <;> simp_all

@[simp]
lemma reverse_appendₜ {r : α → α → Type*} {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
  (x ++ y).reverse = y.reverse ++ x.reverse := by
  induction x <;> simp_all


@[simp]
lemma length_reverse {a b : α} (x : a -[r]→* b) :
  x.reverse.length = x.length := by
  induction x <;> simp_all

end reverse

section map
variable {r : Rel α α} {β : Type*} {s : Rel β β} (f : r →r s)
/--
For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
can be pushed out to a strict chain of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
def map (f : r →r s) {a b : α} (x : a -[r]→* b) :
    (f a) -[s]→* (f b) := match x with
  | .singleton a => .singleton (f a)
  | .cons a l hr => .cons (f a) (map f l) (f.map_rel hr)

@[simp]
lemma map_singleton (a : α) :
  map f (singleton (r := r) a) = singleton (f a) := rfl

@[simp]
lemma map_cons (a : α) {b b' : α} (x : b -[r]→* b') (hr : r a b) :
  map f (cons a x hr) = cons (f a) (map f x) (f.map_rel hr) := rfl

@[simp]
lemma map_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
    map f (snoc x c hr) = snoc (map f x) (f c) (f.map_rel hr) := by
  induction x <;> simp_all

@[simp]
lemma map_append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
    map f (x ++ y) = (map f x) ++ (map f y) := by
  induction x <;> simp_all

@[simp]
lemma toList_map {a b : α} (x : a -[r]→* b) :
    toList (map f x) = (toList x).map f := by
  induction x <;> simp_all

variable {γ : Type*} {t : Rel γ γ}

@[simp]
lemma map_map (g : s →r t) (f : r →r s) {a₁ b₁ : α} (x : a₁ -[r]→* b₁) :
    RelSeriesHT.map g (RelSeriesHT.map f x) = RelSeriesHT.map (g.comp f) x := by
  induction x with
  | singleton a => simp
  | cons a l hab ih => simp_all

@[simp]
lemma map_copy {a a' b b' : α} (ha : a = a') (hb : b = b') (x : a -[r]→* b) :
    (x.copy ha hb).map f = (x.map f).copy (congr(f $ha)) (congr(f $hb)) := by
  aesop

lemma map_eq_self {f : r →r r} (hf : ∀ a, f a = a) {a b : α} (x : a -[r]→* b) :
    (x.map f).copy (hf a) (hf b) = x := by
  induction x with
  | singleton a =>
    simp
  | cons a x hab ih =>
    nth_rw 2 [← ih]
    apply copy_cons

end map

section equiv

/--
A relation-isomorphism between two relations induces a bijection between the respective relseries .
-/
def equiv {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s) {a b : α}:
    a -[r]→* b ≃ (e a) -[s]→* (e b) where
  toFun :=
    map (a := a) (b := b) (r := r) (s := s) e.toRelEmbedding
  invFun x:=
    (map (a := e a) (b:= e b) (s := r) (r := s) e.symm.toRelEmbedding x).copy
      (by simp)
      (by simp)
  left_inv := by
    intro x
    simp only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, map_map]
    apply map_eq_self
  right_inv := by
    intro x
    simp only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, map_copy, map_map]
    apply map_eq_self
    simp

@[simp]
lemma equiv_singleton {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s) {a : α} :
  equiv e (singleton (r := r) a) = singleton (r := s) (e a) := rfl

@[simp]
lemma equiv_cons {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s) (a : α) {b c : α}
    (x : b -[r]→* c) (hr : r a b):
    equiv e (cons a x hr) = cons (e a) (equiv e x) (e.map_rel_iff.mpr hr) := rfl

@[simp]
lemma length_equiv {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s) {a b : α}
    (x : a -[r]→* b) : (equiv e x).length = x.length := by
  induction x with
  | singleton a => simp
  | cons a l hab ih => simp_all

-- this is kinda ugly, because there is no direct or implicit coersion of reliso to relhom.
lemma equiv_apply {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s) {a b : α} (x : a -[r]→* b):
  equiv e x = map e.toRelEmbedding.toRelHom x := rfl

lemma equiv_symm_apply {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s)
    {a b : α} (x : e a -[s]→* (e b)):
    (equiv e).symm x = (map (e.symm.toRelEmbedding) x).copy (by simp) (by simp) := rfl

end equiv

-- section copymap

-- variable {r : Rel α α} {β : Type*} {s : Rel β β}
-- /--
-- For two preorders `α, β`, if `f : α → β` is strictly monotonic, then a strict chain of `α`
-- can be pushed out to a strict chain of `β` by
-- `a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-- -/
-- def copymap (f : α → α) (hf : ∀ i, f i = i) {a b : α} (x : (f a) -[r]→* (f b)) :
--     (a) -[r]→* (b) := x.map ⟨_,_⟩

-- @[simp]
-- lemma map_singleton (a : α) :
--   map f (singleton (r := r) a) = singleton (f a) := rfl

-- @[simp]
-- lemma map_cons (a : α) {b b' : α} (x : b -[r]→* b') (hr : r a b) :
--   map f (cons a x hr) = cons (f a) (map f x) (f.map_rel hr) := rfl

-- @[simp]
-- lemma map_snoc {a b : α} (x : a -[r]→* b) (c : α) (hr : r b c) :
--     map f (snoc x c hr) = snoc (map f x) (f c) (f.map_rel hr) := by
--   induction x <;> simp_all

-- @[simp]
-- lemma map_append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) :
--     map f (x ++ y) = (map f x) ++ (map f y) := by
--   induction x <;> simp_all

-- @[simp]
-- lemma toList_map {a b : α} (x : a -[r]→* b) :
--     toList (map f x) = (toList x).map f := by
--   induction x <;> simp_all

-- variable {γ : Type*} {t : Rel γ γ}

-- @[simp]
-- lemma map_map (g : s →r t) (f : r →r s) {a₁ b₁ : α} (x : a₁ -[r]→* b₁) :
--     RelSeriesHT.map g (RelSeriesHT.map f x) = RelSeriesHT.map (g.comp f) x := by
--   induction x with
--   | singleton a => simp
--   | cons a l hab ih => simp_all


-- end copymap

section coe_subtype
/-
This bit of api is ugly to write, we have to repeat the subtype explicitly a lot.
It might be better suited to only the cases where the relation is supplied by typeclasses
like [Preorder], since we'd be abusing defeq anyway.
-/

variable {r : Rel α α} {p : α → Prop}
/-- elementwise subtype coersion -/
def coeSubtype {ap bp : {a : α // p a}} (x : ap -[fun ap bp : {a : α // p a} ↦ r ap bp]→* bp) :
    ap -[r]→* bp :=
  (x.map ⟨Subtype.val (p := p),fun h => h⟩)

@[simp]
lemma coeSubtype_singleton (ap : Subtype p):
  coeSubtype (singleton (r := fun x y : Subtype p ↦ r x y) ap) = singleton (r := r) ap := rfl

@[simp]
lemma coeSubtype_cons (ap : {a : α // p a}) {bp cp : {a : α // p a}}
    (x : bp -[fun y z : {a : α // p a} ↦ r y z]→* cp) (hab : r ap bp):
  coeSubtype (cons ap x hab) = cons (ap : α) (coeSubtype x) hab := rfl

@[simp]
lemma coeSubtype_snoc {ap bp : {a : α // p a}}
    (x : ap -[fun y z : {a : α // p a} ↦ r y z]→* bp) (cp : {a : α // p a})  (hbc : r bp cp):
    coeSubtype (snoc x cp hbc) = snoc (coeSubtype x) cp hbc := by
  induction x <;> simp_all

@[simp]
lemma length_coeSubtype_eq_length {p : α → Prop} {ap bp : {a : α // p a}}
    {x : ap -[fun ap bp : {a : α // p a} ↦ r ap bp]→* bp} :
    (coeSubtype x).length = x.length := by
  induction x <;> simp_all

end coe_subtype

section mem

instance membership {r : Rel α α} {a b : α} : Membership α (a -[r]→* b) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩

instance membershipₜ {r : α → α → Type*} {a b : α} : Membership α (a -[r]→* b) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩

section prop
variable {r : Rel α α} {a b : α} {s : a -[r]→* b} {x : α}
theorem mem_def : x ∈ s ↔ x ∈ Set.range s := Iff.rfl

@[simp] theorem mem_toList : x ∈ s.toList ↔ x ∈ s := by
  rw [mem_def]
  induction s with
  | singleton a =>
    simp only [toList_singleton, List.mem_cons, List.not_mem_nil, or_false, length_singleton,
      Nat.reduceAdd, Set.mem_range, toFun_singleton, eq_comm, exists_const]
  | cons a l hab ih =>
    simp_all only [Set.mem_range, toList_cons, List.mem_cons, length_cons]
    refine ⟨(·.elim (⟨0,·.symm⟩) (·.elim (⟨·.succ,·⟩))),
      (·.elim (·.cases (.inl ·.symm) (.inr ⟨·,·⟩)))⟩

@[simp]
lemma mem_singleton_iff {a x : α} : x ∈ singleton (r := r) a ↔ x = a := by
  simp [← mem_toList]

@[simp]
lemma mem_cons_iff (c : α) (hr : r c a) : x ∈ cons c s hr ↔ x = c ∨ x ∈ s := by
  simp [← mem_toList]

@[simp]
lemma mem_snoc_iff (c : α) (hr : r b c) : x ∈ snoc s c hr ↔ x ∈ s ∨ x = c := by
  simp [← mem_toList]

@[simp]
lemma mem_append_iff {c : α} {t : b -[r]→* c} : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t := by
  simp [← mem_toList]
  refine ⟨(·.elim .inl (.inr <| List.mem_of_mem_tail ·)),(·.elim .inl ?_)⟩
  cases t with
  | singleton a =>
    simp only [toList_singleton, List.mem_cons, List.not_mem_nil, or_false, mem_toList,
      List.tail_cons]
    rintro rfl
    exact ⟨s.length,toFun_length s⟩
  | cons a l hab =>
    simp only [toList_cons, List.mem_cons, mem_toList, List.tail_cons]
    exact (·.elim (fun h => .inl (h.symm ▸ ⟨s.length,toFun_length s⟩)) .inr)

@[simp]
lemma mem_reverse_iff : x ∈ s.reverse ↔ x ∈ s := by
  simp [← mem_toList]

@[simp]
lemma head_mem : a ∈ s := ⟨0,toFun_zero s⟩

@[simp]
lemma getLast_mem : b ∈ s := ⟨s.length,toFun_length s⟩

@[simp]
lemma mem_map {β : Type*} {t : Rel β β} (f : r →r t) {y : β} : y ∈ map f s ↔ ∃ x ∈ s, f x = y := by
  simp_all [← mem_toList]

lemma exists_eq_append_of_mem {a b : α} (l : a -[r]→* b) {c : α} (hc : c ∈ l) :
    ∃ (x : a-[r]→* c), ∃ (y : c -[r]→* b), l = x ++ y := by
  rw [← mem_toList] at hc
  induction l with
  | singleton a =>
    simp only [toList_singleton, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases hc
    use (singleton c), singleton c
    rfl
  | cons a l hab ih =>
    simp only [toList_cons, List.mem_cons] at hc
    obtain (rfl|hc) := hc
    · use (singleton c), cons c l hab
      rfl
    · obtain ⟨x,y,rfl⟩ := ih hc
      use (cons a x hab), y
      rfl
end prop
end mem
end RelSeriesHT

variable {r : Rel α α}
namespace RelSeriesHT
section LE

/--
given `x y : a -[r]→* b`, we say that `x` is less than `y` if `y` can be obtained from `x` by
substituting single steps or values in `x` for any `r`-series with the right start and end points.

For example, using (· < ·) as a relation on naturals, we have that `[0,2,3] ≤ [0,1,2,3]`
as we can substitute the `0,2` step with `[0,1,2]`.
Of note is the fact that if `r a a`, then we have `[a,a] ≤ [a]`.
-/
protected inductive Le {rel : Rel α α} : {a b : α} → (l r : a -[rel]→* b) → Prop where
  | ofSingleton {a : α} (x : a -[rel]→* a) : RelSeriesHT.Le (.singleton a) x
  | ofSubstCons {a b : α} (hr : rel a b) (hseries : a -[rel]→* b) {c : α} {l r : b -[rel]→* c}
    (hle : RelSeriesHT.Le l r) : RelSeriesHT.Le (.cons a l hr) (hseries ++ r)

section
private lemma le_refl {a b : α} (l : a -[r]→* b) : l.Le l := l.rec (.ofSingleton <| .singleton ·)
  fun _ _ _ _ hr hle => Le.ofSubstCons hr (ofRel hr) hle

private lemma exists_eq_append_of_append_le' {a b c : α}
  (x : a -[r]→* b) (y : b -[r]→* c) (z : a -[r]→* c) (h : (x ++ y).Le z) :
    ∃ (x' : a -[r]→* b), ∃ (y' : b -[r]→* c), x' ++ y' = z ∧ x.Le x' ∧ y.Le y' := by
  induction x with
  | singleton a =>
    simp_all only [singleton_append]
    use (singleton a), z
    simp_all only [singleton_append, and_true, true_and]
    exact le_refl _
  | cons a l hab ih =>
    simp_all only [cons_append]
    cases h with
    | ofSubstCons hr hseries hle =>
      obtain ⟨x',y',rfl,hl,hr⟩ := ih _ _ hle
      use (hseries ++ x'), y'
      simp only [append_assoc, true_and]
      use (Le.ofSubstCons _ hseries hl)

private lemma le_trans {a b : α} {x y z : a -[r]→* b} (hxy : x.Le y) (hyz : y.Le z) : x.Le z := by
  induction hxy with
  | ofSingleton z => exact Le.ofSingleton z
  | ofSubstCons hr hseries hle ih =>
    obtain ⟨x',y',rfl,hx',hy'⟩ := exists_eq_append_of_append_le' _ _ _ hyz
    cases hx' with
    | ofSingleton x =>
      simp_all
      apply Le.ofSubstCons _ (singleton _) (ih hyz)
    | ofSubstCons hr' hseries hle =>
      simp_all
      rw [← append_assoc]
      apply Le.ofSubstCons _ (hseries ++ _) (ih hy')

instance {a b : α} : Preorder (a -[r]→* b) where
  le := RelSeriesHT.Le
  le_refl := le_refl
  le_trans a b c := le_trans


lemma exists_eq_append_of_append_le {a b c : α}
  (x : a -[r]→* b) (y : b -[r]→* c) (z : a -[r]→* c) (h : (x ++ y) ≤ z) :
    ∃ (x' : a -[r]→* b), ∃ (y' : b -[r]→* c), x' ++ y' = z ∧ x ≤ x' ∧ y ≤ y' :=
  exists_eq_append_of_append_le' x y z h

end

@[simp]
lemma le_def {a b :α} (x y : a -[r]→* b) : x.Le y ↔ x ≤ y := Iff.rfl

@[simp]
lemma singleton_le {a : α} (x : a -[r]→* a) : singleton a ≤ x := RelSeriesHT.Le.ofSingleton x

lemma cons_le_append (a : α) {b c : α} (hr : r a b) (x : a -[r]→* b) {y y' : b -[r]→* c}
    (hy : y ≤ y') : cons a y hr ≤ (x ++ y') := RelSeriesHT.Le.ofSubstCons hr x hy

@[elab_as_elim, induction_eliminator]
lemma le_induction {motive : {a b : α} → (x y : a -[r]→* b) → x ≤ y → Prop}
    (ofSingleton : {a : α} → (x : a-[r]→* a) → motive (singleton a) x (singleton_le x))
    (ofSubstCons : {a b : α} → (hr : r a b) → (hseries : a -[r]→* b) → {c : α} →
      {y y' : b -[r]→* c} → (hle : y ≤ y') → (ih : motive y y' hle) →
      motive (cons a y hr) (hseries ++ y') (cons_le_append a hr hseries hle) )
    {a b : α}
    {x y: a -[r]→* b} (hle : x ≤ y)
     : motive x y hle :=
  @Le.rec α r motive ofSingleton ofSubstCons a b x y hle

@[elab_as_elim, cases_eliminator]
lemma le_casesOn {motive : {a b : α} → (x y : a -[r]→* b) → x ≤ y → Prop}
    (ofSingleton : {a : α} → (x : a-[r]→* a) → motive (singleton a) x (singleton_le x))
    (ofSubstCons : {a b : α} → (hr : r a b) → (hseries : a -[r]→* b) → {c : α} →
      {y y' : b -[r]→* c} → (hle : y ≤ y') →
      motive (cons a y hr) (hseries ++ y') (cons_le_append a hr hseries hle) )
    {a b : α}
    {x y: a -[r]→* b} (hle : x ≤ y)
     : motive x y hle :=
  @Le.casesOn α r motive a b x y hle ofSingleton @ofSubstCons

@[simp]
lemma ofRel_le {a b : α} (hr : r a b) (x : a -[r]→* b) : ofRel hr ≤ x := by
  convert cons_le_append a hr (x) (singleton_le (r := r) (singleton b))
  simp

lemma append_right_mono {a b c : α} (l : a -[r]→* b):
  Monotone (α := b -[r]→* c) (l ++ ·) := by
  intro x y
  induction l with
  | singleton a => exact id
  | cons a l hab ih =>
    intro h
    exact cons_le_append a hab (ofRel hab) (ih h)

lemma append_left_mono {a b c : α} (l : b -[r]→* c):
  Monotone (α := a -[r]→* b) (· ++ l) := by
  intro x y h
  induction h with
  | ofSingleton x =>
    simp only [singleton_append]
    induction l with
    | singleton a =>
      exact singleton_le _
    | cons a l hab ih =>
      rw [← snoc_append]
      exact cons_le_append _ _ _ (le_refl _)
  | ofSubstCons hr hseries hle ih =>
    simp_all
    exact cons_le_append _ hr hseries (ih l)

lemma append_le_append {a b c : α} {x x' : a -[r]→* b} (hx : x ≤ x') {y y' : b -[r]→* c}
    (hy : y ≤ y') :
  x ++ y ≤ x' ++ y':= by
  trans x ++ y'
  · exact append_right_mono _ hy
  · exact append_left_mono _ hx

lemma map_mono {β : Type*} {s : Rel β β} (f : r →r s) {a b : α}:
    Monotone (α := a -[r]→* b) (map f) := by
  intro x y h
  induction h with
  | ofSingleton x => simp
  | ofSubstCons hr hseries hle ih =>
    simp only [map_cons, map_append]
    apply cons_le_append _ _ _ ih

lemma copy_mono {a a' b b' : α} (ha : a = a') (hb : b = b') :
    Monotone (α := a -[r]→* b) (copy · ha hb) := by
  intro x y h
  cases h with
  | ofSingleton x => aesop
  | ofSubstCons hr hseries hle =>
    cases ha; cases hb
    simp only [copy_rfl_rfl]
    apply cons_le_append _ _ _ hle

/-- `equiv` as an orderiso -/
def orderIso {β : Type*} {r: Rel α α} {s : Rel β β} (e: r ≃r s) {a b : α} :
    a -[r]→* b ≃o (e a) -[s]→* (e b) where
  __ := equiv e
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rw [← (equiv e).left_inv' x,← (equiv e).left_inv' y]
      rw [equiv_symm_apply,equiv_symm_apply]
      apply copy_mono _ _ (map_mono _ h)
    · intro h
      rw [equiv_apply, equiv_apply]
      exact map_mono _ h

@[simp]
lemma orderIso_apply {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s)
    {a b : α} (x : a -[r]→* b) : orderIso e x = equiv e x := rfl

@[simp]
lemma orderIso_symm_apply {β : Type*} {r : Rel α α} {s : Rel β β} (e : r ≃r s)
    {a b : α} (x : e a -[s]→* e b) : (orderIso e).symm x = (equiv e).symm x := rfl

lemma length_order_iso {β : Type*} {r : Rel α α} {s : Rel β β}
  (e: r ≃r s) {a b : α} {x : a -[r]→* b} : ((orderIso e) x).length = x.length := by simp


@[simp]
lemma snoc_le_append {a b : α} {x x' : a -[r]→* b}
    (hy : x ≤ x') (c : α) (hr : r b c) (y : b -[r]→* c): snoc x c hr ≤ (x' ++ y) := by
  induction x with
  | singleton a =>
    convert cons_le_append _ hr (x' ++ y) (singleton_le (singleton c)) using 1
    simp
  | cons a l hab ih =>
    simp only [snoc_cons]
    cases hy with
    | ofSubstCons hr' hseries hle' =>
      rw [append_assoc]
      convert cons_le_append a hab (hseries) (ih hle' hr y)

lemma reverse_mono {a b : α} : Monotone (α := a -[r]→* b) (·.reverse) := by
  intro x y hxy
  simp only
  induction hxy with
  | ofSingleton a => simp
  | ofSubstCons hr hseries hle hi => simp_all

/-- reversing a series is a galois-insertion with itself, i.e. reversing is an order isomorphism -/
def reverse_gi {a b : α} : GaloisInsertion (α := a -[r]→* b) (·.reverse) (·.reverse) where
  choice x _ := x.reverse
  gc := by
    rw [GaloisConnection]
    intro x y
    constructor
    · rw [← reverse_reverse y]
      nth_rw 2 [← reverse_reverse x]
      apply reverse_mono
    · nth_rw 2 [← reverse_reverse y]
      apply reverse_mono
  le_l_u := by intros;simp
  choice_eq _ _ := rfl

/-- reversing a series is a galois coinsertion with itself, meaning it is an order isomorphism -/
def reverse_gci {a b : α} : GaloisCoinsertion (α := a -[r]→* b) (·.reverse) (·.reverse) where
  choice x _ := x.reverse
  gc := by
    rw [GaloisConnection]
    intro x y
    constructor
    · rw [← reverse_reverse y]
      nth_rw 2 [← reverse_reverse x]
      apply reverse_mono
    · nth_rw 2 [← reverse_reverse y]
      apply reverse_mono
  u_l_le := by intros; simp
  choice_eq _ _ := rfl

lemma reverse_strictMono {a b : α} : StrictMono (α := a -[r]→* b) (·.reverse) := by
  intro x y hxy
  simp only
  have hle := reverse_mono hxy.le
  use hle
  contrapose hxy
  simp only [le_def, not_not,not_lt_iff_le_imp_le] at hxy ⊢
  rw [← reverse_reverse x, ← reverse_reverse y]
  exact fun _ => reverse_mono hxy
-- #check List.Sublist

lemma mem_of_le_of_mem {a b : α} {x y : a -[r]→* b} (hle : x ≤ y) : ∀ ⦃c:α⦄, c ∈ x → c ∈ y := by
  intro c
  rw [← mem_toList]
  induction hle with
  | ofSingleton x => simp_all
  | ofSubstCons hr hseries hle ih =>
    simp only [toList_cons, List.mem_cons, mem_toList, toList_append, List.mem_append]
    rintro (rfl|h)
    · simp
    · simp_all

lemma List.cons_sublist_iff' {a : α} {l₁ l₂ : List α} : (a::l₁).Sublist l₂ ↔
    ∃ r₁ r₂, r₁ ++ r₂ = l₂ ∧ a ∈ r₁ ∧ l₁.Sublist r₂ ∧ l₁.head? = r₂.head? := by
  constructor
  · intro h
    generalize heq:a :: l₁ = z at *
    induction h generalizing a l₁ with
    | slnil => contradiction
    | cons b h' ih =>
      cases heq
      specialize ih rfl
      obtain ⟨r₁,r₂,rfl,ha,hsub,hhead⟩ := ih
      use b::r₁,r₂,rfl,List.mem_cons_of_mem b ha,hsub
    | cons₂ a h' ih =>
      rename_i l₃ l₄ _
      cases heq
      cases l₃ with
      | nil =>
        simp_all
        use a::l₄,[]
        simp
      | cons head tail =>
        specialize ih rfl
        obtain ⟨r₁,r₂,rfl,hhead,hsub,hhead'⟩ := ih
        obtain ⟨m,n,rfl,_⟩ := List.eq_append_cons_of_mem hhead
        use a::m,head::n++r₂
        simp only [List.cons_append, List.append_assoc, List.mem_cons, true_or,
          List.cons_sublist_cons, List.head?_cons, and_true, true_and]
        exact List.sublist_append_of_sublist_right hsub
  · rintro ⟨r₁,r₂,rfl,hl,hr⟩
    simp_rw [List.cons_sublist_iff]
    use r₁, r₂,rfl,hl
    exact hr.left


lemma le_of_toList_sublist_toList {a b : α} (x y : a -[r]→* b)
    (hxy : x.toList.Sublist y.toList) : x ≤ y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [toList_cons]
    rename_i c d
    obtain ⟨r1,r2,hy,hmem,hsub,hhead⟩ := List.cons_sublist_iff'.mp hxy
    clear hxy
    obtain ⟨c',n,m,rfl,rfl,rfl⟩ := exists_eq_append_of_toList_eq_append' y _ _ (by
      apply List.ne_nil_of_mem (a := d)
      apply hsub.mem
      simp only [mem_toList, getLast_mem]) hy.symm
    simp only [head?_toList, List.head?_tail] at hhead
    cases hhead
    specialize ih _ hsub
    exact cons_le_append a hab n ih


end LE

section IsReduced
/-- A series `a -[r]→* b` is reduced when all larger chains are longer,
  or quivalently, when all adjacent elements are distinct. -/
@[mk_iff]
class IsReduced {a b : α} (x : a -[r]→* b) : Prop where
  isReduced (y : a -[r]→* b) : x ≤ y → x.length ≤ y.length

@[simp]
instance isReduced_singleton (a : α) : (singleton (r := r) a).IsReduced := by
  simp only [singleton_le, length_singleton, zero_le, imp_self, implies_true, isReduced_iff]

@[simp]
lemma isReduced_cons_iff (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) :
    (cons a x hr).IsReduced ↔ a ≠ b ∧ x.IsReduced := by
  simp only [isReduced_iff, length_cons, ne_eq]
  constructor
  · intro h
    have : a ≠ b := by
      rintro rfl
      specialize h x (cons_le_append a hr (singleton a) (le_refl _))
      simp at h
    use this
    intro y hy
    specialize h (cons a y hr) (cons_le_append a hr (ofRel hr) hy)
    simpa using h
  · rintro ⟨hne,h⟩
    intro y hy
    cases hy with
    | ofSubstCons hr hseries hle =>
      specialize h _ hle
      simp only [length_append]
      have := length_pos_of_ne hne hseries
      omega

lemma append_isReduced {a b c} {x : a -[r]→* b} {y : b -[r]→* c} :
    (x ++ y).IsReduced ↔ x.IsReduced ∧ y.IsReduced := by
  induction x with
  | singleton a => simp
  | cons a l hab ih => simp_all [and_assoc]

/-- `x.reduce` computes the canonical reduced form of an `r` series by
  dropping "reflexive" steps. the result will be equivalent to the original
  with respect to the ordering of series. -/
noncomputable def reduce {a b : α} (x : a -[r]→* b) : a -[r]→* b :=
  open Classical in
  match x with
  | .singleton a => .singleton a
  | @cons _ _ a b c l hr => if h: a = b then copy (reduce l) (h.symm) rfl else .cons a (reduce l) hr

@[simp]
lemma reduce_singleton (a : α) : reduce (.singleton (r := r) a) = .singleton a := rfl

lemma reduce_cons_of_eq (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) (hab : a = b) :
    reduce (cons a x hr) = copy (reduce x) (hab.symm) rfl := by
  rw [reduce,dif_pos hab]

lemma reduce_cons_of_ne (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) (hab : a ≠ b) :
    reduce (cons a x hr) = cons a (reduce x) hr := by
  rw [reduce,dif_neg hab]

@[simp]
lemma reduce_cons [DecidableEq α] (a : α) {b c : α} (x : b -[r]→* c) (hr : r a b) :
    reduce (cons a x hr) =
      if h : a = b then copy (reduce x) (h.symm) rfl else cons a (reduce x) hr := by
  rw [reduce]
  congr

@[simp]
lemma reduce_append {a b c : α} (x : a -[r]→* b) (y : b -[r]→* c) : reduce (x ++ y) =
    reduce x ++ reduce y := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all
    rw [reduce,reduce]
    split <;> rename_i h
    · cases h
      simp_all
    · simp_all

@[simp]
lemma toList_reduce [DecidableEq α] {a b : α} (x : a -[r]→* b) :
    toList (reduce x) = x.toList.destutter (· ≠ ·) := by
  induction x with
  | singleton a =>
    simp
  | cons a l hab ih =>
    simp only [reduce_cons, ne_eq, toList_cons]
    cases l with
    | singleton a =>
      simp only [reduce_singleton, toList_singleton, List.destutter_pair, ite_not]
      split <;> simp_all
    | cons a l hab =>
      simp only [toList_cons]
      split <;> simp_all only [ne_eq, toList_cons, toList_copy]
      · rw [List.destutter_cons_cons]
        simp_all only [not_true_eq_false, ite_false, reduce_cons]
        rfl
      · rw [List.destutter_cons_cons]
        simp_all only [not_false_eq_true, ite_true, List.cons.injEq, true_and]
        rw [← List.destutter_cons']

@[simp]
lemma length_reduce_le_length_self {a b : α} (x : a -[r]→* b) : x.reduce.length ≤ x.length := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> simp_all ; omega

/-- the universal property of `IsReduced` -/
lemma le_reduce_of_le {a b : α} {x y : a -[r]→* b} (hle : x ≤ y) : x ≤ y.reduce := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    cases hle with
    | ofSubstCons hr hseries hle =>
      rw [reduce_append]
      exact cons_le_append a hab hseries.reduce (ih hle)

lemma reduce_le_self {a b : α} (x : a -[r]→* b) : x.reduce ≤ x := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> rename_i h
    · cases h
      apply le_trans ih
      exact append_left_mono l (singleton_le (ofRel hab))
    · exact append_right_mono (ofRel hab) (ih)

@[simp]
lemma self_le_reduce {a b : α} (x : a -[r]→* b) : x ≤ x.reduce :=
  le_reduce_of_le (le_refl x)

lemma reduce_mono {a b : α} : Monotone (α := a -[r]→* b) (·.reduce) :=
  fun a _ hle => le_trans (reduce_le_self a) (le_reduce_of_le hle)

lemma reduce_gc {a b : α} : GaloisConnection (α := a -[r]→* b) (id) (reduce) := by
  rw [GaloisConnection]
  simp_all only [id_eq]
  intro x y
  refine ⟨le_reduce_of_le,(le_trans · (reduce_le_self y))⟩

lemma reduce_le_reduce_iff {a b : α} (x y : a -[r]→* b) : x ≤ y ↔ x.reduce ≤ y.reduce := by
  constructor
  · apply reduce_mono
  exact (le_trans (self_le_reduce x) <| le_trans · (reduce_le_self y))

lemma reduce_strictMono {a b : α} : StrictMono (α := a -[r]→* b) (·.reduce) := by
  intro x y hlt
  simpa [lt_iff_le_not_le,← reduce_le_reduce_iff]

@[simp]
lemma reduce_isReduced {a b : α} (x : a -[r]→* b) : x.reduce.IsReduced := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> rename_i h
    · cases h; simp_all
    · simp_all

lemma reduce_eq_self_of_isReduced {a b : α} (x : a -[r]→* b) (hx : x.IsReduced) :
    x.reduce = x := by
  induction x with
  | singleton a => simp_all
  | cons a l hab ih =>
    simp_all
    rw [reduce_cons_of_ne a l hab hx.left, ih]

@[simp]
lemma reduce_reduce {a b : α} (x : a -[r]→* b) : x.reduce.reduce = x.reduce := by
  rw [reduce_eq_self_of_isReduced _ (reduce_isReduced x)]

@[simp]
lemma IsReduced_ofRel {a b : α} (hr : r a b) : (ofRel hr).IsReduced ↔ a ≠ b := by
  constructor
  · rintro h rfl
    have h := h.isReduced _ (cons_le_append a hr (singleton a) (le_refl (singleton a)))
    simp at h
  · rw [isReduced_iff]
    contrapose!
    rintro ⟨z,hz1,hz2⟩
    cases z <;> simp_all

@[simp]
lemma isReduced_of_irrefl [IsIrrefl α r] {a b : α} (x : a -[r]→* b) : x.IsReduced := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    simp_all only [isReduced_cons_iff, ne_eq, and_true]
    rintro rfl
    exact irrefl _ hab

lemma toList_reduce_sublist_of_reduce_le {a b : α} (x y : a -[r]→* b) :
  x.reduce ≤ y → x.reduce.toList.Sublist y.toList := by
  induction x with
  | singleton a => simp
  | cons a l hab ih =>
    rw [reduce]
    split <;> rename_i h
    · cases h
      simp_all
    · simp_all only [toList_cons]
      intro h
      cases h with
      | ofSubstCons hr hseries hle =>
        refine List.cons_sublist_iff.mpr ?_
        simp only [← toList_append, toList_append']
        refine ⟨hseries.toList.dropLast,_,rfl,?_,ih _ hle⟩
        cases hseries with
        | singleton a => contradiction
        | cons a l hab =>
          rw [toList_cons,List.dropLast_cons_of_ne_nil l.toList_ne_nil]
          simp

lemma le_iff_sublist_of_IsReduced {a b : α} {x : a -[r]→* b} (hx : x.IsReduced) (y : a -[r]→* b) :
    x.toList.Sublist y.toList ↔ x ≤ y := by
  constructor
  · exact le_of_toList_sublist_toList x y
  · intro h
    rw [← reduce_eq_self_of_isReduced _ hx] at h ⊢
    exact toList_reduce_sublist_of_reduce_le x y h

lemma le_antisymm_of_isReduced_of_isReduced {a b : α} {x y : a -[r]→* b} (hx : x.IsReduced)
    (hy : y.IsReduced) : x ≤ y → y ≤ x → x = y := by
  intro hle hge
  refine eq_of_heq (ext _ _ ?_).right.right
  apply List.Sublist.antisymm
  · rwa [le_iff_sublist_of_IsReduced hx]
  · rwa [le_iff_sublist_of_IsReduced hy]

instance [IsIrrefl α r] {a b : α} : PartialOrder (a -[r]→* b) where
  le_antisymm x y :=
    le_antisymm_of_isReduced_of_isReduced (isReduced_of_irrefl x) (isReduced_of_irrefl y)

end IsReduced

lemma eq_of_le_of_length_le {a b : α} {x y : a -[r]→* b} (hx : x.IsReduced) :
  x ≤ y → y.length ≤ x.length → x = y := by
  intro hle hlength
  refine eq_of_heq (ext _ _ ?_).right.right
  rw [← le_iff_sublist_of_IsReduced hx] at hle
  rw [← Nat.add_le_add_iff_right (n := 1)] at hlength
  simp_rw [← length_toList] at hlength
  exact hle.eq_of_length_le hlength

lemma length_mono_of_isReduced {a b : α} {x : a -[r]→* b} (hx : x.IsReduced) (y : a -[r]→* b) :
  x ≤ y → x.length ≤ y.length := by
  exact hx.isReduced y

lemma length_strictMono_of_isReduced {a b : α} {x : a -[r]→* b} (hx : x.IsReduced)
    (y : a -[r]→* b) : x < y → x.length < y.length := by
  simp_rw [lt_iff_le_not_le]
  rintro ⟨hle,hnle⟩
  use hx.isReduced y hle
  contrapose! hnle
  have hsublist: x.toList.Sublist y.toList := (le_iff_sublist_of_IsReduced hx y).mpr hle
  have heq : x.toList = y.toList := by
    apply hsublist.eq_of_length_le
    rw [length_toList,length_toList]
    omega
  cases eq_of_heq (ext _ _ heq).right.right
  rfl

end RelSeriesHT
set_option linter.style.longFile 1800
