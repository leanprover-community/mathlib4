set_option autoImplicit true

inductive Dyck : Nat → Type
| nil : Dyck 0
| up {n} : Dyck n → Dyck (n + 1)
| down {n} : Dyck (n + 1) → Dyck n

namespace Dyck

def length : ∀ {n}, Dyck n → Nat
  | _, nil => 0
  | _, up d
  | _, down d => length d + 1

def cast (h : n = m) : Dyck n → Dyck m :=
  by subst h; exact id

def concat : ∀ {n m}, Dyck n → Dyck m → Dyck (n + m)
  | _, _, d, nil => d
  | _, _, d, up d' => up (concat d d')
  | _, _, d, down d' => down (cast (by omega) (concat d d'))

def prependUp (x : Dyck n) : Dyck (n + 1) := cast (by omega) (concat (up nil) x)

def concatRev : Dyck (n + m) → Dyck m → Dyck n
  | d, nil => d
  | d, up e => concatRev (down d) e
  | d, down e => concatRev (cast (by omega) (up d)) e

/-! Theorems about `Dyck.cast`. -/

@[simp] theorem cast_cast {n m o} (h : n = m) (h' : m = o) (d : Dyck n) :
    cast h' (cast h d) = cast (by simp [h, h']) d := by
  subst h h'
  rfl

@[simp] theorem cast_refl {n} (d : Dyck n) : cast (by simp) d = d := by
  cases d <;> rfl

@[simp] theorem up_cast (h : n = m) : up (cast h d) = cast (by simp [h]) (up d) := by
  subst h; rfl

@[simp] theorem down_cast (h : n + 1 = m + 1) : down (cast h d) = cast (by omega) (down d) := by
  cases h; rfl

/-! Theorems about `Dyck.concat`. -/

@[simp] theorem cast_concat {n m o} (d : Dyck n) (e : Dyck m) (h : n = o) :
    concat (cast h d) e = cast (by simp [h]) (concat d e) :=
  by subst h; simp

@[simp] theorem concat_cast {n m o} (d : Dyck n) (e : Dyck m) (h : m = o) :
    concat d (cast h e) = cast (by simp [h]) (concat d e) :=
  by subst h; simp

theorem concat_assoc {n m o} (d : Dyck n) (e : Dyck m) (f : Dyck o) :
    concat (concat d e) f = cast (by omega) (concat d (concat e f)) :=
  match f with
  | nil
  | up _
  | down _ => by simp [concat, concat_assoc]

/-! Theorems about `Dyck.prependUp`. -/

theorem prependUp_cast (h : n = m) :
    prependUp (cast h d) = cast (by omega) (prependUp d) :=
  by subst h; simp

theorem prependUp_up : prependUp (up d) = up (prependUp d) := by
  match d with
  | nil => rfl
  | up d
  | down d => simp [prependUp, concat, down_cast, prependUp_up]

theorem prependUp_down {n} {d : Dyck (n+1)} : prependUp (down d) = down (prependUp d) := by
  match n, d with
  | n, up d
  | n, down d => simp [prependUp, concat, down_cast, prependUp_down]

def leftCap : ∀ {n}, Dyck (n + 2) → Dyck n
  | 0, up x => down x
  | n + 1, up x => up (leftCap x)
  | _, down x => down (leftCap x)

@[simp] theorem leftCap_cast (h : n + 2 = m + 2) :
    leftCap (cast h d) = cast (by omega) (leftCap d) := by
  cases h
  rfl

def cap (k : Nat) (d : Dyck (n + k + 2)) : Dyck (n + k) :=
  match k, d with
  | 0, up x => down x
  | k+1, up x => up (cap k x)
  | k, down x => down (cap (k+1) x)

@[local simp] private theorem cap_cast {k} (h : n + k + 2 = m + k + 2) (d : Dyck (n + k + 2)):
    cap k (cast h d) = cast (by omega) (cap k d) := by
  have h' : n = m := by omega
  subst h'
  rfl

private theorem cap_prependUp {n} {d : Dyck (n + 1 + k + 1)} :
    cap (n := n + 1) k (prependUp d) =
      cast (by omega) (prependUp (cap (n := n) k (cast (by omega) d))) := by
  match k, d with
  | 0, up d =>
    unfold prependUp
    rw [concat, ← up_cast, cap, ← up_cast (by omega), cap, concat, cast_cast, cast_refl, down_cast]
    · rfl
    · simp; omega
  | k+1, up x =>
    rw [prependUp_up, cap, cap_prependUp, ← up_cast, cap, up_cast, prependUp_up]
  | _, down d =>
    rw [prependUp_down, cap, cap_prependUp, ← down_cast, cap, down_cast, prependUp_down]

def cap' (k : Nat) (d : Dyck (n + 2)) : Dyck n :=
  let k' := min k n
  cast (by omega) (cap (n := n - k') k' (cast (by omega) d))

theorem cap'_cap'_of_ge (h : k₁ ≥ k₂)


theorem cap_cap_of_ge (h : k₁ ≥ k₂) (w : m ≥ {d : Dyck m} : cap k₁ (cast sorry (cap k₂ d)) = cap k₂ (cap (k₁ + 2) d) := sorry

abbrev rightCap (d : Dyck (n + 2)) : Dyck n := cap 0 d

theorem rightCap_up : rightCap (up d) = down d := by
  rw [rightCap, cap]

theorem rightCap_prependUp {n} {d : Dyck (n + 2)} :
    rightCap (prependUp d) = prependUp (rightCap d) := by
  rw [rightCap, cap_prependUp]
  rfl

private theorem cap_leftCap {n} {d : Dyck (n + k + 4)} :
    cap k (leftCap d) =
      leftCap (cast (by omega) (cap (n := n + 2) k (cast (by omega) d))) := by
  match k, d with
  | 0, up x => simp [leftCap, cap]
  | k+1, up x =>
    rw [leftCap, cap, cap_leftCap, ← up_cast (by omega), cap, ← up_cast, leftCap]
  | _, down x =>
    rw [leftCap, cap, cap_leftCap, ← down_cast (by omega), cap, ← down_cast, leftCap]

theorem rightCap_leftCap {n} {d : Dyck (n + 4)} : rightCap (leftCap d) = leftCap (rightCap d) := by
  rw [rightCap, cap_leftCap, leftCap_cast, cap_cast, leftCap_cast, cast_cast]
  rfl

theorem cap_eq_leftCap {d : Dyck (0 + k + 2)} : cap (n := 0) k d = leftCap d := by
  match k, d with
  | 0, up x => rw [cap, leftCap]
  | k+1, up x => rw [cap, cap_eq_leftCap, leftCap]
  | _, down x => rw [cap, cap_eq_leftCap, leftCap]

theorem rightCap_eq_leftCap {d : Dyck 2} : rightCap d = leftCap d := by
  match d with
  | up x => rw [leftCap, rightCap_up]
  | down x => rw [leftCap, rightCap, cap, cap_eq_leftCap]

def flip : Dyck n → Dyck n
  | nil => nil
  | up x => prependUp (flip x)
  | down x => leftCap (prependUp (flip x))

example : flip nil.up.down = nil.up.down := rfl
example : flip nil.up.up.up = nil.up.up.up := rfl
example : flip nil.up.up.up.down = nil.up.down.up.up := rfl
example : flip nil.up.up.down.down.up.down = nil.up.down.up.up.down.down := rfl

theorem flip_cast (h : n = m) : flip (cast h d) = cast h (flip d) := by
  subst h; rfl

theorem flip_up : flip (up d) = prependUp (flip d) := rfl
theorem flip_down : flip (down d) = leftCap (prependUp (flip d)) := rfl

theorem flip_prependUp {n} {d : Dyck n} : flip (prependUp d) = up (flip d) := by
  rw [prependUp, flip_cast]
  induction d with
  | nil => rfl
  | @up n d ih =>
    rw [concat, flip_up]
    replace ih := congrArg (cast (by omega : n + 1 = 0 + 1 + n)) ih
    rw [cast_cast, cast_refl] at ih
    rw [ih, prependUp_cast, cast_cast, cast_refl, flip_up, prependUp_up]
  | @down n d ih =>
    rw [concat, flip_down, flip_cast]
    replace ih := congrArg (cast (by omega : n + 1 + 1 = 0 + 1 + (n + 1))) ih
    rw [cast_cast, cast_refl] at ih
    rw [ih, cast_cast, prependUp_cast, flip_down, leftCap_cast, cast_cast, cast_refl, prependUp_up,
      leftCap]

theorem flip_leftCap {n} {d : Dyck (n+2)} : flip (leftCap d) = rightCap (flip d) := by
  match n, d with
  | 0, up x =>
    rw [leftCap, flip_up, flip_down, rightCap_eq_leftCap]
  | n+1, up x =>
    rw [leftCap, flip_up, flip_leftCap, flip_up, rightCap_prependUp]
  | _, down x =>
    rw [leftCap, flip_down, flip_leftCap, flip_down, ← rightCap_prependUp, rightCap_leftCap]

theorem flip_flip : flip (flip d) = d := by
  induction d with
  | nil => rfl
  | up d ih =>
    rw [flip_up]
    cases d with
    | nil => rfl
    | up d
    | down d => rw [flip_prependUp, ih]
  | down d ih =>
    rw [flip_down]
    cases d with
    | up d
    | down d => rw [flip_leftCap, flip_prependUp, ih, rightCap_up]

theorem flip_rightCap : flip (rightCap d) = leftCap (flip d) := by
  rw [← flip_flip (d := leftCap _), flip_leftCap, flip_flip]

end Dyck
