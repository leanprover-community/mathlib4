import Mathlib

def Fin.range (n : Nat) : List (Fin n) :=
  (List.range n).attach.map fun ⟨i, h⟩ => ⟨i, by simpa using h⟩

@[simp] theorem Fin.range_zero : Fin.range 0 = [] := by
  simp [Fin.range]

@[simp] theorem Fin.length_range (n : Nat) : (Fin.range n).length = n := by
  simp [Fin.range, List.length_map, List.length_range]

@[simp] theorem Fin.getElem_range (n : Nat) (i : Nat) (h : i < (Fin.range n).length) : (Fin.range n)[i] = ⟨i, by simpa using h⟩ := by
  simp [Fin.range, List.getElem_map, List.getElem_range]

@[simp] theorem Fin.mem_range (n : Nat) (i : Fin n) : i ∈ Fin.range n := by
  simp only [range, List.mem_map, List.mem_attach, true_and, Subtype.exists, List.mem_range]
  refine ⟨i, by simp, rfl⟩

def toFin? (x : Int) : Option (Fin 8) :=
  if 0 ≤ x then if h : x.toNat < 8 then some ⟨x.toNat, h⟩ else none else none

@[simp] theorem toFin?_cast (x : Fin 8) : toFin? (x : Int) = some x := by
  simp [toFin?]

@[simp] theorem toFin?_eq_some_iff (x : Int) : toFin? x = some y ↔ x = y := by
  simp only [toFin?]
  split <;> rename_i h₁
  · simp only [Option.dite_none_right_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨h, rfl⟩
      simp [h₁]
    · rintro rfl
      simp
  · simp only [reduceCtorEq, false_iff]
    omega
namespace List

@[simp] theorem map_set {α β : Type} (f : α → β) (l : List α) (i : Nat) (a : α) :
    (l.set i a).map f = (l.map f).set i (f a) := by
  cases l with
  | nil => simp
  | cons x l => cases i <;> simp

end List

@[simp] theorem boole_pos_iff [Decidable p] : (0 < if p then 1 else 0) ↔ p := by
  split <;> simp_all

theorem List.getElem_le_sum_nat (l : List Nat) (i : Nat) (h : i < l.length) : l[i] ≤ l.sum := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp at h
      specialize ih _ h
      simp
      omega

theorem List.apply_getElem_le_sum_map_nat (f : α → Nat) (l : List α) (i : Nat) (h : i < l.length) : f l[i] ≤ (l.map f).sum := by
  have := (l.map f).getElem_le_sum_nat i (by simpa using h)
  simpa using this

@[simp] theorem List.sum_set_nat (l : List Nat) (i : Nat) (h : i < l.length) (a : Nat) :
    (l.set i a).sum = l.sum - l[i] + a := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp [Nat.add_comm]
    | succ i =>
      simp at h
      have : l[i] ≤ l.sum := getElem_le_sum_nat _ _ _
      simp_all
      omega

namespace Array

@[simp] theorem getElem_toList (a : Array α) (i : Nat) (h : i < a.size) : a.toList[i] = a[i] := rfl

@[simp] theorem getElem_mk (data : List α) (i : Nat) (h : i < data.length) : (Array.mk data)[i] = data[i] := rfl

@[simp] theorem map_mk (f : α → β) (data : List α) :
    Array.map f (Array.mk data) = Array.mk (List.map f data) := by
  ext <;> simp

@[simp] theorem map_set (f : α → β) (xs : Array α) (i : Fin xs.size) (a : α) :
    (xs.set i a).map f = (xs.map f).set (Fin.cast (by simp) i) (f a) := by
  simp [Array.set]

def countP (p : α → Bool) (xs : Array α) : Nat :=
  xs.toList.countP p

theorem countP_set (p : α → Bool) (l : Array α) (i : Fin l.size) (a : α) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  simp [countP, List.countP_set]

theorem exists_mem_toList {as : Array α} {p : α → Prop} :
    (∃ x ∈ as.toList, p x) ↔ ∃ (i : Nat) (h : i < as.size), p as[i] := by
  constructor
  · rintro ⟨x, m, w⟩
    obtain ⟨i, h, rfl⟩ := List.getElem_of_mem m
    exact ⟨i, h, w⟩
  · rintro ⟨i, h, w⟩
    exact ⟨as[i], getElem_mem_toList as h, w⟩

@[simp] theorem countP_pos_iff (p : α → Bool) (l : Array α) :
    0 < l.countP p ↔ ∃ (i : Nat) (h : i < l.size), p l[i] := by
  simp [countP, exists_mem_toList]

@[simp] theorem one_le_countP_iff (p : α → Bool) (l : Array α) : 1 ≤ l.countP p ↔ ∃ (i : Nat) (h : i < l.size), p l[i] :=
  countP_pos_iff p l

def sum [Zero α] [Add α] (xs : Array α) : α :=
  xs.toList.sum

@[simp] theorem sum_set (v : Array Nat) (i : Fin v.size) (a : Nat) :
    (v.set i a).sum = v.sum - v[i] + a := by
  simp [sum]

theorem getElem_le_sum_nat (l : Array Nat) (i : Nat) (h : i < l.size) : l[i] ≤ l.sum := by
  simp [sum]
  apply List.getElem_le_sum_nat

theorem apply_getElem_le_sum_map_nat (f : α → Nat) (l : Array α) (i : Nat) (h : i < l.size) : f l[i] ≤ (l.map f).sum := by
  have := (l.map f).getElem_le_sum_nat i (by simpa using h)
  simpa using this

end Array

structure Vec (n : Nat) (α : Type _) where
  toArray : Array α
  size : toArray.size = n

namespace Vec

@[simp] theorem size_toArray (v : Vec n α) : v.toArray.size = n := by
  simp [set, v.size]

instance [Repr α] : Repr (Vec n α) where
  reprPrec v n := reprPrec v.1 n

instance : GetElem (Vec n α) Nat α (fun _ i => i < n) where
  getElem v i h := v.1[i]'(Nat.lt_of_lt_of_eq h v.2.symm)

@[simp] theorem getElem_toArray (v : Vec n α) (i : Nat) (h : i < v.toArray.size) : v.toArray[i] = v[i]'(by simpa using h) := rfl

@[simp] theorem getElem_mk (data : Array α) (size : data.size = n) (i : Nat) (h : i < n) : (Vec.mk data size)[i] = data[i] := rfl

def replicate (n : Nat) (v : α) : Vec n α := ⟨Array.mkArray n v, by simp⟩

instance : Inhabited (Vec 0 α) := ⟨⟨#[], rfl⟩⟩
instance [Inhabited α] : Inhabited (Vec n α) := ⟨replicate n default⟩

def set (v : Vec n α) (i : Fin n) (a : α) : Vec n α :=
  ⟨v.1.set ⟨i, Nat.lt_of_lt_of_eq i.2 v.2.symm⟩ a, by simp [Array.set, v.2]⟩

@[simp] theorem toArray_set (v : Vec n α) (i : Fin n) (a : α) : (v.set i a).toArray = v.toArray.set (Fin.cast v.2.symm i) a := rfl

@[simp] theorem set_mk {data : Array α} {size : data.size = n} :
    (mk data size).set i a = mk (data.set (Fin.cast size.symm i) a) (by simp [size]) := rfl

@[simp] theorem getElem_set (v : Vec n α) (i : Fin n) (a : α) (j : Nat) (h : j < n) : (v.set i a)[j] = if i = j then a else v[j] := by
  cases v
  simp [Array.getElem_set, Fin.ext_iff]  -- Annoying that we need to use `ext_iff` here.

def map (f : α → β) (v : Vec n α) : Vec n β :=
  ⟨v.1.map f, by simp [v.2]⟩

@[simp] theorem toArray_map (f : α → β) (v : Vec n α) : (v.map f).toArray = v.toArray.map f := rfl

@[simp] theorem getElem_map (f : α → β) (v : Vec n α) (i : Nat) (h : i < n) : (v.map f)[i] = f v[i] := by
  simp [map]

@[simp] theorem map_set (f : α → β) (v : Vec n α) (i : Fin n) (a : α) : (v.set i a).map f = (v.map f).set i (f a) := by
  simp [map]

def countP (p : α → Bool) (v : Vec n α) : Nat :=
  v.toArray.countP p

theorem countP_set (p : α → Bool) (l : Vec n α) (i : Fin n) (a : α) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  simp [countP, Array.countP_set]

@[simp] theorem countP_pos_iff (p : α → Bool) (l : Vec n α) :
    0 < l.countP p ↔ ∃ (i : Nat) (h : i < n), p l[i] := by
  simp [countP]

@[simp] theorem one_le_countP_iff (p : α → Bool) (l : Vec n α) : 1 ≤ l.countP p ↔ ∃ (i : Nat) (h : i < n), p l[i] :=
  countP_pos_iff p l

def sum [Zero α] [Add α] (v : Vec n α) : α :=
  v.toArray.sum

@[simp] theorem sum_set (v : Vec n Nat) (i : Fin n) (a : Nat) :
    (v.set i a).sum = v.sum - v[i] + a := by
  simp [sum]

theorem getElem_le_sum_nat (l : Vec n Nat) (i : Nat) (h : i < n) : l[i] ≤ l.sum := by
  simp [sum]
  apply Array.getElem_le_sum_nat

theorem apply_getElem_le_sum_map_nat (f : α → Nat) (l : Vec n α) (i : Nat) (h : i < n) : f l[i] ≤ (l.map f).sum := by
  have := (l.map f).getElem_le_sum_nat i (by simpa using h)
  simpa using this

end Vec

namespace Chess

inductive Piece where
  | king
  | queen
  | rook
  | bishop
  | knight
  | pawn
deriving Repr, DecidableEq

/-! `x` is file, `y` is rank -/

structure Position where
  whiteToMove : Bool
  board : Vec 8 (Vec 8 (Option (Bool × Piece)))
deriving Repr

-- So much missing API:
-- #check Array.count
-- #check Vec.map
-- #check Vec.countP

namespace Position

def occupied (pos : Position) (x : Int) (y : Int) : Bool :=
  match toFin? x, toFin? y with
  | some x, some y => pos.board[x][y].isSome
  | _, _ => false

@[simp] theorem isSome_getElem_getElem_board (pos : Position) (x : Fin 8) (y : Fin 8) :
    pos.board[(x : Nat)][(y : Nat)].isSome = pos.occupied x y := by
  simp [occupied]

def friendly (pos : Position) (x : Int) (y : Int) : Bool :=
  match toFin? x, toFin? y with
  | some x, some y =>
    match pos.board[x][y], pos.whiteToMove with
    | some (true, _), true => true
    | some (false, _), false => true
    | _, _ => false
  | _, _ => false

def countPieces (pos : Position) : Nat :=
  (pos.board.map (fun file => file.countP Option.isSome)).sum

theorem countPieces_eq (pos : Position) :
    pos.countPieces = ((Fin.range 8).map fun (x : Fin 8) => (Fin.range 8).countP fun (y : Fin 8) => pos.occupied x y).sum := by
  sorry

end Position

def rookDirs : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]
def bishopDirs : List (Int × Int) := [(1, 1), (-1, -1), (1, -1), (-1, 1)]
def knightDirs : List (Int × Int) := [(2, 1), (2, -1), (-2, 1), (-2, -1), (1, 2), (1, -2), (-1, 2), (-1, -2)]
def kingDirs := rookDirs ++ bishopDirs
def queenDirs := rookDirs ++ bishopDirs

def onBoard? (pos : Int × Int) : Option (Fin 8 × Fin 8) := do
  let (x, y) := pos
  let x? ← toFin? x
  let y? ← toFin? y
  pure (x?, y?)

@[simp] theorem onBoard?_eq_some_iff (pos : Int × Int) :
    onBoard? pos = some (x, y) ↔ (x : Int) = pos.1 ∧ (y : Int) = pos.2 := by
  simp only [onBoard?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some,
    toFin?_eq_some_iff, Option.some.injEq, Prod.mk.injEq, exists_eq_right_right]
  simp [eq_comm]

def kingMoves (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  kingDirs.map (fun (dx, dy) => (x + dx, y + dy)) |>.filterMap onBoard?

def knightMoves (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  knightDirs.map (fun (dx, dy) => (x + dx, y + dy)) |>.filterMap onBoard?

def unoccupiedUntil (occupied : Int → Int → Bool) (x : Nat) (y : Nat) (dx dy : Int) (s : Nat) : Bool :=
  (List.iota (s-1)).all fun i => !occupied (x + i * dx) (y + i * dy)

def unblockedMoves (occupied : Int → Int → Bool) (x : Nat) (y : Nat) (dx dy : Int) : List (Fin 8 × Fin 8) :=
  (List.iota 7).filterMap (fun (s : Nat) => if unoccupiedUntil occupied x y dx dy s then some (x + s * dx, y + s * dy) else none)
    |>.filterMap onBoard?

def rookMoves (occupied : Int → Int → Bool) (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  rookDirs.bind fun (dx, dy) => unblockedMoves occupied x y dx dy

def bishopMoves (occupied : Int → Int → Bool) (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  bishopDirs.bind (fun (dx, dy) => unblockedMoves  occupied x y dx dy)

def queenMoves (occupied : Int → Int → Bool) (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  queenDirs.bind (fun (dx, dy) => unblockedMoves  occupied x y dx dy)

def pawnMoves (occupied : Int → Int → Bool) (whiteToMove : Bool) (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  let candidates :=
    if whiteToMove then
      if y = 7 then [] else
        let canMove := !occupied x (y + 1)
        let canMoveTwice := y = 1 && (!occupied x 2) && (!occupied x 3)
        let canCaptureLeft := occupied (x - 1) (y + 1)
        let canCaptureRight := occupied (x + 1) (y + 1)
        (if canMove then [(0, 1)] else []) ++ (if canMoveTwice then [(0, 2)] else []) ++
          (if canCaptureLeft then [(-1, 1)] else []) ++ (if canCaptureRight then [(1, 1)] else [])
    else
      if y = 0 then [] else
        let canMove := !occupied x (y - 1)
        let canMoveTwice := y = 6 && (!occupied x (y - 1)) && (!occupied x (y - 2))
        let canCaptureLeft := occupied (x - 1) (y - 1)
        let canCaptureRight := occupied (x + 1) (y - 1)
        (if canMove then [(0, -1)] else []) ++ (if canMoveTwice then [(0, -2)] else []) ++
          (if canCaptureLeft then [(-1, -1)] else []) ++ (if canCaptureRight then [(1, -1)] else [])
  candidates.map (fun (dx, dy) => (x + dx, y + dy)) |>.filterMap onBoard?

namespace Position

def pieceMoves (pos : Position) (piece : Piece) (x : Nat) (y : Nat) : List (Fin 8 × Fin 8) :=
  let candidates := match piece with
  | .king => kingMoves x y
  | .queen => queenMoves pos.occupied x y
  | .rook => rookMoves pos.occupied x y
  | .bishop => bishopMoves pos.occupied x y
  | .knight => knightMoves x y
  | .pawn => pawnMoves pos.occupied pos.whiteToMove x y
  candidates.filter (fun (x', y') => pos.friendly x' y' = false)

def activePiece? (pos : Position) (x y : Fin 8) : Option Piece :=
  match pos.board[x][y], pos.whiteToMove with
  | some (true, p), true => some p
  | some (false, p), false => some p
  | _, _ => none

def erase (pos : Position) (x y : Fin 8) : Position :=
  { pos with board := pos.board.set x (pos.board[x].set y none) }

def set (pos : Position) (x y : Fin 8) (p : Piece) : Position :=
  { pos with board := pos.board.set x (pos.board[x].set y (some (pos.whiteToMove, p))) }

def endTurn (pos : Position) : Position :=
  { pos with whiteToMove := !pos.whiteToMove }

def move (pos : Position) (piece : Piece) (x y : Fin 8) (x' y' : Fin 8) : Position :=
  pos.erase x y |>.set x' y' piece |>.endTurn

def moves (pos : Position) : List Position :=
  Fin.range 8 |>.bind fun x =>
    Fin.range 8 |>.bind fun y =>
      pos.activePiece? x y |>.toList.bind fun piece =>
        pos.pieceMoves piece x y |>.map fun (x', y') => pos.move piece x y x' y'

def validMove (p₁ p₂ : Position) : Prop :=
  p₂ ∈ p₁.moves

def empty : Position :=
  { whiteToMove := true
    board := .replicate 8 (.replicate 8 none) }

example : Position.empty.moves = [] := rfl

/-- A king at a1 has 3 moves. -/
example : (Position.empty.set 0 0 .king).moves.length = 3 := rfl

def initial : Position :=
  Position.empty
    |>.set 0 0 .rook |>.set 1 0 .knight |>.set 2 0 .bishop |>.set 3 0 .queen
    |>.set 4 0 .king |>.set 5 0 .bishop |>.set 6 0 .knight |>.set 7 0 .rook
    |>.set 0 1 .pawn |>.set 1 1 .pawn |>.set 2 1 .pawn |>.set 3 1 .pawn
    |>.set 4 1 .pawn |>.set 5 1 .pawn |>.set 6 1 .pawn |>.set 7 1 .pawn
    |>.endTurn
    |>.set 0 6 .pawn |>.set 1 6 .pawn |>.set 2 6 .pawn |>.set 3 6 .pawn
    |>.set 4 6 .pawn |>.set 5 6 .pawn |>.set 6 6 .pawn |>.set 7 6 .pawn
    |>.set 0 7 .rook |>.set 1 7 .knight |>.set 2 7 .bishop |>.set 3 7 .queen
    |>.set 4 7 .king |>.set 5 7 .bishop |>.set 6 7 .knight |>.set 7 7 .rook
    |>.endTurn

/-- White has 20 possible moves from the initial position. -/
example : initial.moves.length = 20 := rfl

end Position

open Position

@[simp] theorem board_endTurn (p : Position) : (p.endTurn).board = p.board := by
  simp [endTurn]

@[simp] theorem countPieces_endTurn (p : Position) : (p.endTurn).countPieces = p.countPieces := by
  simp [countPieces, moves]

theorem countPieces_set (p : Position) (x y : Fin 8) (piece : Piece) :
    (p.set x y piece).countPieces = if p.occupied x y then p.countPieces else p.countPieces + 1 := by
  simp [countPieces]
  simp [Position.set]
  cases h : p.occupied x y
  · rw [Vec.countP_set]
    · simp [h, ← Nat.add_assoc]
      rw [Nat.sub_add_cancel]
      apply Vec.apply_getElem_le_sum_map_nat
  · simp
    rw [Vec.countP_set]
    simp [h]
    rw [Nat.sub_add_cancel, Nat.sub_add_cancel]
    · apply Vec.apply_getElem_le_sum_map_nat
    · simp
      refine ⟨y.1, y.2, by simpa using h⟩

theorem occupied_erase (p : Position) (x y : Fin 8) :
    (p.erase x y).occupied x' y' = if x' = x ∧ y' = y then false else p.occupied x' y' := by
  simp only [erase, occupied]
  split
  · rename_i x'' y'' hx hy
    simp only [toFin?_eq_some_iff] at hx hy
    subst hx hy
    simp only [Fin.getElem_fin, Vec.getElem_set]
    split <;> rename_i h₁
    · simp only [Vec.getElem_set]
      split <;> rename_i h₂
      · simp_all
      · simp_all [Ne.symm h₂]
    · simp_all [Ne.symm h₁]
  · simp_all

theorem countPieces_erase (p : Position) (x y : Fin 8) :
    (p.erase x y).countPieces = if p.occupied x y then p.countPieces - 1 else p.countPieces := by
  sorry
  -- rw [countPieces_eq]
  -- simp only [occupied_erase]
  -- simp
  -- conv =>
  --   lhs
  --   congr
  --   congr
  --   ext x'
  --   congr
  --   ext y'
  --   rw [Bool.and_comm]
  -- simp only [← List.countP_filter']
  -- simp
  -- sorry

theorem occupied_of_activePiece? {p : Position} {x y : Fin 8} {piece : Piece} :
    p.activePiece? x y = some piece → p.occupied x y := by
  simp only [activePiece?, Fin.getElem_fin, occupied, toFin?_cast]
  split <;> simp_all

theorem countPieces_pos_of_occupied {p : Position} {x y : Fin 8} (h : p.occupied x y) :
    0 < p.countPieces := by
  rw [countPieces_eq]
  calc
    0 < 1 := Nat.zero_lt_one
    1 ≤ _ := ?_
    _ ≤ _ := List.apply_getElem_le_sum_map_nat _ _ x (by simp)
  simp only [Fin.getElem_range, Fin.eta, List.one_le_countP_iff, Fin.mem_range, true_and]
  refine ⟨y, by simpa using h⟩

theorem countPieces_pos_of_activePiece? {p : Position} {x y : Fin 8} {piece : Piece}
    (h : p.activePiece? x y = some piece) : 0 < p.countPieces :=
  countPieces_pos_of_occupied (occupied_of_activePiece? h)

theorem countPieces_move (p : Position) {x y x' y' : Fin 8} (piece : Piece) (w : (x', y') ≠ (x, y)) (h : p.occupied x y) :
    (p.move piece x y x' y').countPieces = if p.occupied x' y' then p.countPieces - 1 else p.countPieces := by
  simp [move, countPieces_set, countPieces_erase]
  split
  · split
    · rfl
    · simp_all [occupied_erase]
  · split
    · simp_all [occupied_erase]
      omega
    · have := countPieces_pos_of_occupied h
      omega

theorem mem_ite [Membership α β] [Decidable p] {a : α} {x y : β} : (a ∈ if p then x else y) ↔ if p then a ∈ x else a ∈ y := by
  split <;> rfl

theorem ne_of_mem_pieceMoves
    {p : Position} {x y x' y' : Fin 8} (h : (x', y') ∈ p.pieceMoves piece x y) :
    (x', y') ≠ (x, y) := by
  simp only [pieceMoves] at h
  cases piece with
  | king | rook | bishop | queen | knight =>
    simp [kingMoves, kingDirs, knightMoves, knightDirs, rookMoves, rookDirs, bishopMoves,
      bishopDirs, queenMoves, queenDirs, unblockedMoves] at h
    simp
    omega
  | pawn =>
    simp [pawnMoves, mem_ite] at h
    obtain ⟨⟨a, b, h⟩, -⟩ := h
    simp
    split at h <;> omega

theorem countPieces_of_validMove (p₁ p₂ : Position) (h : p₁.validMove p₂) :
    p₂.countPieces = p₁.countPieces ∨ p₂.countPieces + 1 = p₁.countPieces := by
  simp only [validMove, moves, List.mem_bind, Option.mem_toList, Option.mem_def, List.mem_map,
    Prod.exists] at h
  obtain ⟨x, -, y, -, piece, h, x', y', m, rfl⟩ := h
  rw [countPieces_move p₁ piece (ne_of_mem_pieceMoves m) (occupied_of_activePiece? h)]
  have := countPieces_pos_of_activePiece? h
  split <;> omega

theorem getElem_getElem_board_move (p : Position) (x y x' y' : Fin 8) (w z : Nat) (hw : w < 8) (hz : z < 8) (piece : Piece) :
    (p.move piece x y x' y').board[w][z] =
      if w = x ∧ z = y then none else
        if w = x' ∧ z = y' then some (p.whiteToMove, piece) else
          p.board[w][z] := by
  simp [move]
  simp [Position.set, erase]
  sorry

def conservativeMove (p₁ p₂ : Position) : Prop := p₁.countPieces = p₂.countPieces

theorem countPieces_le_of_validMove {p₁ p₂ : Position} (h : p₁.validMove p₂) : p₂.countPieces ≤ p₁.countPieces := by
  have := countPieces_of_validMove p₁ p₂ h
  omega

/-- If a pawn moves without taking, it does not change file. -/
theorem pawn_file_of_conservativeMove (h : p₁.activePiece? x y = some Piece.pawn)
    (m : (x', y') ∈ p₁.pieceMoves Piece.pawn ↑x ↑y) (h₂ : conservativeMove p₁ (p₁.move Piece.pawn x y x' y')) :
    x' = x := by
  simp [pieceMoves, pawnMoves] at m
  split at m <;> rename_i player
  · obtain ⟨⟨a, b, h⟩, -⟩ := m
    split at h
    · simp at h
    · simp at h
      obtain ⟨h|h|h|h, hx, hx⟩ := h
      · omega
      · omega
      · sorry
      · sorry

  · sorry

def leadingWhitePawn (p : Position) (x : Fin 8) : Option (Fin 8) :=
  (Fin.range 8).reverse |>.find? (fun y => p.board[x][y] = some (true, .pawn))

theorem leadingWhitePawn_of_conservativeMove {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (z : Fin 8) :
    match leadingWhitePawn p₁ z with
    | none => leadingWhitePawn p₂ z = none
    | some y => leadingWhitePawn p₂ z = some y ∨ y < 7 ∧ leadingWhitePawn p₂ z = some (y + 1) := by
  simp only [validMove, moves, List.mem_bind, Option.mem_toList, Option.mem_def, List.mem_map,
    Prod.exists] at h₁
  obtain ⟨x, -, y, -, piece, h, x', y', m, rfl⟩ := h₁
  split <;> rename_i w
  · simp [leadingWhitePawn] at w ⊢
    by_cases r : piece = .pawn
    · subst r
      have : x' = x := pawn_file_of_conservativeMove h m h₂
      subst x'
      rintro w
      rw [getElem_getElem_board_move]
      split
      · simp
      · split
        · simp_all
          sorry
        · sorry
    · sorry
  · sorry

def leadingBlackPawn (p : Position) (x : Fin 8) : Option (Fin 8) :=
  (Fin.range 8).find? (fun y => p.board[x][y] = some (false, .pawn))

theorem leadingBlackPawn_of_conservativeMove {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (z : Fin 8) :
    match leadingBlackPawn p₁ z with
    | none => leadingBlackPawn p₂ z = none
    | some y => leadingBlackPawn p₂ z = some y ∨ 0 < y ∧ leadingBlackPawn p₂ z = some (y - 1) :=
  sorry

theorem leadingWhitePawn_of_conservativeMove_of_blackToMove
    {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (w : p₁.whiteToMove = false) (z : Fin 8) :
    leadingWhitePawn p₂ z = leadingWhitePawn p₁ z :=
  sorry

theorem leadingBlackPawn_of_conservativeMove_of_whiteToMove
    {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (w : p₁.whiteToMove = true) (z : Fin 8) :
    leadingBlackPawn p₂ z = leadingBlackPawn p₁ z :=
  sorry

def pawnsBlocked (p : Position) (x : Fin 8) : Prop :=
  ∃ y, leadingWhitePawn p x = some y ∧ leadingBlackPawn p x = some (y + 1)

/-- You shall not pass! -/
theorem leadingWhitePawn_of_conservativeMove_of_pawnsBlocked
    {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (x : Fin 8)
    (w : pawnsBlocked p₁ x) :
    leadingWhitePawn p₂ x = leadingWhitePawn p₁ x :=
  sorry

theorem leadingBlackPawn_of_conservativeMove_of_pawnsBlocked
    {p₁ p₂ : Position} (h₁ : validMove p₁ p₂) (h₂ : conservativeMove p₁ p₂) (x : Fin 8)
    (w : pawnsBlocked p₁ x) :
    leadingBlackPawn p₂ x = leadingBlackPawn p₁ x :=
  sorry

def opposedPawns (p : Position) (x : Fin 8) : Bool :=
  match leadingWhitePawn p x, leadingBlackPawn p x with
  | none, none => false
  | some _, none => false
  | none, some _ => false
  | some y, some z => y < z

example : opposedPawns Position.initial 0 = true := rfl

theorem opposedPawns_of_conservativeMove {p₁ p₂ : Position} (valid : validMove p₁ p₂) (conservative : conservativeMove p₁ p₂) (x : Fin 8) :
    opposedPawns p₁ x = opposedPawns p₂ x := by
  unfold opposedPawns
  by_cases toMove : p₁.whiteToMove
  · have white := leadingWhitePawn_of_conservativeMove valid conservative x
    have black := leadingBlackPawn_of_conservativeMove_of_whiteToMove valid conservative toMove x
    revert white
    match h₁ : leadingWhitePawn p₁ x with
    | none => intro white; simp_all
    | some y =>
      intro white
      simp at white
      rcases white with (white | white) <;> simp [white, black]
      match h₂ : leadingBlackPawn p₁ x with
      | none => simp
      | some y' =>
        by_cases h₃ : pawnsBlocked p₁ x
        · replace h₃ := leadingWhitePawn_of_conservativeMove_of_pawnsBlocked valid conservative x h₃
          simp_all
        · simp [pawnsBlocked] at h₃
          specialize h₃ _ h₁
          simp_all
          omega
  · have white := leadingWhitePawn_of_conservativeMove_of_blackToMove valid conservative (by simpa using toMove) x
    have black := leadingBlackPawn_of_conservativeMove valid conservative x
    revert black
    match h₁ : leadingBlackPawn p₁ x with
    | none => intro black; simp_all
    | some y =>
      intro black
      simp at black
      rcases black with (black | black) <;> simp [black, white]
      match h₂ : leadingWhitePawn p₁ x with
      | none => simp
      | some y' =>
        by_cases h₃ : pawnsBlocked p₁ x
        · replace h₃ := leadingBlackPawn_of_conservativeMove_of_pawnsBlocked valid conservative x h₃
          simp [h₁, black.2] at h₃
        · simp [pawnsBlocked] at h₃
          specialize h₃ _ h₂
          simp_all
          omega

structure Game where
  history : List Position
  valid : List.Chain validMove Position.initial history

theorem chain_conversativeMove_of_countPieces (g : Game)
    (h : ∀ p ∈ g.history.getLast?, p.countPieces = Position.initial.countPieces) :
    List.Chain conservativeMove Position.initial g.history :=
  sorry

def wrongColorPawns : Position :=
  Position.empty
    |>.set 0 0 .rook |>.set 1 0 .knight |>.set 2 0 .bishop |>.set 3 0 .queen
    |>.set 4 0 .king |>.set 5 0 .bishop |>.set 6 0 .knight |>.set 7 0 .rook
    |>.set 0 6 .pawn |>.set 1 6 .pawn |>.set 2 6 .pawn |>.set 3 6 .pawn
    |>.set 4 6 .pawn |>.set 5 6 .pawn |>.set 6 6 .pawn |>.set 7 6 .pawn
    |>.endTurn
    |>.set 0 1 .pawn |>.set 1 1 .pawn |>.set 2 1 .pawn |>.set 3 1 .pawn
    |>.set 4 1 .pawn |>.set 5 1 .pawn |>.set 6 1 .pawn |>.set 7 1 .pawn
    |>.set 0 7 .rook |>.set 1 7 .knight |>.set 2 7 .bishop |>.set 3 7 .queen
    |>.set 4 7 .king |>.set 5 7 .bishop |>.set 6 7 .knight |>.set 7 7 .rook
    |>.endTurn

example : opposedPawns wrongColorPawns 0 = false := rfl

theorem countPieces_initial : Position.initial.countPieces = 32 := sorry
theorem countPieces_wrongColorPawns : wrongColorPawns.countPieces = 32 := sorry

open List

instance {f : α → β} : IsTrans α (fun x y => f x = f y) where
  trans := fun _ _ _ => Eq.trans

theorem _root_.List.Pairwise.head_getLast {l : List α} (w : 2 ≤ l.length) (h : List.Pairwise r l) :
    r (l.head (by rintro rfl; simp at w)) (getLast l (by rintro rfl; simp at w)) :=
  match l with
  | a :: b :: l => rel_of_pairwise_cons h (getLast_mem (by simp))

theorem _root_.List.Pairwise.cons_getLast {l : List α} (_ : l ≠ []) (h : List.Pairwise r (a :: l)) :
    r a ((a :: l).getLast (by simp)) :=
  match l with
  | b :: l => rel_of_pairwise_cons h (getLast_mem (by simp))

theorem _root_.List.Chain.and {l : List α} {r s : α → α → Prop} (h₁ : List.Chain r a l) (h₂ : List.Chain s a l) :
    List.Chain (fun x y => r x y ∧ s x y) a l :=
  sorry

theorem wrongColorPawns_unreachable : ¬ ∃ (g : Game), g.history.getLast? = some wrongColorPawns := by
  rintro ⟨g, h⟩
  have := chain_conversativeMove_of_countPieces g
  simp [h] at this
  specialize this (countPieces_wrongColorPawns.trans countPieces_initial.symm)
  have := g.valid.and this
  have := this.imp (fun p₁ p₂ ⟨v, c⟩ => opposedPawns_of_conservativeMove v c 0)
  have := this.pairwise
  have := this.cons_getLast
  rw [List.getLast?_eq_some_iff] at h
  obtain ⟨ys, h⟩ := h
  simp [h] at this
  cases this
