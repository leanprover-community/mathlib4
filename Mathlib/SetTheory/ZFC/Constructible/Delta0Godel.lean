/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0
public import Mathlib.SetTheory.ZFC.Constructible.Godel
public import Mathlib.Tactic.FinCases

/-!
# Bounded formulas for Gödel operations

This file supplies reusable `Δ₀` formulas for the finite set encodings used
by the Jensen--Devlin Gödel operations.  All coordinate conventions are
intrinsically checked by the `Fin` indices.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Delta0Formula

/-- Ambient membership on Mathlib's internal ZFC sets. -/
abbrev ZFMem : ZFSet.{u} → ZFSet.{u} → Prop :=
  fun x y => x ∈ y

/-- Formula saying that coordinate `left` is a subset of coordinate `right`. -/
def subsetAt {n : Nat} (left right : Fin n) : Delta0Formula n :=
  .boundedAll left
    (.mem (Fin.last n) right.castSucc)

@[simp]
theorem satisfies_subsetAt {n : Nat} (left right : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (subsetAt left right) s ↔ s left ⊆ s right := by
  simp only [subsetAt, satisfies_boundedAll, Satisfies, snoc_last,
    snoc_castSucc]
  change (∀ z : ZFSet.{u}, z ∈ s left → z ∈ s right) ↔ s left ⊆ s right
  rfl

/-- Formula saying that coordinate `set` is the singleton of coordinate `x`. -/
def singletonEqAt {n : Nat} (set x : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.boundedAll set
      (.eq (Fin.last n) x.castSucc))

@[simp]
theorem satisfies_singletonEqAt {n : Nat} (set x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (singletonEqAt set x) s ↔
      s set = ({s x} : ZFSet.{u}) := by
  simp only [singletonEqAt, Satisfies, satisfies_boundedAll, snoc_last,
    snoc_castSucc]
  change
    (s x ∈ s set ∧ ∀ z : ZFSet.{u}, z ∈ s set → z = s x) ↔
      s set = ({s x} : ZFSet.{u})
  constructor
  · rintro ⟨hx, hall⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact ZFSet.mem_singleton.mpr (hall z hz)
    · intro hz
      have hzx : z = s x := ZFSet.mem_singleton.mp hz
      subst z
      exact hx
  · intro h
    rw [h]
    simp

/-- Formula saying that coordinate `set` is the unordered pair `{x,y}`. -/
def unorderedPairEqAt {n : Nat} (set x y : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.conj (.mem y set)
      (.boundedAll set
        (.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))

@[simp]
theorem satisfies_unorderedPairEqAt {n : Nat} (set x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (unorderedPairEqAt set x y) s ↔
      s set = ({s x, s y} : ZFSet.{u}) := by
  simp only [unorderedPairEqAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, snoc_last, snoc_castSucc]
  change
    (s x ∈ s set ∧ s y ∈ s set ∧
      ∀ z : ZFSet.{u}, z ∈ s set → z = s x ∨ z = s y) ↔
      s set = ({s x, s y} : ZFSet.{u})
  constructor
  · rintro ⟨hx, hy, hall⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_pair]
    constructor
    · exact hall z
    · rintro (rfl | rfl)
      · exact hx
      · exact hy
  · intro h
    rw [h]
    simp

/-- Formula saying that coordinate `pair` is `⟨x,y⟩`. -/
def kuratowskiPairEqAt {n : Nat} (pair x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedEx pair
      (singletonEqAt (Fin.last n) x.castSucc))
    (.conj
      (.boundedEx pair
        (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))
      (.boundedAll pair
        (.disj
          (singletonEqAt (Fin.last n) x.castSucc)
          (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))))

@[simp]
theorem satisfies_kuratowskiPairEqAt {n : Nat} (pair x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (kuratowskiPairEqAt pair x y) s ↔
      s pair = ZFSet.pair (s x) (s y) := by
  simp only [kuratowskiPairEqAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, satisfies_singletonEqAt, satisfies_unorderedPairEqAt]
  simp only [snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨⟨sx, hsxPair, hsx⟩, ⟨⟨pxy, hpxyPair, hpxy⟩, hall⟩⟩
    apply ZFSet.ext
    intro z
    simp only [ZFSet.pair, ZFSet.mem_pair]
    constructor
    · intro hz
      rcases hall z hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (rfl | rfl)
      · rw [← hsx]
        exact hsxPair
      · rw [← hpxy]
        exact hpxyPair
  · intro h
    rw [h]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨{s x}, ?_, rfl⟩
      simp [ZFSet.pair]
    · refine ⟨{s x, s y}, ?_, rfl⟩
      simp [ZFSet.pair]
    · intro z hz
      simpa [ZFSet.pair] using hz

/-- Formula saying that coordinate `out` is the right-associated triple `⟨x,y,z⟩`. -/
def tripleEqAt {n : Nat} (out x y z : Fin n) : Delta0Formula n :=
  .boundedEx out
    (.boundedEx (Fin.last n)
      (.conj
        (kuratowskiPairEqAt (Fin.last (n + 1))
          y.castSucc.castSucc z.castSucc.castSucc)
        (kuratowskiPairEqAt out.castSucc.castSucc x.castSucc.castSucc
          (Fin.last (n + 1)))))

@[simp]
theorem satisfies_tripleEqAt {n : Nat} (out x y z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (tripleEqAt out x y z) s ↔
      s out = Godel.triple (s x) (s y) (s z) := by
  simp only [tripleEqAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨container, hcontainer, inner, hinner, hpair, hout⟩
    rw [hout, hpair]
    rfl
  · intro h
    let inner := ZFSet.pair (s y) (s z)
    rw [h]
    refine ⟨{s x, inner}, ?_, inner, ?_, rfl, rfl⟩
    · simp [Godel.triple, ZFSet.pair, inner]
    · simp [inner]

/--
Bound five witnesses `p ∈ relation`, `leftBox ∈ p`, `left ∈ leftBox`,
`rightBox ∈ p`, and `right ∈ rightBox`.  This supplies bounded
candidates for the two components of a Kuratowski pair belonging to a
relation.
-/
def withBoundedPairComponents {n : Nat} (relation : Fin n)
    (body : Delta0Formula (n + 5)) : Delta0Formula n :=
  .boundedEx relation
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (.boundedEx (Fin.last n).castSucc.castSucc
          (.boundedEx (Fin.last (n + 3)) body))))

@[simp]
theorem satisfies_withBoundedPairComponents {A : Type u}
    (E : A → A → Prop) {n : Nat} (relation : Fin n)
    (body : Delta0Formula (n + 5)) (s : Tuple A n) :
    Satisfies E (withBoundedPairComponents relation body) s ↔
      ∃ p : A, E p (s relation) ∧
        ∃ leftBox : A, E leftBox p ∧
          ∃ left : A, E left leftBox ∧
            ∃ rightBox : A, E rightBox p ∧
              ∃ right : A, E right rightBox ∧
                Satisfies E body
                  (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
                    rightBox) right) := by
  simp only [withBoundedPairComponents, Satisfies, snoc_last,
    snoc_castSucc]

/--
Formula saying `q = {w | ⟨w,z⟩ ∈ x}`.  The reverse containment ranges over
`p ∈ x`, `box ∈ p`, and `w ∈ box`; these bounds are sufficient because
`{w} ∈ ⟨w,z⟩`.
-/
def fiberEqAt {n : Nat} (q x z : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll q
      (.boundedEx x.castSucc
        (kuratowskiPairEqAt
          (Fin.last (n + 1))
          (Fin.last n).castSucc
          z.castSucc.castSucc)))
    (.boundedAll x
      (.boundedAll (Fin.last n)
        (.boundedAll (Fin.last (n + 1))
          (.imp
            (kuratowskiPairEqAt
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2))
              z.castSucc.castSucc.castSucc)
            (.mem (Fin.last (n + 2)) q.castSucc.castSucc.castSucc)))))

@[simp]
theorem satisfies_fiberEqAt {n : Nat} (q x z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberEqAt q x z) s ↔
      s q = Godel.fiber (s x) (s z) := by
  simp only [fiberEqAt, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_kuratowskiPairEqAt, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro w
    rw [Godel.mem_fiber_iff]
    constructor
    · intro hw
      rcases hsub w hw with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
    · intro hp
      have hsingle : ({w} : ZFSet.{u}) ∈ ZFSet.pair w (s z) := by
        simp [ZFSet.pair]
      exact hsup (ZFSet.pair w (s z)) hp ({w} : ZFSet.{u}) hsingle w
        (by simp) rfl
  · intro h
    constructor
    · intro w hw
      refine ⟨ZFSet.pair w (s z), ?_, rfl⟩
      rw [h] at hw
      simpa using hw
    · intro p hp box hbox w hw hpair
      rw [h]
      change w ∈ Godel.fiber (s x) (s z)
      rw [Godel.mem_fiber_iff]
      simpa [← hpair] using hp

/-- Formula saying that `q` lies in the right-domain operation `F₆(x,-)`. -/
def f6MemAt {n : Nat} (q x : Fin n) : Delta0Formula n :=
  .boundedEx x
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (kuratowskiPairEqAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 2))
          q.castSucc.castSucc.castSucc)))

@[simp]
theorem satisfies_f6MemAt {n : Nat} (q x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f6MemAt q x) s ↔
      ∃ w : ZFSet.{u}, ZFSet.pair w (s q) ∈ s x := by
  simp only [f6MemAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨p, hp, box, hbox, w, hw, hpair⟩
    exact ⟨w, by simpa [← hpair] using hp⟩
  · rintro ⟨w, hw⟩
    refine ⟨ZFSet.pair w (s q), hw, ({w} : ZFSet.{u}), ?_, w, by simp, rfl⟩
    simp [ZFSet.pair]

theorem satisfies_f6MemAt_iff_mem {n : Nat} (q x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f6MemAt q x) s ↔
      s q ∈ Godel.F6 (s x) (s y) := by
  rw [satisfies_f6MemAt, Godel.mem_F6_iff]

/-- Formula saying that `q` is a fiber of `x` at some index in `y`. -/
def f8MemAt {n : Nat} (q x y : Fin n) : Delta0Formula n :=
  .boundedEx y
    (fiberEqAt q.castSucc x.castSucc (Fin.last n))

@[simp]
theorem satisfies_f8MemAt {n : Nat} (q x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f8MemAt q x y) s ↔
      s q ∈ Godel.F8 (s x) (s y) := by
  simp only [f8MemAt, Satisfies, satisfies_fiberEqAt,
    snoc_last, snoc_castSucc]
  rw [Godel.mem_F8_iff]

end Constructible.Delta0Formula

namespace Constructible.Godel

open Constructible.Delta0Formula

/-!
The fixed assignment convention for the following formulas is `![q,x,y]`:
coordinate `0` is the candidate member and coordinates `1,2` are the two
arguments of the Gödel operation.
-/

/-- `q ∈ F₀(x,y)`. -/
def memF0Formula : Delta0Formula 3 :=
  .disj (.eq 0 1) (.eq 0 2)

@[simp]
theorem satisfies_memF0Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF0Formula ![q, x, y] ↔ q ∈ F0 x y := by
  simp [memF0Formula]

/-- `q ∈ F₁(x,y)`. -/
def memF1Formula : Delta0Formula 3 :=
  .conj (.mem 0 1) (.neg (.mem 0 2))

@[simp]
theorem satisfies_memF1Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF1Formula ![q, x, y] ↔ q ∈ F1 x y := by
  simp [memF1Formula]

/-- `q ∈ F₂(x,y) = x × y`. -/
def memF2Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 2
      (kuratowskiPairEqAt 0 3 4))

@[simp]
theorem satisfies_memF2Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF2Formula ![q, x, y] ↔ q ∈ F2 x y := by
  rw [mem_F2_iff]
  simp only [memF2Formula, Satisfies, satisfies_kuratowskiPairEqAt]
  constructor
  · rintro ⟨a, hax, b, hby, hq⟩
    refine ⟨a, hax, b, ?_, ?_⟩
    · change b ∈ y at hby
      exact hby
    · change q = ZFSet.pair a b at hq
      exact hq
  · rintro ⟨a, hax, b, hby, hq⟩
    refine ⟨a, hax, b, ?_, ?_⟩
    · change b ∈ y
      exact hby
    · change q = ZFSet.pair a b
      exact hq

/-- `q ∈ F₃(x,y)`. -/
def memF3Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 3 8)))

set_option maxHeartbeats 400000 in
-- Normalizing the six appended bounded witnesses requires extra kernel reduction.
@[simp]
theorem satisfies_memF3Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF3Formula ![q, x, y] ↔ q ∈ F3 x y := by
  rw [mem_F3_iff]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      Satisfies ZFMem
        (withBoundedPairComponents (2 : Fin 4)
          (.conj
            (kuratowskiPairEqAt 4 6 8)
            (tripleEqAt 0 6 3 8)))
        (snoc ![q, x, y] z)) ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u z v
  simp only [satisfies_withBoundedPairComponents, Satisfies,
    satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      ∃ p : ZFSet.{u}, p ∈ y ∧
        ∃ leftBox : ZFSet.{u}, leftBox ∈ p ∧
          ∃ u : ZFSet.{u}, u ∈ leftBox ∧
            ∃ rightBox : ZFSet.{u}, rightBox ∈ p ∧
              ∃ v : ZFSet.{u}, v ∈ rightBox ∧
                (p = ZFSet.pair u v ∧ q = triple u z v)) ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u z v
  constructor
  · rintro ⟨z, hzx, p, hpy, leftBox, hleftBox, u, hu,
        rightBox, hrightBox, v, hv, hp, hq⟩
    refine ⟨u, z, v, hzx, ?_, hq⟩
    rw [← hp]
    exact hpy
  · rintro ⟨u, z, v, hzx, huv, hq⟩
    let p := ZFSet.pair u v
    refine ⟨z, hzx, p, ?_, {u}, ?_, u, ?_, {u, v}, ?_, v, ?_, rfl, hq⟩
    · simpa [p] using huv
    · simp [p, ZFSet.pair]
    · simp
    · simp [p, ZFSet.pair]
    · simp

/-- `q ∈ F₄(x,y)`. -/
def memF4Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 8 3)))

set_option maxHeartbeats 400000 in
-- Normalizing the six appended bounded witnesses requires extra kernel reduction.
@[simp]
theorem satisfies_memF4Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF4Formula ![q, x, y] ↔ q ∈ F4 x y := by
  rw [mem_F4_iff]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      Satisfies ZFMem
        (withBoundedPairComponents (2 : Fin 4)
          (.conj
            (kuratowskiPairEqAt 4 6 8)
            (tripleEqAt 0 6 8 3)))
        (snoc ![q, x, y] z)) ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u v z
  simp only [satisfies_withBoundedPairComponents, Satisfies,
    satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      ∃ p : ZFSet.{u}, p ∈ y ∧
        ∃ leftBox : ZFSet.{u}, leftBox ∈ p ∧
          ∃ u : ZFSet.{u}, u ∈ leftBox ∧
            ∃ rightBox : ZFSet.{u}, rightBox ∈ p ∧
              ∃ v : ZFSet.{u}, v ∈ rightBox ∧
                (p = ZFSet.pair u v ∧ q = triple u v z)) ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u v z
  constructor
  · rintro ⟨z, hzx, p, hpy, leftBox, hleftBox, u, hu,
        rightBox, hrightBox, v, hv, hp, hq⟩
    refine ⟨u, v, z, hzx, ?_, hq⟩
    rw [← hp]
    exact hpy
  · rintro ⟨u, v, z, hzx, huv, hq⟩
    let p := ZFSet.pair u v
    refine ⟨z, hzx, p, ?_, {u}, ?_, u, ?_, {u, v}, ?_, v, ?_, rfl, hq⟩
    · simpa [p] using huv
    · simp [p, ZFSet.pair]
    · simp
    · simp [p, ZFSet.pair]
    · simp

/-- `q ∈ F₅(x,y) = ⋃₀ x`; the second argument is unused. -/
def memF5Formula : Delta0Formula 3 :=
  .boundedEx 1 (.mem 0 3)

@[simp]
theorem satisfies_memF5Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF5Formula ![q, x, y] ↔ q ∈ F5 x y := by
  rw [mem_F5_iff]
  simp only [memF5Formula, Satisfies]
  constructor
  · rintro ⟨w, hwx, hqw⟩
    refine ⟨w, hwx, ?_⟩
    change q ∈ w at hqw
    exact hqw
  · rintro ⟨w, hwx, hqw⟩
    refine ⟨w, hwx, ?_⟩
    change q ∈ w
    exact hqw

/-- `q ∈ F₆(x,y)`; the second argument is unused. -/
def memF6Formula : Delta0Formula 3 :=
  f6MemAt 0 1

@[simp]
theorem satisfies_memF6Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF6Formula ![q, x, y] ↔ q ∈ F6 x y := by
  simp [memF6Formula]

/-- `q ∈ F₇(x,y)`; the second argument is unused. -/
def memF7Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 1
      (.conj (kuratowskiPairEqAt 0 3 4) (.mem 3 4)))

@[simp]
theorem satisfies_memF7Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF7Formula ![q, x, y] ↔ q ∈ F7 x y := by
  rw [mem_F7_iff]
  simp only [memF7Formula, Satisfies]
  constructor
  · rintro ⟨z, hzx, w, hwx, hpair, hzw⟩
    refine ⟨z, hzx, w, ?_, ?_, hzw⟩
    · change w ∈ x at hwx
      exact hwx
    · have hp := (satisfies_kuratowskiPairEqAt (0 : Fin 5)
          (3 : Fin 5) (4 : Fin 5) (snoc (snoc ![q, x, y] z) w)).mp hpair
      change q = ZFSet.pair z w at hp
      exact hp
  · rintro ⟨z, hzx, w, hwx, hq, hzw⟩
    refine ⟨z, hzx, w, ?_, ?_, ?_⟩
    · change w ∈ x
      exact hwx
    · apply (satisfies_kuratowskiPairEqAt (0 : Fin 5)
          (3 : Fin 5) (4 : Fin 5) (snoc (snoc ![q, x, y] z) w)).mpr
      change q = ZFSet.pair z w
      exact hq
    · change z ∈ w
      exact hzw

/-- `q ∈ F₈(x,y)`. -/
def memF8Formula : Delta0Formula 3 :=
  f8MemAt 0 1 2

@[simp]
theorem satisfies_memF8Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF8Formula ![q, x, y] ↔ q ∈ F8 x y := by
  simp [memF8Formula]

/-- Uniform `Δ₀` membership formula for the nine Gödel operations. -/
def memOpFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => memF0Formula
  | 1 => memF1Formula
  | 2 => memF2Formula
  | 3 => memF3Formula
  | 4 => memF4Formula
  | 5 => memF5Formula
  | 6 => memF6Formula
  | 7 => memF7Formula
  | 8 => memF8Formula
  | _ => .neg (.eq 0 0)

/-- The uniform formula defines membership in `op i x y`. -/
@[simp]
theorem satisfies_memOpFormula (i : Fin 9) (q x y : ZFSet.{u}) :
    Satisfies ZFMem (memOpFormula i) ![q, x, y] ↔
      q ∈ op i x y := by
  fin_cases i <;> simp [memOpFormula, op]

/-- The same uniform correctness theorem in the unrestricted `FOFormula` syntax. -/
theorem satisfies_toFO_memOpFormula (i : Fin 9) (q x y : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem (memOpFormula i).toFO ![q, x, y] ↔
      q ∈ op i x y := by
  rw [Delta0Formula.satisfies_toFO, satisfies_memOpFormula]

/--
The same operation formula with the section convention used by `DefZF`:
parameters `x,y` come first and the candidate member `q` is last.
-/
def memOpSectionFormula (i : Fin 9) : Delta0Formula 3 :=
  Delta0Formula.rename ![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)]
    (memOpFormula i)

@[simp]
theorem satisfies_memOpSectionFormula (i : Fin 9) (x y q : ZFSet.{u}) :
    Satisfies ZFMem (memOpSectionFormula i) ![x, y, q] ↔
      q ∈ op i x y := by
  rw [memOpSectionFormula, Delta0Formula.satisfies_rename]
  have hassign :
      (fun j => ![x, y, q] (![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)] j)) =
        ![q, x, y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_memOpFormula i q x y

/--
If the operands lie in a transitive carrier and the operation value is a
subset of that carrier, its uniform `Δ₀` membership formula places the value
in `DefZF`.
-/
theorem op_mem_DefZF_of_subset {U x y : ZFSet.{u}} {i : Fin 9}
    (hU : U.IsTransitive) (hx : x ∈ U) (hy : y ∈ U)
    (hsub : op i x y ⊆ U) :
    op i x y ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier U := ⟨x, hx⟩
  let sy : ZFCarrier U := ⟨y, hy⟩
  let params : Tuple (ZFCarrier U) 2 := ![sx, sy]
  refine ⟨hsub, 2, params, (memOpSectionFormula i).toFO, ?_⟩
  intro q
  rw [Delta0Formula.satisfies_toFO]
  have habs := Delta0Formula.satisfies_absolute hU
    (memOpSectionFormula i) (snoc params q)
  have hamb :
      Satisfies ZFMem (memOpSectionFormula i)
          (Delta0Formula.val (snoc params q)) ↔
        q.1 ∈ op i x y := by
    have hval :
        Delta0Formula.val (snoc params q) = ![x, y, q.1] := by
      funext j
      fin_cases j <;> rfl
    rw [hval]
    exact satisfies_memOpSectionFormula i x y q.1
  exact hamb.symm.trans habs.symm

/-- The same hypotheses also put the operation value in the Gödel candidate. -/
theorem op_mem_godelDef_of_subset {U x y : ZFSet.{u}} {i : Fin 9}
    (hx : x ∈ U) (hy : y ∈ U) (hsub : op i x y ⊆ U) :
    op i x y ∈ godelDef U := by
  apply mem_godelDef_iff.mpr
  refine ⟨hsub, ?_⟩
  exact op_mem_rudimentaryClosure
    (subset_rudimentaryClosure U hx) (subset_rudimentaryClosure U hy)

end Constructible.Godel
