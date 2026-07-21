/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Simple

/-!
# Formula relations as rudimentary sets

This module compiles every internally scoped first-order formula over a
transitive `ZFSet` into a rudimentary relation set.  Taking a parameter fiber
then proves the formula-to-Gödel inclusion for `Def(U)`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

/-- Reverse-snoc coding of a nonempty tuple by right-associated ordered pairs. -/
def positiveTupleCode : (n : Nat) → Tuple ZFSet.{u} (n + 1) → ZFSet.{u}
  | 0, s => s 0
  | n + 1, s =>
      ZFSet.pair (s (Fin.last (n + 1)))
        (positiveTupleCode n (fun i => s i.castSucc))

/-- The set of codes of nonempty tuples over `U`. -/
noncomputable def positiveTupleSpace (U : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => U
  | n + 1 => F2 U (positiveTupleSpace U n)

@[simp]
theorem positiveTupleCode_snoc {n : Nat}
    (s : Tuple ZFSet.{u} (n + 1)) (x : ZFSet.{u}) :
    positiveTupleCode (n + 1) (snoc s x) =
      ZFSet.pair x (positiveTupleCode n s) := by
  simp [positiveTupleCode]

@[simp]
theorem mem_positiveTupleSpace_iff {U : ZFSet.{u}} {n : Nat}
    (s : Tuple ZFSet.{u} (n + 1)) :
    positiveTupleCode n s ∈ positiveTupleSpace U n ↔
      ∀ i, s i ∈ U := by
  induction n with
  | zero =>
      simp only [positiveTupleCode, positiveTupleSpace]
      constructor
      · intro h i
        fin_cases i
        exact h
      · intro h
        exact h 0
  | succ n ih =>
      rw [positiveTupleSpace, positiveTupleCode]
      rw [F2, ZFSet.pair_mem_prod, ih]
      constructor
      · rintro ⟨hlast, hprefix⟩ i
        refine Fin.lastCases hlast (fun j => hprefix j) i
      · intro h
        exact ⟨h (Fin.last (n + 1)), fun j => h j.castSucc⟩

theorem F0_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F0 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (0 : Fin 9)) hx hy)

theorem F1_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F1 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (1 : Fin 9)) hx hy)

theorem F2_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F2 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (2 : Fin 9)) hx hy)

theorem F3_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F3 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (3 : Fin 9)) hx hy)

theorem F4_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F4 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (4 : Fin 9)) hx hy)

theorem F5_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F5 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (5 : Fin 9)) hx hy)

theorem F6_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F6 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (6 : Fin 9)) hx hy)

theorem F7_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F7 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (7 : Fin 9)) hx hy)

theorem F8_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    F8 x y ∈ rudimentaryClosure U := by
  simpa [op] using
    (op_mem_rudimentaryClosure (i := (8 : Fin 9)) hx hy)

theorem positiveTupleSpace_mem_rudimentaryClosure (U : ZFSet.{u}) :
    ∀ n, positiveTupleSpace U n ∈ rudimentaryClosure U := by
  intro n
  induction n with
  | zero => exact self_mem_rudimentaryClosure U
  | succ n ih =>
      exact F2_mem_rudimentaryClosure
        (self_mem_rudimentaryClosure U) ih

/-- Kuratowski ordered pairs stay inside the rudimentary closure. -/
theorem orderedPair_mem_rudimentaryClosure {U x y : ZFSet.{u}}
    (hx : x ∈ rudimentaryClosure U) (hy : y ∈ rudimentaryClosure U) :
    ZFSet.pair x y ∈ rudimentaryClosure U := by
  have hs : F0 x x ∈ rudimentaryClosure U :=
    F0_mem_rudimentaryClosure hx hx
  have hp : F0 x y ∈ rudimentaryClosure U :=
    F0_mem_rudimentaryClosure hx hy
  have h := F0_mem_rudimentaryClosure hs hp
  simpa [F0, ZFSet.pair] using h

/-- Every concrete tuple of members of `U` has its code in the closure. -/
theorem positiveTupleCode_mem_rudimentaryClosure {U : ZFSet.{u}} :
    ∀ {n : Nat} (s : Tuple (ZFCarrier U) (n + 1)),
      positiveTupleCode n (Constructible.Delta0Formula.val s) ∈
        rudimentaryClosure U := by
  intro n
  induction n with
  | zero =>
      intro s
      exact subset_rudimentaryClosure U (s 0).2
  | succ n ih =>
      intro s
      let pref : Tuple (ZFCarrier U) (n + 1) := fun i => s i.castSucc
      let x : ZFCarrier U := s (Fin.last (n + 1))
      have hs : snoc pref x = s := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [x]
        · simp [pref]
      rw [← hs]
      simp only [Constructible.Delta0Formula.val_snoc,
        positiveTupleCode_snoc]
      exact orderedPair_mem_rudimentaryClosure
        (subset_rudimentaryClosure U x.2) (ih pref)

/-- Taking the unique fiber indexed by a singleton is a rudimentary operation. -/
theorem fiber_mem_rudimentaryClosure {U r p : ZFSet.{u}}
    (hr : r ∈ rudimentaryClosure U) (hp : p ∈ rudimentaryClosure U) :
    fiber r p ∈ rudimentaryClosure U := by
  have hsingle : F0 p p ∈ rudimentaryClosure U :=
    F0_mem_rudimentaryClosure hp hp
  have hfibers : F8 r (F0 p p) ∈ rudimentaryClosure U :=
    F8_mem_rudimentaryClosure hr hsingle
  have hunion : F5 (F8 r (F0 p p)) U ∈ rudimentaryClosure U :=
    F5_mem_rudimentaryClosure hfibers (self_mem_rudimentaryClosure U)
  have heq : F5 (F8 r (F0 p p)) U = fiber r p := by
    apply ZFSet.ext
    intro q
    simp [F0]
  rwa [heq] at hunion

/-- A rudimentary set coding a relation on nonempty tuples over `U`. -/
structure RelationRep (U : ZFSet.{u}) (n : Nat)
    (P : Tuple (ZFCarrier U) (n + 1) → Prop) where
  /-- The set coding the represented relation. -/
  set : ZFSet.{u}
  set_mem : set ∈ rudimentaryClosure U
  subset_space : set ⊆ positiveTupleSpace U n
  correct : ∀ s : Tuple (ZFCarrier U) (n + 1),
    positiveTupleCode n (Constructible.Delta0Formula.val s) ∈ set ↔ P s

namespace RelationRep

/-- Every tuple is its prefix followed by its last coordinate. -/
theorem tuple_snoc_eta {A : Type u} {n : Nat} (s : Tuple A (n + 1)) :
    snoc (fun i => s i.castSucc) (s (Fin.last n)) = s := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Change only the external predicate characterized by a representation. -/
def congr {U : ZFSet.{u}} {n : Nat}
    {P Q : Tuple (ZFCarrier U) (n + 1) → Prop}
    (r : RelationRep U n P) (h : ∀ s, P s ↔ Q s) :
    RelationRep U n Q where
  set := r.set
  set_mem := r.set_mem
  subset_space := r.subset_space
  correct := fun s => (r.correct s).trans (h s)

theorem mem_F3_triple_iff {x r a b c : ZFSet.{u}} :
    triple a b c ∈ F3 x r ↔ b ∈ x ∧ ZFSet.pair a c ∈ r := by
  rw [mem_F3_iff]
  constructor
  · rintro ⟨a', b', c', hb', hac', h⟩
    rcases ZFSet.pair_inj.mp h with ⟨rfl, htail⟩
    rcases ZFSet.pair_inj.mp htail with ⟨rfl, rfl⟩
    exact ⟨hb', hac'⟩
  · rintro ⟨hb, hac⟩
    exact ⟨a, b, c, hb, hac, rfl⟩

theorem mem_F4_triple_iff {x r a b c : ZFSet.{u}} :
    triple a b c ∈ F4 x r ↔ c ∈ x ∧ ZFSet.pair a b ∈ r := by
  rw [mem_F4_iff]
  constructor
  · rintro ⟨a', b', c', hc', hab', h⟩
    rcases ZFSet.pair_inj.mp h with ⟨rfl, htail⟩
    rcases ZFSet.pair_inj.mp htail with ⟨rfl, rfl⟩
    exact ⟨hc', hab'⟩
  · rintro ⟨hc, hab⟩
    exact ⟨a, b, c, hc, hab, rfl⟩

theorem pair_mem_F7_iff {U a b : ZFSet.{u}} (ha : a ∈ U) (hb : b ∈ U) :
    ZFSet.pair a b ∈ F7 U U ↔ a ∈ b := by
  rw [mem_F7_iff]
  constructor
  · rintro ⟨a', ha', b', hb', hp, hab⟩
    rcases ZFSet.pair_inj.mp hp with ⟨h₁, h₂⟩
    simpa [← h₁, ← h₂] using hab
  · intro hab
    exact ⟨a, ha, b, hb, rfl, hab⟩

/-- The primitive membership relation represents `last ∈ first` on pairs. -/
noncomputable def lastMemRepZero (U : ZFSet.{u}) :
    RelationRep U 1
      (fun s => (s (Fin.last 1)).1 ∈ (s 0).1) where
  set := F7 U U
  set_mem := F7_mem_rudimentaryClosure
    (self_mem_rudimentaryClosure U) (self_mem_rudimentaryClosure U)
  subset_space := by
    intro q hq
    rcases mem_F7_iff.mp hq with ⟨a, ha, b, hb, rfl, hab⟩
    rw [positiveTupleSpace, positiveTupleSpace, F2,
      ZFSet.pair_mem_prod]
    exact ⟨ha, hb⟩
  correct := by
    intro s
    simp only [positiveTupleCode]
    rw [mem_F7_iff]
    constructor
    · rintro ⟨a, ha, b, hb, hp, hab⟩
      rcases ZFSet.pair_inj.mp hp with ⟨h₁, h₂⟩
      simpa [← h₁, ← h₂] using hab
    · intro h
      exact ⟨(s (Fin.last 1)).1, (s (Fin.last 1)).2,
        (s 0).1, (s 0).2, rfl, h⟩

/-- Membership of the new last coordinate in the previous last coordinate. -/
noncomputable def lastMemRepLast (U : ZFSet.{u}) (n : Nat) :
    RelationRep U (n + 2)
      (fun s =>
        (s (Fin.last (n + 2))).1 ∈
          (s (Fin.last (n + 1)).castSucc).1) where
  set := F4 (positiveTupleSpace U n) (F7 U U)
  set_mem := F4_mem_rudimentaryClosure
    (positiveTupleSpace_mem_rudimentaryClosure U n)
    (F7_mem_rudimentaryClosure
      (self_mem_rudimentaryClosure U) (self_mem_rudimentaryClosure U))
  subset_space := by
    intro q hq
    rcases mem_F4_iff.mp hq with ⟨a, b, c, hc, hab, rfl⟩
    rw [positiveTupleSpace, F2, triple, ZFSet.pair_mem_prod]
    have hab' := (mem_F7_iff.mp hab)
    rcases hab' with ⟨a', ha', b', hb', hp, _⟩
    rcases ZFSet.pair_inj.mp hp with ⟨rfl, rfl⟩
    refine ⟨ha', ?_⟩
    rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod]
    exact ⟨hb', hc⟩
  correct := by
    intro s
    let tail : Tuple (ZFCarrier U) (n + 2) := fun i => s i.castSucc
    let rest : Tuple (ZFCarrier U) (n + 1) := fun i => tail i.castSucc
    let a : ZFCarrier U := s (Fin.last (n + 2))
    let b : ZFCarrier U := tail (Fin.last (n + 1))
    have hs : snoc tail a = s := tuple_snoc_eta s
    have ht : snoc rest b = tail := tuple_snoc_eta tail
    rw [← hs, ← ht]
    simp only [Constructible.Delta0Formula.val_snoc,
      positiveTupleCode_snoc, snoc_last, snoc_castSucc]
    change triple a.1 b.1
        (positiveTupleCode n (Constructible.Delta0Formula.val rest)) ∈
          F4 (positiveTupleSpace U n) (F7 U U) ↔ a.1 ∈ b.1
    rw [mem_F4_triple_iff,
      mem_positiveTupleSpace_iff, pair_mem_F7_iff a.2 b.2]
    simp

/-- Direct membership: the newest coordinate belongs to any older coordinate. -/
theorem exists_lastMemRep (U : ZFSet.{u}) :
    ∀ (n : Nat) (j : Fin (n + 1)),
      Nonempty <| RelationRep U (n + 1)
        (fun s =>
          (s (Fin.last (n + 1))).1 ∈ (s j.castSucc).1) := by
  intro n
  induction n with
  | zero =>
      intro j
      fin_cases j
      exact ⟨lastMemRepZero U⟩
  | succ n ih =>
      intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · exact ⟨lastMemRepLast U n⟩
      · rcases ih k with ⟨r⟩
        refine ⟨{
          set := F3 U r.set
          set_mem := F3_mem_rudimentaryClosure
            (self_mem_rudimentaryClosure U) r.set_mem
          subset_space := ?_
          correct := ?_
        }⟩
        · intro q hq
          rcases mem_F3_iff.mp hq with ⟨a, b, c, hb, hac, rfl⟩
          have hspace := r.subset_space hac
          rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod] at hspace
          rw [positiveTupleSpace, F2, triple, ZFSet.pair_mem_prod]
          refine ⟨hspace.1, ?_⟩
          rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod]
          exact ⟨hb, hspace.2⟩
        · intro s
          let tail : Tuple (ZFCarrier U) (n + 2) := fun i => s i.castSucc
          let rest : Tuple (ZFCarrier U) (n + 1) := fun i => tail i.castSucc
          let a : ZFCarrier U := s (Fin.last (n + 2))
          let b : ZFCarrier U := tail (Fin.last (n + 1))
          have hs : snoc tail a = s := tuple_snoc_eta s
          have ht : snoc rest b = tail := tuple_snoc_eta tail
          rw [← hs, ← ht]
          simp only [Constructible.Delta0Formula.val_snoc,
            positiveTupleCode_snoc, snoc_last, snoc_castSucc]
          change triple a.1 b.1
              (positiveTupleCode n (Constructible.Delta0Formula.val rest)) ∈
                F3 U r.set ↔ a.1 ∈ (rest k).1
          rw [mem_F3_triple_iff]
          have hr := r.correct (snoc rest a)
          simp only [Constructible.Delta0Formula.val_snoc,
            positiveTupleCode_snoc, snoc_last, snoc_castSucc] at hr
          rw [hr]
          simp [b.2]

/-- Chosen direct-membership representative. -/
noncomputable def lastMemRep (U : ZFSet.{u}) (n : Nat)
    (j : Fin (n + 1)) :
    RelationRep U (n + 1)
      (fun s =>
        (s (Fin.last (n + 1))).1 ∈ (s j.castSucc).1) :=
  Classical.choice (exists_lastMemRep U n j)

/-- Add one unused newest coordinate to a represented relation. -/
noncomputable def weakenLast {U : ZFSet.{u}} {n : Nat}
    {P : Tuple (ZFCarrier U) (n + 1) → Prop}
    (r : RelationRep U n P) :
    RelationRep U (n + 1)
      (fun s => P (fun i => s i.castSucc)) where
  set := F2 U r.set
  set_mem := F2_mem_rudimentaryClosure
    (self_mem_rudimentaryClosure U) r.set_mem
  subset_space := by
    intro q hq
    rcases mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
    rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod]
    exact ⟨ha, r.subset_space hb⟩
  correct := by
    intro s
    let pref : Tuple (ZFCarrier U) (n + 1) := fun i => s i.castSucc
    let x : ZFCarrier U := s (Fin.last (n + 1))
    have hs : snoc pref x = s := tuple_snoc_eta s
    rw [← hs]
    simp only [Constructible.Delta0Formula.val_snoc,
      positiveTupleCode_snoc, F2, ZFSet.pair_mem_prod]
    rw [r.correct]
    simp [x.2, pref]

/-- Membership atoms whose member coordinate occurs later than the container. -/
theorem exists_forwardMemRep (U : ZFSet.{u}) :
    ∀ (n : Nat) (i j : Fin (n + 1)), j < i →
      Nonempty (RelationRep U n (fun s => (s i).1 ∈ (s j).1)) := by
  intro n
  induction n with
  | zero =>
      intro i j h
      fin_cases i
      fin_cases j
      omega
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · intro h
          omega
        · intro h
          exact ⟨lastMemRep U n k⟩
      · intro j
        refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro h
          exact False.elim ((not_lt_of_ge (Fin.le_last ii.castSucc)) h)
        · intro h
          have hjj : jj < ii := by simpa using h
          rcases ih ii jj hjj with ⟨r⟩
          exact ⟨weakenLast r⟩

/-- Chosen representative for a forward-oriented membership atom. -/
noncomputable def forwardMemRep (U : ZFSet.{u}) {n : Nat}
    (i j : Fin (n + 1)) (h : j < i) :
    RelationRep U n (fun s => (s i).1 ∈ (s j).1) :=
  Classical.choice (exists_forwardMemRep U n i j h)

/-- The full relation on all nonempty tuples over `U`. -/
noncomputable def top (U : ZFSet.{u}) (n : Nat) :
    RelationRep U n (fun _ => True) where
  set := positiveTupleSpace U n
  set_mem := positiveTupleSpace_mem_rudimentaryClosure U n
  subset_space := Set.Subset.rfl
  correct := by
    intro s
    rw [mem_positiveTupleSpace_iff]
    simp

/-- Complement a represented relation inside the tuple space. -/
noncomputable def neg {U : ZFSet.{u}} {n : Nat}
    {P : Tuple (ZFCarrier U) (n + 1) → Prop}
    (r : RelationRep U n P) : RelationRep U n (fun s => ¬P s) where
  set := F1 (positiveTupleSpace U n) r.set
  set_mem := F1_mem_rudimentaryClosure
    (positiveTupleSpace_mem_rudimentaryClosure U n) r.set_mem
  subset_space := by
    intro z hz
    exact (mem_F1_iff.mp hz).1
  correct := by
    intro s
    rw [mem_F1_iff, r.correct, mem_positiveTupleSpace_iff]
    simp

/-- Intersect two represented relations. -/
noncomputable def conj {U : ZFSet.{u}} {n : Nat}
    {P Q : Tuple (ZFCarrier U) (n + 1) → Prop}
    (r : RelationRep U n P) (t : RelationRep U n Q) :
    RelationRep U n (fun s => P s ∧ Q s) where
  set := F1 r.set (F1 r.set t.set)
  set_mem := F1_mem_rudimentaryClosure r.set_mem
    (F1_mem_rudimentaryClosure r.set_mem t.set_mem)
  subset_space := by
    intro z hz
    exact r.subset_space (mem_F1_iff.mp hz).1
  correct := by
    intro s
    simp only [mem_F1_iff, r.correct, t.correct]
    tauto

/-- Union/disjunction of two represented relations. -/
noncomputable def disj {U : ZFSet.{u}} {n : Nat}
    {P Q : Tuple (ZFCarrier U) (n + 1) → Prop}
    (r : RelationRep U n P) (t : RelationRep U n Q) :
    RelationRep U n (fun s => P s ∨ Q s) := by
  apply congr (neg (conj (neg r) (neg t)))
  intro s
  tauto

/-- The empty relation. -/
noncomputable def bot (U : ZFSet.{u}) (n : Nat) :
    RelationRep U n (fun _ => False) := by
  apply congr (neg (top U n))
  intro s
  simp

/-- Project away the newest (last syntactic, outermost coded) coordinate. -/
noncomputable def ex {U : ZFSet.{u}} {n : Nat}
    {P : Tuple (ZFCarrier U) (n + 2) → Prop}
    (r : RelationRep U (n + 1) P) :
    RelationRep U n (fun s => ∃ x : ZFCarrier U, P (snoc s x)) where
  set := F6 r.set U
  set_mem := F6_mem_rudimentaryClosure r.set_mem
    (self_mem_rudimentaryClosure U)
  subset_space := by
    intro z hz
    rcases mem_F6_iff.mp hz with ⟨w, hw⟩
    have hspace := r.subset_space hw
    rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod] at hspace
    exact hspace.2
  correct := by
    intro s
    constructor
    · intro h
      rcases mem_F6_iff.mp h with ⟨w, hw⟩
      have hspace := r.subset_space hw
      rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod] at hspace
      let x : ZFCarrier U := ⟨w, hspace.1⟩
      refine ⟨x, ?_⟩
      apply (r.correct (snoc s x)).mp
      simpa only [Constructible.Delta0Formula.val_snoc,
        positiveTupleCode_snoc, x] using hw
    · rintro ⟨x, hx⟩
      apply mem_F6_iff.mpr
      refine ⟨x.1, ?_⟩
      have hcode := (r.correct (snoc s x)).mpr hx
      simpa only [Constructible.Delta0Formula.val_snoc,
        positiveTupleCode_snoc] using hcode

/-- Equality of two coordinates, obtained extensionally from direct membership. -/
noncomputable def eqRep (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (i j : Fin (n + 1)) :
    RelationRep U n (fun s => (s i).1 = (s j).1) := by
  let ri := lastMemRep U n i
  let rj := lastMemRep U n j
  let differing := disj (conj ri (neg rj)) (conj rj (neg ri))
  apply congr (neg (ex differing))
  intro s
  simp only [snoc_last, snoc_castSucc]
  change
    (¬∃ y : ZFCarrier U,
      ((y.1 ∈ (s i).1 ∧ y.1 ∉ (s j).1) ∨
        (y.1 ∈ (s j).1 ∧ y.1 ∉ (s i).1))) ↔
      (s i).1 = (s j).1
  constructor
  · intro h
    apply ZFSet.ext
    intro y
    constructor
    · intro hyi
      by_contra hyj
      have hyU : y ∈ U := hU.mem_trans hyi (s i).2
      exact h ⟨⟨y, hyU⟩, Or.inl ⟨hyi, hyj⟩⟩
    · intro hyj
      by_contra hyi
      have hyU : y ∈ U := hU.mem_trans hyj (s j).2
      exact h ⟨⟨y, hyU⟩, Or.inr ⟨hyj, hyi⟩⟩
  · intro hij h
    rcases h with ⟨y, h | h⟩
    · exact h.2 (hij ▸ h.1)
    · exact h.2 (hij.symm ▸ h.1)

/-- An arbitrary membership atom, reduced to direct membership plus equality. -/
noncomputable def memRep (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (i j : Fin (n + 1)) :
    RelationRep U n (fun s => (s i).1 ∈ (s j).1) := by
  let zIndex : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let yIndex : Fin (n + 3) := Fin.last (n + 2)
  let direct := lastMemRep U (n + 1) (Fin.last (n + 1))
  let yEq := eqRep U hU yIndex i.castSucc.castSucc
  let zEq := eqRep U hU zIndex j.castSucc.castSucc
  apply congr (ex (ex (conj direct (conj yEq zEq))))
  intro s
  simp only [zIndex, yIndex, snoc_last, snoc_castSucc]
  change
    (∃ z : ZFCarrier U, ∃ y : ZFCarrier U,
      y.1 ∈ z.1 ∧ y.1 = (s i).1 ∧ z.1 = (s j).1) ↔
      (s i).1 ∈ (s j).1
  constructor
  · rintro ⟨z, y, hyz, hy, hz⟩
    simpa [hy, hz] using hyz
  · intro h
    exact ⟨s j, s i, h, rfl, rfl⟩

/-- Compile every positive-arity first-order relation over `U` to a rudimentary set. -/
noncomputable def formulaRep (U : ZFSet.{u}) (hU : U.IsTransitive) :
    {n : Nat} → (φ : FOFormula (n + 1)) →
      RelationRep U n
        (fun s => FOFormula.Satisfies (zfCarrierMem U) φ s)
  | _, .mem i j => memRep U hU i j
  | _, .eq i j => by
      apply congr (eqRep U hU i j)
      intro s
      change (s i).1 = (s j).1 ↔ s i = s j
      exact Subtype.ext_iff.symm
  | _, .neg φ => neg (formulaRep U hU φ)
  | _, .conj φ ψ => conj (formulaRep U hU φ) (formulaRep U hU ψ)
  | _, .ex φ => ex (formulaRep U hU φ)

/-- Every formula-defined subset of a transitive `U` belongs to its rudimentary closure. -/
theorem definableSection_mem_rudimentaryClosure {U z : ZFSet.{u}}
    (hU : U.IsTransitive) (hzU : z ⊆ U) {n : Nat}
    (params : Tuple (ZFCarrier U) n) (φ : FOFormula (n + 1))
    (hdef : ∀ q : ZFCarrier U,
      q.1 ∈ z ↔ FOFormula.Satisfies (zfCarrierMem U) φ (snoc params q)) :
    z ∈ rudimentaryClosure U := by
  cases n with
  | zero =>
      let r := formulaRep U hU φ
      have heq : z = r.set := by
        apply ZFSet.ext
        intro y
        constructor
        · intro hy
          let q : ZFCarrier U := ⟨y, hzU hy⟩
          have hsat := (hdef q).mp hy
          have hcode := (r.correct (snoc params q)).mpr hsat
          change y ∈ r.set at hcode
          exact hcode
        · intro hy
          have hyU : y ∈ U := by
            have hspace := r.subset_space hy
            simpa [positiveTupleSpace] using hspace
          let q : ZFCarrier U := ⟨y, hyU⟩
          apply (hdef q).mpr
          apply (r.correct (snoc params q)).mp
          change y ∈ r.set
          exact hy
      rw [heq]
      exact r.set_mem
  | succ n =>
      let r := formulaRep U hU φ
      let p := positiveTupleCode n (Constructible.Delta0Formula.val params)
      have hp : p ∈ rudimentaryClosure U :=
        positiveTupleCode_mem_rudimentaryClosure params
      have hfiber : fiber r.set p ∈ rudimentaryClosure U :=
        fiber_mem_rudimentaryClosure r.set_mem hp
      have heq : z = fiber r.set p := by
        apply ZFSet.ext
        intro y
        constructor
        · intro hy
          let q : ZFCarrier U := ⟨y, hzU hy⟩
          apply mem_fiber_iff.mpr
          have hsat := (hdef q).mp hy
          have hcode := (r.correct (snoc params q)).mpr hsat
          simpa only [Constructible.Delta0Formula.val_snoc,
            positiveTupleCode_snoc, p] using hcode
        · intro hy
          have hpair : ZFSet.pair y p ∈ r.set := mem_fiber_iff.mp hy
          have hspace := r.subset_space hpair
          rw [positiveTupleSpace, F2, ZFSet.pair_mem_prod] at hspace
          let q : ZFCarrier U := ⟨y, hspace.1⟩
          apply (hdef q).mpr
          apply (r.correct (snoc params q)).mp
          simpa only [Constructible.Delta0Formula.val_snoc,
            positiveTupleCode_snoc, p, q] using hpair
      rw [heq]
      exact hfiber

private theorem defZF_subset_godelDef_aux {U : ZFSet.{u}}
    (hU : U.IsTransitive) :
    Constructible.DefZF U ⊆ godelDef U := by
  intro z hz
  rcases Constructible.mem_DefZF_iff_exists_satisfies.mp hz with
    ⟨hzU, n, params, φ, hdef⟩
  apply mem_godelDef_iff.mpr
  exact ⟨hzU,
    definableSection_mem_rudimentaryClosure hU hzU params φ hdef⟩

end RelationRep

/-- Formula definability implies membership in the Gödel-operation
presentation. -/
theorem DefZF_subset_godelDef {U : ZFSet.{u}} (hU : U.IsTransitive) :
    Constructible.DefZF U ⊆ godelDef U :=
  RelationRep.defZF_subset_godelDef_aux hU

end Constructible.Godel
