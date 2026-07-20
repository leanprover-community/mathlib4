/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Delta0Godel

/-!
# Bounded graph formulas for the Gödel operations

Membership in every Jensen--Devlin operation is `Δ₀`.  This file strengthens
that result to formulas for the full graphs `out = Fᵢ(x,y)`, using only bounded
quantifiers in both containment directions.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

/-- Place the uniform operation-membership formula at arbitrary coordinates. -/
def memOpAt {n : Nat} (i : Fin 9) (q x y : Fin n) : Delta0Formula n :=
  Delta0Formula.rename ![q, x, y] (memOpFormula i)

@[simp]
theorem satisfies_memOpAt {n : Nat} (i : Fin 9) (q x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memOpAt i q x y) s ↔
      s q ∈ op i (s x) (s y) := by
  rw [memOpAt, Delta0Formula.satisfies_rename]
  have hassign :
      (fun j => s (![q, x, y] j)) = ![s q, s x, s y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_memOpFormula i (s q) (s x) (s y)

/-- The forward-containment half of an operation graph. -/
def outputSubsetOpAt {n : Nat} (i : Fin 9) (out x y : Fin n) :
    Delta0Formula n :=
  .boundedAll out
    (memOpAt i (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_outputSubsetOpAt {n : Nat} (i : Fin 9)
    (out x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (outputSubsetOpAt i out x y) s ↔
      s out ⊆ op i (s x) (s y) := by
  simp only [outputSubsetOpAt, Delta0Formula.satisfies_boundedAll,
    satisfies_memOpAt, snoc_last, snoc_castSucc]
  rfl

/-! All graph formulas below use the fixed assignment `![out,x,y]`. -/

/-- The graph of `F₀(x,y) = {x,y}`. -/
def graphF0Formula : Delta0Formula 3 :=
  unorderedPairEqAt 0 1 2

@[simp]
theorem satisfies_graphF0Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF0Formula ![out, x, y] ↔ out = F0 x y := by
  simp [graphF0Formula, F0]

/-- The fully bounded graph of `F₁(x,y) = x \ y`. -/
def graphF1Formula : Delta0Formula 3 :=
  .conj
    (subsetAt 0 1)
    (.boundedAll 1
      (.biimp
        (.mem 3 0)
        (.neg (.mem 3 2))))

@[simp]
theorem satisfies_graphF1Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF1Formula ![out, x, y] ↔ out = F1 x y := by
  simp only [graphF1Formula, Satisfies, satisfies_subsetAt,
    satisfies_boundedAll, satisfies_biimp]
  rw [ZFSet.ext_iff]
  simp only [mem_F1_iff]
  constructor
  · rintro ⟨houtx, hchar⟩ z
    constructor
    · intro hzout
      have hzx : z ∈ x := houtx hzout
      exact ⟨hzx, (hchar z hzx).mp hzout⟩
    · rintro ⟨hzx, hzy⟩
      exact (hchar z hzx).mpr hzy
  · intro hext
    constructor
    · intro z hzout
      exact (hext z).mp hzout |>.1
    · intro z hzx
      constructor
      · intro hzout
        exact (hext z).mp hzout |>.2
      · intro hzy
        exact (hext z).mpr ⟨hzx, hzy⟩

/-- The fully bounded graph of `F₂(x,y) = x × y`. -/
def graphF2Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 2
          (kuratowskiPairEqAt 3 4 5))))
    (.boundedAll 1
      (.boundedAll 2
        (.boundedEx 0
          (kuratowskiPairEqAt 5 3 4))))

@[simp]
theorem satisfies_graphF2Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF2Formula ![out, x, y] ↔ out = F2 x y := by
  simp only [graphF2Formula, Satisfies, satisfies_boundedAll,
    satisfies_kuratowskiPairEqAt]
  change
    ((∀ q : ZFSet.{u}, q ∈ out →
        ∃ a : ZFSet.{u}, a ∈ x ∧
          ∃ b : ZFSet.{u}, b ∈ y ∧ q = ZFSet.pair a b) ∧
      ∀ a : ZFSet.{u}, a ∈ x →
        ∀ b : ZFSet.{u}, b ∈ y →
          ∃ p : ZFSet.{u}, p ∈ out ∧ p = ZFSet.pair a b) ↔
      out = F2 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F2_iff]
    constructor
    · exact hsub q
    · rintro ⟨a, hax, b, hby, rfl⟩
      rcases hsup a hax b hby with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F2_iff.mp hq
    · intro a hax b hby
      refine ⟨ZFSet.pair a b, ?_, rfl⟩
      rw [h, mem_F2_iff]
      exact ⟨a, hax, b, hby, rfl⟩

/-- Reverse-containment formula for `F₃`. -/
def containsF3Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 3 8))))))))

set_option maxHeartbeats 1200000 in
-- Six nested bounded witnesses require extra reduction of appended assignments.
@[simp]
theorem satisfies_containsF3Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem containsF3Formula ![out, x, y] ↔
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v := by
  simp only [containsF3Formula, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∀ z : ZFSet.{u}, z ∈ x →
      ∀ p : ZFSet.{u}, p ∈ y →
        ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
          ∀ u : ZFSet.{u}, u ∈ leftBox →
            ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
              ∀ v : ZFSet.{u}, v ∈ rightBox →
                p = ZFSet.pair u v →
                  ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v) ↔
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v)
  rfl

/-- The fully bounded graph of `F₃(x,y)`. -/
def graphF3Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (3 : Fin 9) 0 1 2) containsF3Formula

@[simp]
theorem satisfies_graphF3Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF3Formula ![out, x, y] ↔ out = F3 x y := by
  simp only [graphF3Formula, Satisfies, satisfies_outputSubsetOpAt,
    satisfies_containsF3Formula]
  change
    (out ⊆ F3 x y ∧
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v)) ↔
      out = F3 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact fun hqout => hsub hqout
    · intro hq
      rcases mem_F3_iff.mp hq with ⟨u, z, v, hzx, huv, rfl⟩
      rcases hsup z hzx (ZFSet.pair u v) huv ({u} : ZFSet.{u})
          (by simp [ZFSet.pair]) u (by simp) ({u, v} : ZFSet.{u})
          (by simp [ZFSet.pair]) v (by simp) rfl with ⟨q', hq', hq'eq⟩
      rw [← hq'eq]
      exact hq'
  · intro h
    constructor
    · rw [h]
    · intro z hzx p hpy leftBox hleftBox u hu rightBox hrightBox v hv hp
      refine ⟨triple u z v, ?_, rfl⟩
      rw [h, mem_F3_iff]
      refine ⟨u, z, v, hzx, ?_, rfl⟩
      rw [← hp]
      exact hpy

/-- Reverse-containment formula for `F₄`. -/
def containsF4Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 8 3))))))))

set_option maxHeartbeats 1200000 in
-- Six nested bounded witnesses require extra reduction of appended assignments.
@[simp]
theorem satisfies_containsF4Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem containsF4Formula ![out, x, y] ↔
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z := by
  simp only [containsF4Formula, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∀ z : ZFSet.{u}, z ∈ x →
      ∀ p : ZFSet.{u}, p ∈ y →
        ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
          ∀ u : ZFSet.{u}, u ∈ leftBox →
            ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
              ∀ v : ZFSet.{u}, v ∈ rightBox →
                p = ZFSet.pair u v →
                  ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z) ↔
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z)
  rfl

/-- The fully bounded graph of `F₄(x,y)`. -/
def graphF4Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (4 : Fin 9) 0 1 2) containsF4Formula

@[simp]
theorem satisfies_graphF4Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF4Formula ![out, x, y] ↔ out = F4 x y := by
  simp only [graphF4Formula, Satisfies, satisfies_outputSubsetOpAt,
    satisfies_containsF4Formula]
  change
    (out ⊆ F4 x y ∧
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z)) ↔
      out = F4 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact fun hqout => hsub hqout
    · intro hq
      rcases mem_F4_iff.mp hq with ⟨u, v, z, hzx, huv, rfl⟩
      rcases hsup z hzx (ZFSet.pair u v) huv ({u} : ZFSet.{u})
          (by simp [ZFSet.pair]) u (by simp) ({u, v} : ZFSet.{u})
          (by simp [ZFSet.pair]) v (by simp) rfl with ⟨q', hq', hq'eq⟩
      rw [← hq'eq]
      exact hq'
  · intro h
    constructor
    · rw [h]
    · intro z hzx p hpy leftBox hleftBox u hu rightBox hrightBox v hv hp
      refine ⟨triple u v z, ?_, rfl⟩
      rw [h, mem_F4_iff]
      refine ⟨u, v, z, hzx, ?_, rfl⟩
      rw [← hp]
      exact hpy

/-- The fully bounded graph of `F₅(x,y) = ⋃₀x`. -/
def graphF5Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.mem 3 4)))
    (.boundedAll 1
      (.boundedAll 3
        (.mem 4 0)))

@[simp]
theorem satisfies_graphF5Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF5Formula ![out, x, y] ↔ out = F5 x y := by
  simp only [graphF5Formula, Satisfies, satisfies_boundedAll]
  rw [ZFSet.ext_iff]
  simp only [mem_F5_iff]
  constructor
  · rintro ⟨hforward, hback⟩ z
    constructor
    · exact hforward z
    · rintro ⟨w, hwx, hzw⟩
      exact hback w hwx z hzw
  · intro hext
    constructor
    · intro z hzout
      exact (hext z).mp hzout
    · intro w hwx z hzw
      exact (hext z).mpr ⟨w, hwx, hzw⟩

/-- The fully bounded graph of `F₆(x,y)`. -/
def graphF6Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f6MemAt 3 1))
    (.boundedAll 1
      (.boundedAll 3
        (.boundedAll 4
          (.imp
            (f6MemAt 5 1)
            (.mem 5 0)))))

@[simp]
theorem satisfies_graphF6Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF6Formula ![out, x, y] ↔ out = F6 x y := by
  simp only [graphF6Formula, Satisfies, satisfies_boundedAll,
    satisfies_imp, satisfies_f6MemAt]
  change
    (((∀ q : ZFSet.{u}, q ∈ out →
          ∃ w : ZFSet.{u}, ZFSet.pair w q ∈ x) ∧
       (∀ p : ZFSet.{u}, p ∈ x →
          ∀ box : ZFSet.{u}, box ∈ p →
            ∀ q : ZFSet.{u}, q ∈ box →
              (∃ w : ZFSet.{u}, ZFSet.pair w q ∈ x) → q ∈ out)) ↔
      out = F6 x y)
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F6_iff]
    constructor
    · exact hsub q
    · rintro ⟨w, hp⟩
      exact hsup (ZFSet.pair w q) hp ({w, q} : ZFSet.{u})
        (by simp [ZFSet.pair]) q (by simp) ⟨w, hp⟩
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F6_iff.mp hq
    · intro p hp box hbox q hqbox hq
      rw [h, mem_F6_iff]
      exact hq

/-- The fully bounded graph of `F₇(x,y)`. -/
def graphF7Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 1
          (.conj
            (kuratowskiPairEqAt 3 4 5)
            (.mem 4 5)))))
    (.boundedAll 1
      (.boundedAll 1
        (.imp (.mem 3 4)
          (.boundedEx 0
            (kuratowskiPairEqAt 5 3 4)))))

@[simp]
theorem satisfies_graphF7Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF7Formula ![out, x, y] ↔ out = F7 x y := by
  simp only [graphF7Formula, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_kuratowskiPairEqAt]
  change
    ((∀ q : ZFSet.{u}, q ∈ out →
        ∃ z : ZFSet.{u}, z ∈ x ∧
          ∃ w : ZFSet.{u}, w ∈ x ∧
            (q = ZFSet.pair z w ∧ z ∈ w)) ∧
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ w : ZFSet.{u}, w ∈ x →
          z ∈ w →
            ∃ p : ZFSet.{u}, p ∈ out ∧ p = ZFSet.pair z w) ↔
      out = F7 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F7_iff]
    constructor
    · exact hsub q
    · rintro ⟨z, hzx, w, hwx, rfl, hzw⟩
      rcases hsup z hzx w hwx hzw with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F7_iff.mp hq
    · intro z hzx w hwx hzw
      refine ⟨ZFSet.pair z w, ?_, rfl⟩
      rw [h, mem_F7_iff]
      exact ⟨z, hzx, w, hwx, rfl, hzw⟩

/-- The fully bounded graph of `F₈(x,y)`. -/
def graphF8Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f8MemAt 3 1 2))
    (.boundedAll 2
      (.boundedEx 0
        (fiberEqAt 4 1 3)))

@[simp]
theorem satisfies_graphF8Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF8Formula ![out, x, y] ↔ out = F8 x y := by
  simp only [graphF8Formula, Satisfies, satisfies_boundedAll,
    satisfies_f8MemAt, satisfies_fiberEqAt]
  change
    (((∀ q : ZFSet.{u}, q ∈ out → q ∈ F8 x y) ∧
       (∀ z : ZFSet.{u}, z ∈ y →
          ∃ q : ZFSet.{u}, q ∈ out ∧ q = fiber x z)) ↔
      out = F8 x y)
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact hsub q
    · intro hq
      rcases mem_F8_iff.mp hq with ⟨z, hzy, hqz⟩
      rcases hsup z hzy with ⟨q', hq'out, hq'z⟩
      simpa [hqz, hq'z] using hq'out
  · intro h
    constructor
    · intro q hq
      simpa [h] using hq
    · intro z hz
      refine ⟨fiber x z, ?_, rfl⟩
      rw [h, mem_F8_iff]
      exact ⟨z, hz, rfl⟩

/-- Uniform fully bounded graph formula for all nine Gödel operations. -/
def opGraphFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => graphF0Formula
  | 1 => graphF1Formula
  | 2 => graphF2Formula
  | 3 => graphF3Formula
  | 4 => graphF4Formula
  | 5 => graphF5Formula
  | 6 => graphF6Formula
  | 7 => graphF7Formula
  | 8 => graphF8Formula
  | _ => .neg (.eq 0 0)

@[simp]
theorem satisfies_opGraphFormula (i : Fin 9) (out x y : ZFSet.{u}) :
    Satisfies ZFMem (opGraphFormula i) ![out, x, y] ↔
      out = op i x y := by
  fin_cases i <;> simp [opGraphFormula, op]

@[simp]
theorem satisfies_toFO_opGraphFormula (i : Fin 9) (out x y : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem (opGraphFormula i).toFO ![out, x, y] ↔
      out = op i x y := by
  rw [Delta0Formula.satisfies_toFO, satisfies_opGraphFormula]

end Constructible.Godel
