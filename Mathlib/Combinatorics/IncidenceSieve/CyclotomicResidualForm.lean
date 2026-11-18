/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/

/-!
# Finite Cyclotomic Incidence Sieve and Residual Form Left Behind

This module formalizes the finite multi-block incidence sieve connecting
cyclotomic circle/plane covers to the surviving residual form left behind.
It proves universally quantified sieve conservation laws over arbitrary
multiplicity bucket lists and instantiates the three-level master certificate
for Band 1 matchings, 20 coordinate planes, and degree-2 Macaulay syzygies.
-/

namespace Combinatorics.IncidenceSieve
set_option maxRecDepth 4096

def rangeList (start count : Nat) : List Nat :=
  match count with
  | 0 => []
  | c + 1 => start :: rangeList (start + 1) c

def intEq (a b : Int) : Bool := (a - b).natAbs == 0

def intNe (a b : Int) : Bool := (a - b).natAbs != 0

def gcdFuel : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | k + 1, a, b => if b == 0 then a else gcdFuel k b (a % b)

def coprimeUnits (m : Nat) : List Nat :=
  (rangeList 1 (m - 1)).filter (fun t => gcdFuel m t m == 1)

def isShiodaHodge22 (m : Nat) (a : List Nat) : Bool :=
  a.length == 6 &&
  a.all (fun x => Nat.blt 0 x && Nat.blt x m) &&
  (coprimeUnits m).all (fun t =>
    (a.foldl (fun acc x => acc + (t * x) % m) 0) == 3 * m)

def with6Nat (a : List Nat) (f : Nat → Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  match a with
  | [] => false
  | a0 :: r0 => match r0 with
    | [] => false
    | a1 :: r1 => match r1 with
      | [] => false
      | a2 :: r2 => match r2 with
        | [] => false
        | a3 :: r3 => match r3 with
          | [] => false
          | a4 :: r4 => match r4 with
            | [] => false
            | a5 :: r5 => match r5 with
              | [] => f a0 a1 a2 a3 a4 a5
              | _ :: _ => false

def isBand1CompletePairs (m : Nat) (a : List Nat) : Bool :=
  with6Nat a fun a0 a1 a2 a3 a4 a5 =>
    (a0 + a1 == m && a2 + a3 == m && a4 + a5 == m) ||
    (a0 + a1 == m && a2 + a4 == m && a3 + a5 == m) ||
    (a0 + a1 == m && a2 + a5 == m && a3 + a4 == m) ||
    (a0 + a2 == m && a1 + a3 == m && a4 + a5 == m) ||
    (a0 + a2 == m && a1 + a4 == m && a3 + a5 == m) ||
    (a0 + a2 == m && a1 + a5 == m && a3 + a4 == m) ||
    (a0 + a3 == m && a1 + a2 == m && a4 + a5 == m) ||
    (a0 + a3 == m && a1 + a4 == m && a2 + a5 == m) ||
    (a0 + a3 == m && a1 + a5 == m && a2 + a4 == m) ||
    (a0 + a4 == m && a1 + a2 == m && a3 + a5 == m) ||
    (a0 + a4 == m && a1 + a3 == m && a2 + a5 == m) ||
    (a0 + a4 == m && a1 + a5 == m && a2 + a3 == m) ||
    (a0 + a5 == m && a1 + a2 == m && a3 + a4 == m) ||
    (a0 + a5 == m && a1 + a3 == m && a2 + a4 == m) ||
    (a0 + a5 == m && a1 + a4 == m && a2 + a3 == m)

def isBand2ThreePlusThree (m : Nat) (a : List Nat) : Bool :=
  if isBand1CompletePairs m a then false
  else
    with6Nat a fun a0 a1 a2 a3 a4 a5 =>
      let check (s1 s2 : Nat) : Bool := (s1 == m && s2 == 2 * m) || (s1 == 2 * m && s2 == m)
      check (a0 + a1 + a2) (a3 + a4 + a5) ||
      check (a0 + a1 + a3) (a2 + a4 + a5) ||
      check (a0 + a1 + a4) (a2 + a3 + a5) ||
      check (a0 + a1 + a5) (a2 + a3 + a4) ||
      check (a0 + a2 + a3) (a1 + a4 + a5) ||
      check (a0 + a2 + a4) (a1 + a3 + a5) ||
      check (a0 + a2 + a5) (a1 + a3 + a4) ||
      check (a0 + a3 + a4) (a1 + a2 + a5) ||
      check (a0 + a3 + a5) (a1 + a2 + a4) ||
      check (a0 + a4 + a5) (a1 + a2 + a3)

def isBand3TwoPlusFour (m : Nat) (a : List Nat) : Bool :=
  if isBand1CompletePairs m a || isBand2ThreePlusThree m a then false
  else
    with6Nat a fun a0 a1 a2 a3 a4 a5 =>
      (a0 + a1 == m) || (a0 + a2 == m) || (a0 + a3 == m) || (a0 + a4 == m) || (a0 + a5 == m) ||
      (a1 + a2 == m) || (a1 + a3 == m) || (a1 + a4 == m) || (a1 + a5 == m) ||
      (a2 + a3 == m) || (a2 + a4 == m) || (a2 + a5 == m) ||
      (a3 + a4 == m) || (a3 + a5 == m) ||
      (a4 + a5 == m)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def countOcc (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + countOcc x ys

def uniqueList : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let u := uniqueList xs
    if u.contains x then u else x :: u

def s6OrbitSize (a : List Nat) : Nat :=
  let denom := (uniqueList a).foldl (fun acc x => acc * fact (countOcc x a)) 1
  fact a.length / denom

def sortedHodge22Tuples (m : Nat) : List (List Nat) :=
  let units := coprimeUnits m
  let checkHodge (a0 a1 a2 a3 a4 a5 : Nat) : Bool :=
    units.all (fun t =>
      ((t * a0) % m + (t * a1) % m + (t * a2) % m +
       (t * a3) % m + (t * a4) % m + (t * a5) % m) == 3 * m)
  let vals0 := rangeList 1 (m / 2)
  vals0.foldl (fun acc0 a0 =>
    let vals1 := rangeList a0 (m - a0)
    acc0 ++ vals1.foldl (fun acc1 a1 =>
      if Nat.blt (3 * m) (a0 + 5 * a1) then acc1 else
      let vals2 := rangeList a1 (m - a1)
      acc1 ++ vals2.foldl (fun acc2 a2 =>
        if Nat.blt (3 * m) (a0 + a1 + 4 * a2) then acc2 else
        let vals3 := rangeList a2 (m - a2)
        acc2 ++ vals3.foldl (fun acc3 a3 =>
          if Nat.blt (3 * m) (a0 + a1 + a2 + 3 * a3) then acc3 else
          let vals4 := rangeList a3 (m - a3)
          acc3 ++ vals4.foldl (fun acc4 a4 =>
            let s := a0 + a1 + a2 + a3 + a4
            if Nat.blt (3 * m) (s + a4) then acc4 else
            let a5 := 3 * m - s
            if Nat.blt a5 m && checkHodge a0 a1 a2 a3 a4 a5 then
              acc4 ++ [[a0, a1, a2, a3, a4, a5]]
            else acc4
          ) []
        ) []
      ) []
    ) []
  ) []

def summarizeHodgeTuples (m : Nat) (ts : List (List Nat)) :
    Nat × Nat × Nat × Nat × Nat × List (List Nat) :=
  ts.foldl (fun (h22, b1, b2, b3, b4, reps) tuple =>
    let w := s6OrbitSize tuple
    if isBand1CompletePairs m tuple then (h22 + w, b1 + w, b2, b3, b4, reps)
    else if isBand2ThreePlusThree m tuple then (h22 + w, b1, b2 + w, b3, b4, reps)
    else if isBand3TwoPlusFour m tuple then (h22 + w, b1, b2, b3 + w, b4, reps)
    else (h22 + w, b1, b2, b3, b4 + w, reps ++ [tuple])
  ) (0, 0, 0, 0, 0, [])

def fermatCensusSummary (m : Nat) : Nat × Nat × Nat × Nat × Nat × List (List Nat) :=
  summarizeHodgeTuples m (sortedHodge22Tuples m)

def fermat_band2_count (m : Nat) : Nat := (fermatCensusSummary m).2.2.1

def fermat_band3_count (m : Nat) : Nat := (fermatCensusSummary m).2.2.2.1

def getIntAt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getIntAt xs k

def transposeMat (n : Nat) (m : List (List Int)) : List (List Int) :=
  (rangeList 0 n).map (fun j => m.map (fun r => getIntAt r j))

def monomials4 (d : Nat) : List (List Nat) :=
  [0, 1, 2, 3, 4].foldl (fun acc0 a0 =>
    if Nat.blt d a0 then acc0 else
    acc0 ++ [0, 1, 2, 3, 4].foldl (fun acc1 a1 =>
      if Nat.blt d (a0 + a1) then acc1 else
      acc1 ++ [0, 1, 2, 3, 4].foldl (fun acc2 a2 =>
        if Nat.blt d (a0 + a1 + a2) then acc2 else
        let a3 := d - (a0 + a1 + a2)
        if Nat.ble a3 4 then acc2 ++ [[a0, a1, a2, a3]] else acc2
      ) []
    ) []
  ) []

def addExp4 : List Nat → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x + y) :: addExp4 xs ys

def natListEqBool (l1 l2 : List Nat) : Bool :=
  match l1 with
  | [] => match l2 with | [] => true | _ :: _ => false
  | x :: xs => match l2 with | [] => false | y :: ys => (x == y) && natListEqBool xs ys

def coeffInSocle (m : List Nat) (socle : List (List Nat × Int)) : Int :=
  socle.foldl (fun acc (s, c) => if natListEqBool s m then acc + c else acc) 0

def planeSoclePoly : List (List Nat × Int) := [([0, 4, 4, 4], 1)]

def quadricJetSoclePoly : List (List Nat × Int) := [([0, 4, 4, 4], 1), ([4, 0, 4, 4], 1)]

def macaulayPairingMatrix (socle : List (List Nat × Int)) (d : Nat) : List (List Int) :=
  let rows := monomials4 d
  let cols := monomials4 (12 - d)
  rows.map (fun m1 => cols.map (fun m2 => coeffInSocle (addExp4 m1 m2) socle))

def intElimStep (pivotRow : List Int) (p : Int) (row : List Int) : List Int :=
  match row with
  | [] => []
  | r0 :: _ =>
    (List.zipWith (fun a b => p * b - r0 * a) pivotRow row).drop 1

def intMatRankAuxClean (cols : Nat) (rows : List (List Int)) : Nat :=
  match cols with
  | 0 => 0
  | cols' + 1 =>
    match rows with
    | [] => 0
    | _ :: _ =>
      let nonZero := rows.filter (fun r => match r with | [] => false | x :: _ => intNe x 0)
      match nonZero with
      | [] => intMatRankAuxClean cols' (rows.map (fun r => r.drop 1))
      | pRow :: rest =>
        let p := match pRow with | [] => 1 | x :: _ => x
        let zeroRows := rows.filter (fun r => match r with | [] => true | x :: _ => intEq x 0)
        let reduced := (rest ++ zeroRows).map (fun r =>
          match r with
          | [] => []
          | r0 :: rs => if intEq r0 0 then rs else intElimStep pRow p r)
        1 + intMatRankAuxClean cols' reduced

def macaulayMatrixRank (socle : List (List Nat × Int)) (d : Nat) : Nat :=
  let matRows := (macaulayPairingMatrix socle d).filter (fun r => r.any (fun x => intNe x 0))
  match matRows with
  | [] => 0
  | r0 :: _ =>
    let cols := transposeMat r0.length matRows
    let nzCols := cols.filter (fun c => c.any (fun x => intNe x 0))
    match nzCols with
    | [] => 0
    | _ :: _ =>
      let compact := transposeMat matRows.length nzCols
      intMatRankAuxClean nzCols.length compact

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def h31_prim : Nat := binom 11 5 - 6 * binom 6 5

def h22_prim : Nat := (binom 17 5 + 15 * binom 7 5) - (6 * binom 12 5)

def high_support_moduli_counts : List Nat := [(binom 6 4) * 10, (binom 6 5) * 5, binom 6 6]

def high_support_moduli_dim : Nat := high_support_moduli_counts.foldl (· + ·) 0

def all_perfect_matchings_6 : List (List (Nat × Nat)) :=
  [1, 2, 3, 4, 5].foldl (fun acc b =>
    match [1, 2, 3, 4, 5].filter (fun x => x != b) with
    | [] => acc
    | r0 :: t0 => match t0 with
      | [] => acc
      | r1 :: t1 => match t1 with
        | [] => acc
        | r2 :: t2 => match t2 with
          | [] => acc
          | r3 :: t3 => match t3 with
            | [] =>
              acc ++ [
                [(0, b), (r0, r1), (r2, r3)],
                [(0, b), (r0, r2), (r1, r3)],
                [(0, b), (r0, r3), (r1, r2)]
              ]
            | _ :: _ => acc
  ) []

def getNatAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getNatAt xs k

def matchingSatisfied (m : Nat) (a : List Nat) (matching : List (Nat × Nat)) : Bool :=
  matching.all (fun (i, j) => getNatAt a i + getNatAt a j == m)

def matchingSatisfactionCount (m : Nat) (a : List Nat) : Nat :=
  (all_perfect_matchings_6.filter (matchingSatisfied m a)).length

def band1_sorted_tuples_m6 : List (List Nat) :=
  (sortedHodge22Tuples 6).filter (isBand1CompletePairs 6)

def band1_count_by_multiplicity (k : Nat) : Nat :=
  (band1_sorted_tuples_m6.filter (fun a => matchingSatisfactionCount 6 a == k)).foldl
    (fun acc a => acc + s6OrbitSize a) 0

def band1_multiplicity_pairs : List (Nat × Nat) :=
  [1, 2, 3, 6, 15].map (fun k => (k, band1_count_by_multiplicity k))

/-- Total union size (active support) covered by a list of `(multiplicity, count)` buckets. -/
def activeSupport : List (Nat × Nat) → Nat
  | [] => 0
  | (_, n) :: rest => n + activeSupport rest

/-- Total incidence sum `∑ k * n_k` across all blocks in a bucket list. -/
def totalIncidences : List (Nat × Nat) → Nat
  | [] => 0
  | (k, n) :: rest => k * n + totalIncidences rest

/-- Multi-block collision excess measuring overlap beyond the active union. -/
def collisionExcess (buckets : List (Nat × Nat)) : Nat :=
  totalIncidences buckets - activeSupport buckets

/-- Dimension of the uncovered residual form left behind inside `ambientDim`. -/
def residualFormDim (ambientDim : Nat) (buckets : List (Nat × Nat)) : Nat :=
  ambientDim - activeSupport buckets

private theorem nat_mul_ge_self (k n : Nat) (hk : 1 ≤ k) : n ≤ k * n := by
  cases k with
  | zero => exact absurd hk (Nat.not_le_of_gt (Nat.zero_lt_one))
  | succ k' =>
    rw [Nat.succ_mul, Nat.add_comm]
    exact Nat.le_add_right n (k' * n)

private theorem blt_zero_to_one_le (k : Nat) (h : Nat.blt 0 k = true) : 1 ≤ k := by
  cases k with
  | zero => contradiction
  | succ k' => exact Nat.succ_le_succ (Nat.zero_le k')

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | contradiction

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- For any bucket list with every multiplicity `k >= 1`, `activeSupport <= totalIncidences`. -/
theorem activeSupport_le_totalIncidences (buckets : List (Nat × Nat))
    (h : buckets.all (fun p => Nat.blt 0 p.1) = true) :
    activeSupport buckets ≤ totalIncidences buckets := by
  induction buckets with
  | nil => exact Nat.le_refl 0
  | cons p rest ih =>
    cases p with
    | mk k n =>
      dsimp [List.all] at h
      have hk1 : 1 ≤ k := blt_zero_to_one_le k (bool_and_left h)
      have ih' : activeSupport rest ≤ totalIncidences rest := ih (bool_and_right h)
      exact Nat.add_le_add (nat_mul_ge_self k n hk1) ih'

private theorem nat_add_sub_of_le (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  induction a generalizing b with
  | zero => exact Nat.zero_add b
  | succ a' ih =>
    cases b with
    | zero => exact absurd h (Nat.not_le_of_gt (Nat.zero_lt_succ a'))
    | succ b' =>
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact congrArg Nat.succ (ih b' (Nat.le_of_succ_le_succ h))

/-- Universal sieve identity: `activeSupport + collisionExcess = totalIncidences`. -/
theorem activeSupport_add_collisionExcess (buckets : List (Nat × Nat))
    (h : buckets.all (fun p => Nat.blt 0 p.1) = true) :
    activeSupport buckets + collisionExcess buckets = totalIncidences buckets :=
  nat_add_sub_of_le (activeSupport buckets) (totalIncidences buckets)
    (activeSupport_le_totalIncidences buckets h)

/-- Universal residual form identity: `activeSupport + residualFormDim = ambientDim`. -/
theorem activeSupport_add_residualFormDim (ambientDim : Nat) (buckets : List (Nat × Nat))
    (h : activeSupport buckets ≤ ambientDim) :
    activeSupport buckets + residualFormDim ambientDim buckets = ambientDim :=
  nat_add_sub_of_le (activeSupport buckets) ambientDim h

/-- Multiplicity buckets for the 20 coordinate 2-planes in `R^6(F_0)`. -/
def twentyPlaneBuckets : List (Nat × Nat) := [(1, 200), (4, 45)]

/-- Unified three-level cyclotomic incidence sieve and residual form master certificate. -/
theorem cyclotomic_incidence_residual_form_master_cert :
    (totalIncidences band1_multiplicity_pairs == 1875 &&
     activeSupport band1_multiplicity_pairs == 1001 &&
     collisionExcess band1_multiplicity_pairs == 874 &&
     residualFormDim h22_prim band1_multiplicity_pairs == 750 &&
     residualFormDim h22_prim band1_multiplicity_pairs ==
       fermat_band2_count 6 + fermat_band3_count 6) ∧
    (totalIncidences twentyPlaneBuckets == 380 &&
     activeSupport twentyPlaneBuckets == 245 &&
     collisionExcess twentyPlaneBuckets == 135 &&
     residualFormDim h31_prim twentyPlaneBuckets == 181 &&
     residualFormDim h31_prim twentyPlaneBuckets == high_support_moduli_dim) ∧
    ((monomials4 2).length - macaulayMatrixRank planeSoclePoly 2 == 4 &&
     (monomials4 2).length - macaulayMatrixRank quadricJetSoclePoly 2 == 1) :=
  ⟨rfl, rfl, rfl⟩

end Combinatorics.IncidenceSieve
