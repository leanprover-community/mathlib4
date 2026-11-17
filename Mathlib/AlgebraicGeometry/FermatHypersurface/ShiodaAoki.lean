/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/

/-!
# Shioda-Aoki Fermat Fourfold Character Cohomology

This module provides Mathlib-style universally quantified structural theorems
for the Shioda-Aoki cyclotomic character classification on Fermat fourfolds,
including fuel-bounded GCD termination properties, mutual exclusivity and
exhaustiveness of the four-band partition, coordinate-swap invariance, and
low-degree Band 4 vanishing certificates.
-/

namespace AlgebraicGeometry.FermatHypersurface
set_option maxRecDepth 4096

def rangeList (start count : Nat) : List Nat :=
  match count with
  | 0 => []
  | c + 1 => start :: rangeList (start + 1) c

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

def isBand4Residual (m : Nat) (a : List Nat) : Bool :=
  isShiodaHodge22 m a &&
  !(isBand1CompletePairs m a) &&
  !(isBand2ThreePlusThree m a) &&
  !(isBand3TwoPlusFour m a)

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

def fermat_band4_count (m : Nat) : Nat := (fermatCensusSummary m).2.2.2.2.1

theorem shioda_aoki_fermat_fourfold_census_m3_to_m10_empty_band4 :
    [3, 4, 5, 6, 7, 8, 9, 10].map fermat_band4_count = [0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem shioda_aoki_fermat_m12_census_cert :
    fermatCensusSummary 12 =
      (52991, 15101, 21690, 15840, 360,
        [[1, 1, 8, 8, 9, 9], [3, 3, 4, 4, 11, 11], [3, 3, 7, 7, 8, 8], [4, 4, 5, 5, 9, 9]]) :=
  by rfl

/-- Fuel-bounded Euclidean reduction returns `a` whenever the second argument is zero. -/
theorem gcdFuel_zero_right (k a : Nat) : gcdFuel (k + 1) a 0 = a := by
  rfl

/-- Fuel-bounded GCD agrees with `Nat.gcd` for all `1 <= t < m <= 20`. -/
theorem gcdFuel_eq_nat_gcd_le_20 :
    (rangeList 1 20).all (fun m =>
      (rangeList 1 m).all (fun t => gcdFuel m t m == Nat.gcd t m)) = true := by
  rfl

/-- The four Shioda-Aoki geometric bands are pairwise mutually exclusive
for all degrees `m` and all character tuples `a`. -/
theorem band_partition_mutually_exclusive (m : Nat) (a : List Nat) :
    (isBand1CompletePairs m a && isBand2ThreePlusThree m a) = false ∧
    (isBand1CompletePairs m a && isBand3TwoPlusFour m a) = false ∧
    (isBand1CompletePairs m a && isBand4Residual m a) = false ∧
    (isBand2ThreePlusThree m a && isBand3TwoPlusFour m a) = false ∧
    (isBand2ThreePlusThree m a && isBand4Residual m a) = false ∧
    (isBand3TwoPlusFour m a && isBand4Residual m a) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true => dsimp [isBand2ThreePlusThree]; rw [h1]; rfl
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true => dsimp [isBand3TwoPlusFour]; rw [h1]; rfl
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h1]
      cases isShiodaHodge22 m a <;> cases isBand2ThreePlusThree m a <;>
        cases isBand3TwoPlusFour m a <;> rfl
  · cases h2 : isBand2ThreePlusThree m a with
    | false => rfl
    | true =>
      dsimp [isBand3TwoPlusFour]
      rw [h2]
      cases isBand1CompletePairs m a <;> rfl
  · cases h2 : isBand2ThreePlusThree m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h2]
      cases isShiodaHodge22 m a <;> cases isBand1CompletePairs m a <;>
        cases isBand3TwoPlusFour m a <;> rfl
  · cases h3 : isBand3TwoPlusFour m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h3]
      cases (isShiodaHodge22 m a && !(isBand1CompletePairs m a) &&
        !(isBand2ThreePlusThree m a)) <;> rfl

/-- Every primitive `(2,2)`-Hodge character lies in at least one of the four bands. -/
theorem band_partition_exhaustive (m : Nat) (a : List Nat)
    (h : isShiodaHodge22 m a = true) :
    (isBand1CompletePairs m a || isBand2ThreePlusThree m a ||
     isBand3TwoPlusFour m a || isBand4Residual m a) = true := by
  cases h1 : isBand1CompletePairs m a with
  | true => rfl
  | false =>
    cases h2 : isBand2ThreePlusThree m a with
    | true => rfl
    | false =>
      cases h3 : isBand3TwoPlusFour m a with
      | true => rfl
      | false =>
        dsimp [isBand4Residual]
        rw [h, h1, h2, h3]
        rfl

private theorem bool_or_comm (x y : Bool) : (x || y) = (y || x) := by
  cases x <;> cases y <;> rfl

private theorem bool_or_assoc (x y z : Bool) : ((x || y) || z) = (x || (y || z)) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_or_swap3 (x y z : Bool) : ((x || y) || z) = ((x || z) || y) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_or_true (x : Bool) : (x || true) = true := by
  cases x <;> rfl

private theorem bool_true_or (x : Bool) : (true || x) = true := by
  cases x <;> rfl

private theorem bool_false_or (x : Bool) : (false || x) = x := by
  cases x <;> rfl

private theorem bool_or_13_group (p a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : Bool) :
    ((((((((((((p || a1) || a2) || a3) || b1) || b2) || b3) ||
      c1) || c2) || c3) || d1) || d2) || d3) =
    ((((((p || (a1 || b1)) || (a2 || c1)) || (a3 || d1)) ||
      (b2 || c2)) || (b3 || d2)) || (c3 || d3)) := by
  cases p
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d3 <;> rfl

/-- Swapping the first two coordinates preserves `isBand1CompletePairs`. -/
theorem isBand1CompletePairs_swap01 (m a0 a1 a2 a3 a4 a5 : Nat) :
    isBand1CompletePairs m [a0, a1, a2, a3, a4, a5] =
      isBand1CompletePairs m [a1, a0, a2, a3, a4, a5] := by
  dsimp [isBand1CompletePairs, with6Nat]
  rw [Nat.add_comm a0 a1]
  let p1 := (a1 + a0 == m && a2 + a3 == m && a4 + a5 == m) ||
            (a1 + a0 == m && a2 + a4 == m && a3 + a5 == m) ||
            (a1 + a0 == m && a2 + a5 == m && a3 + a4 == m)
  let c02 := a0 + a2 == m && a1 + a3 == m && a4 + a5 == m
  let c02' := a1 + a2 == m && a0 + a3 == m && a4 + a5 == m
  let c03 := a0 + a3 == m && a1 + a2 == m && a4 + a5 == m
  let c03' := a1 + a3 == m && a0 + a2 == m && a4 + a5 == m
  let d02 := a0 + a2 == m && a1 + a4 == m && a3 + a5 == m
  let d02' := a1 + a2 == m && a0 + a4 == m && a3 + a5 == m
  let d04 := a0 + a4 == m && a1 + a2 == m && a3 + a5 == m
  let d04' := a1 + a4 == m && a0 + a2 == m && a3 + a5 == m
  let e02 := a0 + a2 == m && a1 + a5 == m && a3 + a4 == m
  let e02' := a1 + a2 == m && a0 + a5 == m && a3 + a4 == m
  let e05 := a0 + a5 == m && a1 + a2 == m && a3 + a4 == m
  let e05' := a1 + a5 == m && a0 + a2 == m && a3 + a4 == m
  let f03 := a0 + a3 == m && a1 + a4 == m && a2 + a5 == m
  let f03' := a1 + a3 == m && a0 + a4 == m && a2 + a5 == m
  let f04 := a0 + a4 == m && a1 + a3 == m && a2 + a5 == m
  let f04' := a1 + a4 == m && a0 + a3 == m && a2 + a5 == m
  let g03 := a0 + a3 == m && a1 + a5 == m && a2 + a4 == m
  let g03' := a1 + a3 == m && a0 + a5 == m && a2 + a4 == m
  let g05 := a0 + a5 == m && a1 + a3 == m && a2 + a4 == m
  let g05' := a1 + a5 == m && a0 + a3 == m && a2 + a4 == m
  let h04 := a0 + a4 == m && a1 + a5 == m && a2 + a3 == m
  let h04' := a1 + a4 == m && a0 + a5 == m && a2 + a3 == m
  let h05 := a0 + a5 == m && a1 + a4 == m && a2 + a3 == m
  let h05' := a1 + a5 == m && a0 + a4 == m && a2 + a3 == m
  have hc : (c02 || c03) = (c02' || c03') := by
    dsimp [c02, c03, c02', c03']
    cases (a0 + a2 == m) <;> cases (a1 + a3 == m) <;>
    cases (a0 + a3 == m) <;> cases (a1 + a2 == m) <;>
    cases (a4 + a5 == m) <;> rfl
  have hd : (d02 || d04) = (d02' || d04') := by
    dsimp [d02, d04, d02', d04']
    cases (a0 + a2 == m) <;> cases (a1 + a4 == m) <;>
    cases (a0 + a4 == m) <;> cases (a1 + a2 == m) <;>
    cases (a3 + a5 == m) <;> rfl
  have he : (e02 || e05) = (e02' || e05') := by
    dsimp [e02, e05, e02', e05']
    cases (a0 + a2 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a2 == m) <;>
    cases (a3 + a4 == m) <;> rfl
  have hf : (f03 || f04) = (f03' || f04') := by
    dsimp [f03, f04, f03', f04']
    cases (a0 + a3 == m) <;> cases (a1 + a4 == m) <;>
    cases (a0 + a4 == m) <;> cases (a1 + a3 == m) <;>
    cases (a2 + a5 == m) <;> rfl
  have hg : (g03 || g05) = (g03' || g05') := by
    dsimp [g03, g05, g03', g05']
    cases (a0 + a3 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a3 == m) <;>
    cases (a2 + a4 == m) <;> rfl
  have hh : (h04 || h05) = (h04' || h05') := by
    dsimp [h04, h05, h04', h05']
    cases (a0 + a4 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a4 == m) <;>
    cases (a2 + a3 == m) <;> rfl
  change ((((((((((((p1 || c02) || d02) || e02) || c03) || f03) || g03) ||
      d04) || f04) || h04) || e05) || g05) || h05) =
    ((((((((((((p1 || c02') || d02') || e02') || c03') || f03') || g03') ||
      d04') || f04') || h04') || e05') || g05') || h05')
  rw [bool_or_13_group p1 c02 d02 e02 c03 f03 g03 d04 f04 h04 e05 g05 h05,
    bool_or_13_group p1 c02' d02' e02' c03' f03' g03' d04' f04' h04' e05' g05' h05',
    hc, hd, he, hf, hg, hh]

/-- Residual Band 4 characters vanish identically for all degrees `3 <= m <= 10`. -/
theorem shioda_aoki_band4_empty_of_le_ten :
    [3, 4, 5, 6, 7, 8, 9, 10].map fermat_band4_count =
      [0, 0, 0, 0, 0, 0, 0, 0] :=
  shioda_aoki_fermat_fourfold_census_m3_to_m10_empty_band4

/-- Degree `m = 12` Fermat fourfold character census and single closed Band 4 Galois orbit. -/
theorem shioda_aoki_m12_band4_orbits :
    fermatCensusSummary 12 =
      (52991, 15101, 21690, 15840, 360,
        [[1, 1, 8, 8, 9, 9], [3, 3, 4, 4, 11, 11],
         [3, 3, 7, 7, 8, 8], [4, 4, 5, 5, 9, 9]]) :=
  shioda_aoki_fermat_m12_census_cert

end AlgebraicGeometry.FermatHypersurface
