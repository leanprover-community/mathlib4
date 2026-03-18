/- Problem 5   -/
/- Project Euler Problem 5: Smallest multiple
2520 is the smallest number that can be divided by each of the numbers from 1 to 10 without any remainder.
What is the smallest positive number that is evenly divisible by all of the numbers from 1 to 20?
 -/
/- #eval List.range' 1 21


#eval [2, 3, 4, 5].foldl Nat.lcm 1   -- 60
 -/
def smallestMultiple (n : Nat) : Nat :=
  List.range' 1 (n + 1)
  |> List.foldl Nat.lcm 1

#eval smallestMultiple 20 -- 232792560
