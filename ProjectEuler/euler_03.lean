/- Project Euler Problem 3: Largest prime factor
The prime factors of 13195 are 5, 7, 13 and 29.
What is the largest prime factor of the number 600851475143 ?
 -/

def primeFactors (n : Nat) : List Nat :=
  let rec factors (fuel n d : Nat) : List Nat :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if n < 2 then []
      else if n % d == 0 then d :: factors fuel (n / d) d
      else factors fuel n (d + 1)
  factors n n 2

#eval primeFactors 13195

#eval primeFactors 600851475143

#check primeFactors 13195 == [5, 7, 13, 29]


def largestPrimeFactor (n : Nat) : Option Nat :=
  (primeFactors n).reverse.head?

#eval (largestPrimeFactor 600851475143)

def solution (opt : Option Nat) : Nat :=
match opt with
| some x => x   -- use x here
| none   => 0      -- provide a fallback

#eval solution (largestPrimeFactor 600851475143)
