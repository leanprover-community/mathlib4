/- Problem 4   -/
/- Project Euler Problem 4: Largest palindrome product
A palindromic number reads the same both ways. The largest palindrome made from the product of two 2-digit numbers is 9009 = 91 × 99.
Find the largest palindrome made from the product of two 3-digit numbers.
 -/

def reverseString (s : String) : String :=
  String.ofList (List.reverse s.toList)

-- Example usage:
#eval reverseString "hello"
-- Output: "olleh"


def isPalindrome (n : Nat) : Bool :=
  let s := toString n
  s == reverseString s

-- Example usage:
#eval isPalindrome 12321
-- Output: true


def largestPalindromeProduct (n : Nat): Nat :=
  let products := List.range n
    |> List.flatMap (
      fun x => List.range' x (n - x + 1)
      |> List.map (fun y => x * y)
      )
products
    |> List.filter isPalindrome
    |> List.foldl max 0

#eval largestPalindromeProduct 1_000 --  906609

def ls := [1,2,3]

#eval ls.max (by decide)
