import Mathlib.Data.Nat.Notation

-- 1.3. Functions and Definitions

def hello := "Hello"

#eval hello

def lean : String := "Lean"


#eval String.append hello (String.append " " lean)

-- 1.3.1. Defining Functions
def add1 (n : Nat) : Nat := n + 1

#check add1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval maximum (5 + 8) (2 * 7)


-- 1.3.1.1. Exercises🔗
-- Define the function joinStringsWith with type String → String → String → String that
-- creates a new string by placing its first argument between its second and third arguments.
-- joinStringsWith ", " "one" "and another" should evaluate to "one, and another".

def joinStringsWith (first: String) (second : String) (third: String) : String :=
  String.append second (String.append first third)

#eval joinStringsWith ", " "one" "and another"

-- What is the type of joinStringsWith ": "? Check your answer with Lean.

#check joinStringsWith

-- Define a function volume with type Nat → Nat → Nat → Nat that computes the volume of a
-- rectangular prism with the given height, width, and depth.

def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  height * width * depth


-- 1.3.2. Defining Types

def Str : Type := String

def aStr : Str := "This is a string."

def a : ℕ := 3

#check a
