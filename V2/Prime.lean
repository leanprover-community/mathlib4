import MetaCompute.V2.Certify

-- basic certificates
example : Nat.Prime 19 := by pratt mathematica {19, 2, {2, {3, 2, {2}}}}
example : Nat.Prime 37 := by pratt mathematica {37, 2, {2, {3, 2, {2}}}}
example : Nat.Prime 53 := by pratt mathematica {53, 2, {2, {13, 2, {2, {3, 2, {2}}}}}}
example : Nat.Prime 97 := by pratt mathematica {97, 5, {2, {3, 2, {2}}}}








-- hide the really small primes
example : Nat.Prime 101 := by pratt mathematica {101, 2, {2, 5}}
example : Nat.Prime 103 := by pratt mathematica {103, 5, {2, 3, {17, 3, {2}}}}
example : Nat.Prime 103 := by pratt mathematica {103, 5, {2, 3, 17}}

example : Nat.Prime 107 := by pratt mathematica {107, 2, {2, {53, 2, {2, {13, 2, {2, {3, 2, {2}}}}}}}}
example : Nat.Prime 107 := by pratt mathematica {107, 2, {2, 53}}

-- the tactic helps you find the certificate (a bit)
example : Nat.Prime 109 := by pratt mathematica {109, 6, {2, 3}}
example : Nat.Prime 113 := by pratt mathematica {113, 3, {2, 7}}
example : Nat.Prime 127 := by pratt mathematica {127, 3, {2, 3, 7}}
example : Nat.Prime 1270249 := by
  pratt mathematica {1270249, 11, {2, {3, 2, {2}}, {7, 3, {2, {3, 2, {2}}}}, {7561,
   13, {2, {3, 2, {2}}, {5, 2, {2}}, {7, 3, {2, {3, 2, {2}}}}}}}}

-- or you can ask mathematica!
example : Nat.Prime 1873 := by pratt mathematica {1873, 10, {2, 3, 13}}
example : Nat.Prime 1873 := by pratt mathematica {1873, 10, {2, 3, 13}}

example : Nat.Prime 351952158019564383015880113162140133230953767603869 := by
  sorry
