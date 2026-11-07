module

import Mathlib.Tactic.Linter.DecapitaliseName

#guard "AB5OfSize".lowerStart == "ab5OfSize"
#guard "Measurable".lowerStart  == "measurable"
#guard "LE".lowerStart  == "le"
#guard "LE'".lowerStart  == "le'"
#guard "AB4ODFoo".lowerStart == "ab4ODFoo"
#guard "TFAE".lowerStart == "tfae"
#guard "ιOrZero".lowerStart == "ιOrZero"

-- non-ascii first character
#guard "ΓIso".lowerStart  == "ΓIso"
#guard "π".lowerStart  == "π"
#guard "Π".lowerStart  == "Π"
#guard "ωCPO".lowerStart == "ωCPO"
#guard "εNFA".lowerStart == "εNFA"

-- some manual exceptions
#guard "SL2Z".lowerStart == "SL2Z"
#guard "L1Norm".lowerStart == "L1Norm"
#guard "LpNorm".lowerStart == "LpNorm"
#guard "Gammaℝ".lowerStart == "Gammaℝ"
#guard "Icc".lowerStart == "Icc"
#guard "Ioi".lowerStart == "Ioi"
#guard "Icosahedron".lowerStart == "icosahedron"
#guard "Iotop".lowerStart == "Iotop"
#guard "Ixx".lowerStart == "Ixx"

-- names with an abbreviation
#guard "NNNorm".lowerStart  == "nnNorm"
#guard "SDiff".lowerStart  == "sDiff"
#guard "HImp".lowerStart  == "hImp"
#guard "ENNReal".lowerStart  == "ennReal"
#guard "HNot".lowerStart  == "hNot"
#guard "SMul".lowerStart  == "sMul"
#guard "HSMul".lowerStart  == "hsMul"
#guard "ZSMul".lowerStart  == "zsMul"
#guard "HVAdd".lowerStart  == "hvAdd"
#guard "HAppend".lowerStart  == "hAppend"

-- single letters followed by not a latin letter
#guard "L₀X₂ToP".lowerStart == "L₀X₂ToP"
#guard "L1Space".lowerStart == "L1Space"
#guard "T1Space".lowerStart == "T1Space"
#guard "T2Space".lowerStart == "t2Space" -- TODO: discuss
#guard "E6".lowerStart == "e6" -- TODO: discuss (`admissable_E6`)
#guard "H1OfAutOnUnitsUnique".lowerStart == "H1OfAutOnUnitsUnique"
#guard "H0π".lowerStart == "H0π"
#guard "CC".lowerStart == "cc"
#guard "E6".lowerStart == "E6"

-- isolated single capital letter
#guard "X".lowerStart == "X"
