#! /usr/bin/env -S sed -i -f
#
# Rename `MulAction` to `MonoidAction` and `AddAction` to `AddMonoidAction`.
#
#     find Mathlib Archive Counterexamples MathlibTest Wanted -name '*.lean' -print0 \
#       | xargs -0 sed -i -f scripts/monoidaction_rename.sed
#
# The two halves below are a mask/restore pair: names that merely *contain* the string
# `MulAction` are first rewritten with `MulAction` replaced by the placeholder `PROTECTMUL`
# (which no longer matches), then the real rename runs, then the placeholders are put back.
# `PROTECTmul`, `PROTECTADD` and `PROTECTadd` do the same for the other three spellings.

# Leave this rename's own deprecated aliases alone: their whole point is the old name.
/(since := "2026-09-02")/,/^$/ b

# --- mask: module paths, whose files keep their old names --------------------------------
s/Mathlib\.Algebra\.GradedMulAction/Mathlib.Algebra.GradedPROTECTMUL/g
s/Mathlib\.Algebra\.Group\.Submonoid\.MulAction/Mathlib.Algebra.Group.Submonoid.PROTECTMUL/g
s/Mathlib\.Analysis\.Normed\.MulAction/Mathlib.Analysis.Normed.PROTECTMUL/g
s/Mathlib\.Topology\.Algebra\.ConstMulAction/Mathlib.Topology.Algebra.ConstPROTECTMUL/g
s/Mathlib\.Topology\.Algebra\.UniformMulAction/Mathlib.Topology.Algebra.UniformPROTECTMUL/g
s/Mathlib\.Topology\.Algebra\.MulAction/Mathlib.Topology.Algebra.PROTECTMUL/g

# --- mask: other classes that merely share the string ------------------------------------
s/MulActionWithZero/PROTECTMULWithZero/g
s/mulActionWithZero/PROTECTmulWithZero/g
s/AddActionWithZero/PROTECTADDWithZero/g
s/addActionWithZero/PROTECTaddWithZero/g
s/MulActionSemiHom/PROTECTMULSemiHom/g
s/mulActionSemiHom/PROTECTmulSemiHom/g
s/AddActionSemiHom/PROTECTADDSemiHom/g
s/addActionSemiHom/PROTECTaddSemiHom/g
s/DistribMulAction/DistribPROTECTMUL/g
s/distribMulAction/distribPROTECTMUL/g
s/DistribAddAction/DistribPROTECTADD/g
s/distribAddAction/distribPROTECTADD/g
s/MulActionHom/PROTECTMULHom/g
s/mulActionHom/PROTECTmulHom/g
s/AddActionHom/PROTECTADDHom/g
s/addActionHom/PROTECTaddHom/g
s/SubMulAction/SubPROTECTMUL/g
s/subMulAction/subPROTECTMUL/g
s/SubAddAction/SubPROTECTADD/g
s/subAddAction/subPROTECTADD/g

# --- the rename --------------------------------------------------------------------------
s/MulAction/MonoidAction/g
s/mulAction/monoidAction/g
s/AddAction/AddMonoidAction/g
s/addAction/addMonoidAction/g

# --- restore ------------------------------------------------------------------------------
s/PROTECTMUL/MulAction/g
s/PROTECTmul/mulAction/g
s/PROTECTADD/AddAction/g
s/PROTECTadd/addAction/g
