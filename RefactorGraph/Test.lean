import RefactorGraph.DAG

open Lean Std

def runTestsBasic : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 1: Simple chain A → B → C
  stderr.putStrLn "Test 1: Chain graph A → B → C"
  let g1 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"

  let ancsC := g1.ancestors "C"
  assert! ancsC.contains "A" && ancsC.contains "B" && ancsC.size == 2
  stderr.putStrLn "  ✓ ancestors(C) = {A, B}"

  -- Test 2: Diamond A → B, A → C, B → D, C → D
  stderr.putStrLn "Test 2: Diamond graph"
  let g2 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"

  let ancsD := g2.ancestors "D"
  assert! ancsD.contains "A" && ancsD.contains "B" && ancsD.contains "C" && ancsD.size == 3
  stderr.putStrLn "  ✓ ancestors(D) = {A, B, C}"

  -- Test 3: allAncestors matches individual ancestors calls
  stderr.putStrLn "Test 3: allAncestors consistency"
  let allAncs := g2.allAncestors
  for node in ["A", "B", "C", "D"] do
    let expected := g2.ancestors node
    let actual := allAncs.getD node {}
    assert! expected.size == actual.size
    for e in expected do
      assert! actual.contains e
  stderr.putStrLn "  ✓ allAncestors matches individual ancestors calls"

  -- Test 4: Transitive reduction removes A → C from A → B → C, A → C
  stderr.putStrLn "Test 4: Transitive reduction"
  let g3 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"

  let g3reduced := g3.transitiveReduction
  let parentsOfC := g3reduced.parent.getD "C" {}
  assert! !parentsOfC.contains "A" && parentsOfC.contains "B" && parentsOfC.size == 1
  stderr.putStrLn "  ✓ Transitive edge A → C removed"

  -- Test 5: Diamond with transitive edges
  stderr.putStrLn "Test 5: Diamond with all edges"
  let g4 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"

  let g4reduced := g4.transitiveReduction
  let parentsOfD := g4reduced.parent.getD "D" {}
  assert! !parentsOfD.contains "A" && parentsOfD.contains "B" && parentsOfD.contains "C"
  stderr.putStrLn "  ✓ Transitive edge A → D removed in diamond"

  -- Test 6: No false removals
  stderr.putStrLn "Test 6: Non-transitive edges preserved"
  let g5 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"

  let g5reduced := g5.transitiveReduction
  let parentsOfB := g5reduced.parent.getD "B" {}
  let parentsOfC5 := g5reduced.parent.getD "C" {}
  assert! parentsOfB.size == 1 && parentsOfB.contains "A"
  assert! parentsOfC5.size == 1 && parentsOfC5.contains "A"
  stderr.putStrLn "  ✓ Non-transitive edges preserved"

def runTestsEdgeCases : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 7: Empty graph
  stderr.putStrLn "Test 7: Empty graph"
  let gEmpty : DAG String := DAG.empty
  assert! (gEmpty.ancestors "X").size == 0
  assert! gEmpty.allAncestors.size == 0
  let gEmptyReduced := gEmpty.transitiveReduction
  assert! gEmptyReduced.parent.size == 0
  stderr.putStrLn "  ✓ Empty graph handled correctly"

  -- Test 8: Single node with no edges
  stderr.putStrLn "Test 8: Single isolated node"
  let gSingle : DAG String := DAG.empty.insert "A" {}
  assert! (gSingle.ancestors "A").size == 0
  let allAncsSingle := gSingle.allAncestors
  assert! (allAncsSingle.getD "A" {}).size == 0
  stderr.putStrLn "  ✓ Single isolated node handled correctly"

  -- Test 9: removeEdge functionality
  stderr.putStrLn "Test 9: removeEdge functionality"
  let gRemove : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "C" "B"

  let parentsB_before := gRemove.parent.getD "B" {}
  assert! parentsB_before.size == 2

  let gAfterRemove := gRemove.removeEdge "A" "B"
  let parentsB_after := gAfterRemove.parent.getD "B" {}
  assert! parentsB_after.size == 1 && parentsB_after.contains "C" && !parentsB_after.contains "A"

  let gAfterRemove2 := gAfterRemove.removeEdge "X" "B"
  let parentsB_after2 := gAfterRemove2.parent.getD "B" {}
  assert! parentsB_after2.size == 1
  stderr.putStrLn "  ✓ removeEdge works correctly"

  -- Test 10: Ancestors of non-existent node
  stderr.putStrLn "Test 10: Ancestors of non-existent node"
  let g2 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
  let ancsNonExistent := g2.ancestors "NonExistent"
  assert! ancsNonExistent.size == 0
  stderr.putStrLn "  ✓ Non-existent node returns empty ancestors"

def runTestsChains : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 11: Long chain A → B → C → D → E → F
  stderr.putStrLn "Test 11: Long chain (6 nodes)"
  let gLongChain : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "D" "E"
    |>.insertEdge "E" "F"

  let ancsF := gLongChain.ancestors "F"
  assert! ancsF.size == 5
  assert! ancsF.contains "A" && ancsF.contains "B" && ancsF.contains "C"
  assert! ancsF.contains "D" && ancsF.contains "E"
  let gLongChainReduced := gLongChain.transitiveReduction
  let parentsOfF := gLongChainReduced.parent.getD "F" {}
  assert! parentsOfF.size == 1 && parentsOfF.contains "E"
  stderr.putStrLn "  ✓ Long chain handled correctly"

  -- Test 12: Long chain with skip edges (all transitive)
  stderr.putStrLn "Test 12: Long chain with transitive skip edges"
  let gSkipChain : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "C"
    |>.insertEdge "A" "D"
    |>.insertEdge "B" "D"

  let gSkipReduced := gSkipChain.transitiveReduction
  let parentsOfD_skip := gSkipReduced.parent.getD "D" {}
  assert! parentsOfD_skip.size == 1 && parentsOfD_skip.contains "C"
  let parentsOfC_skip := gSkipReduced.parent.getD "C" {}
  assert! parentsOfC_skip.size == 1 && parentsOfC_skip.contains "B"
  stderr.putStrLn "  ✓ Skip edges correctly removed"

  -- Test 13: Deep hierarchy with partial transitive edges
  stderr.putStrLn "Test 13: Deep hierarchy with partial shortcuts"
  let gDeep : DAG String := DAG.empty
    |>.insertEdge "L0" "L1"
    |>.insertEdge "L1" "L2"
    |>.insertEdge "L2" "L3"
    |>.insertEdge "L3" "L4"
    |>.insertEdge "L0" "L2"
    |>.insertEdge "L1" "L3"
    |>.insertEdge "L0" "L4"

  let gDeepReduced := gDeep.transitiveReduction
  let parentsL4 := gDeepReduced.parent.getD "L4" {}
  let parentsL3 := gDeepReduced.parent.getD "L3" {}
  let parentsL2 := gDeepReduced.parent.getD "L2" {}
  assert! parentsL4.size == 1 && parentsL4.contains "L3"
  assert! parentsL3.size == 1 && parentsL3.contains "L2"
  assert! parentsL2.size == 1 && parentsL2.contains "L1"
  stderr.putStrLn "  ✓ Deep hierarchy with shortcuts handled correctly"

def runTestsMultipleRoots : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 14: Multiple roots
  stderr.putStrLn "Test 14: Multiple roots converging"
  let gMultiRoot : DAG String := DAG.empty
    |>.insertEdge "R1" "A"
    |>.insertEdge "R2" "A"
    |>.insertEdge "R3" "A"
    |>.insertEdge "A" "B"

  let ancsB_multi := gMultiRoot.ancestors "B"
  assert! ancsB_multi.size == 4
  assert! ancsB_multi.contains "R1" && ancsB_multi.contains "R2"
  assert! ancsB_multi.contains "R3" && ancsB_multi.contains "A"
  let gMultiRootReduced := gMultiRoot.transitiveReduction
  let parentsOfA_multi := gMultiRootReduced.parent.getD "A" {}
  assert! parentsOfA_multi.size == 3
  stderr.putStrLn "  ✓ Multiple roots handled correctly"

  -- Test 15: Node with many parents
  stderr.putStrLn "Test 15: Node with many direct parents"
  let gManyParents : DAG String := DAG.empty
    |>.insertEdge "P1" "Child"
    |>.insertEdge "P2" "Child"
    |>.insertEdge "P3" "Child"
    |>.insertEdge "P4" "Child"
    |>.insertEdge "P5" "Child"

  let ancsChild := gManyParents.ancestors "Child"
  assert! ancsChild.size == 5
  let gManyParentsReduced := gManyParents.transitiveReduction
  let parentsChild := gManyParentsReduced.parent.getD "Child" {}
  assert! parentsChild.size == 5
  stderr.putStrLn "  ✓ Node with many parents handled correctly"

  -- Test 16: Large fan-in then fan-out
  stderr.putStrLn "Test 16: Fan-in to fan-out pattern"
  let gFan : DAG String := DAG.empty
    |>.insertEdge "S1" "M"
    |>.insertEdge "S2" "M"
    |>.insertEdge "S3" "M"
    |>.insertEdge "M" "T1"
    |>.insertEdge "M" "T2"
    |>.insertEdge "M" "T3"

  let ancsT1 := gFan.ancestors "T1"
  assert! ancsT1.size == 4
  assert! ancsT1.contains "M" && ancsT1.contains "S1"
  assert! ancsT1.contains "S2" && ancsT1.contains "S3"
  let gFanReduced := gFan.transitiveReduction
  let parentsT1_fan := gFanReduced.parent.getD "T1" {}
  let parentsM_fan := gFanReduced.parent.getD "M" {}
  assert! parentsT1_fan.size == 1 && parentsT1_fan.contains "M"
  assert! parentsM_fan.size == 3
  stderr.putStrLn "  ✓ Fan-in/fan-out pattern handled correctly"

def runTestsDiamonds : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 17: Wide diamond (multiple paths, same length)
  stderr.putStrLn "Test 17: Wide diamond (4 intermediate nodes)"
  let gWideDiamond : DAG String := DAG.empty
    |>.insertEdge "Top" "M1"
    |>.insertEdge "Top" "M2"
    |>.insertEdge "Top" "M3"
    |>.insertEdge "Top" "M4"
    |>.insertEdge "M1" "Bottom"
    |>.insertEdge "M2" "Bottom"
    |>.insertEdge "M3" "Bottom"
    |>.insertEdge "M4" "Bottom"

  let ancsBottom := gWideDiamond.ancestors "Bottom"
  assert! ancsBottom.size == 5
  let gWideDiamondReduced := gWideDiamond.transitiveReduction
  let parentsOfBottom := gWideDiamondReduced.parent.getD "Bottom" {}
  assert! parentsOfBottom.size == 4
  stderr.putStrLn "  ✓ Wide diamond handled correctly"

  -- Test 18: Nested diamonds
  stderr.putStrLn "Test 18: Nested diamonds"
  let gNestedDiamond : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
    |>.insertEdge "D" "E"
    |>.insertEdge "D" "F"
    |>.insertEdge "E" "G"
    |>.insertEdge "F" "G"

  let ancsG := gNestedDiamond.ancestors "G"
  assert! ancsG.size == 6
  assert! ancsG.contains "A" && ancsG.contains "B" && ancsG.contains "C"
  assert! ancsG.contains "D" && ancsG.contains "E" && ancsG.contains "F"
  stderr.putStrLn "  ✓ Nested diamonds handled correctly"

  -- Test 19: W-shaped graph
  stderr.putStrLn "Test 19: W-shaped graph (two diamonds sharing middle)"
  let gW : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
    |>.insertEdge "C" "E"
    |>.insertEdge "D" "F"
    |>.insertEdge "E" "F"

  let ancsF_w := gW.ancestors "F"
  assert! ancsF_w.size == 5
  assert! ancsF_w.contains "A" && ancsF_w.contains "B" && ancsF_w.contains "C"
  assert! ancsF_w.contains "D" && ancsF_w.contains "E"
  stderr.putStrLn "  ✓ W-shaped graph handled correctly"

  -- Test 20: Triangle with all edges
  stderr.putStrLn "Test 20: Complete triangle (all transitive)"
  let gTriangle : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"

  let gTriangleReduced := gTriangle.transitiveReduction
  let parentsC_tri := gTriangleReduced.parent.getD "C" {}
  assert! parentsC_tri.size == 1 && parentsC_tri.contains "B" && !parentsC_tri.contains "A"
  stderr.putStrLn "  ✓ Triangle transitive edge removed"

def runTestsComplex : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 21: Complex transitive reduction
  stderr.putStrLn "Test 21: Complex graph with multiple transitive edges"
  let gComplex : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "C"
    |>.insertEdge "A" "D"
    |>.insertEdge "B" "D"

  let gComplexReduced := gComplex.transitiveReduction
  let parentsB_complex := gComplexReduced.parent.getD "B" {}
  let parentsC_complex := gComplexReduced.parent.getD "C" {}
  let parentsD_complex := gComplexReduced.parent.getD "D" {}
  assert! parentsB_complex.size == 1 && parentsB_complex.contains "A"
  assert! parentsC_complex.size == 1 && parentsC_complex.contains "B"
  assert! parentsD_complex.size == 1 && parentsD_complex.contains "C"
  stderr.putStrLn "  ✓ Complex transitive edges correctly removed"

  -- Test 22: allAncestors consistency on larger graph
  stderr.putStrLn "Test 22: allAncestors consistency on complex graph"
  let allAncsComplex := gComplex.allAncestors
  for node in ["A", "B", "C", "D"] do
    let expected := gComplex.ancestors node
    let actual := allAncsComplex.getD node {}
    assert! expected.size == actual.size
    for e in expected do
      assert! actual.contains e
  stderr.putStrLn "  ✓ allAncestors consistent on complex graph"

  -- Test 23: Parallel paths of different lengths
  stderr.putStrLn "Test 23: Parallel paths of different lengths"
  let gParallel : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"

  let gParallelReduced := gParallel.transitiveReduction
  let parentsD_par := gParallelReduced.parent.getD "D" {}
  assert! parentsD_par.size == 1 && parentsD_par.contains "C" && !parentsD_par.contains "A"
  stderr.putStrLn "  ✓ Shortcut edge removed in parallel paths"

def runTestsDisconnected : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 24: Disconnected components
  stderr.putStrLn "Test 24: Disconnected components"
  let gDisconnected : DAG String := DAG.empty
    |>.insertEdge "A1" "B1"
    |>.insertEdge "B1" "C1"
    |>.insertEdge "A2" "B2"
    |>.insertEdge "B2" "C2"

  let ancsC1 := gDisconnected.ancestors "C1"
  let ancsC2 := gDisconnected.ancestors "C2"
  assert! ancsC1.size == 2 && ancsC1.contains "A1" && ancsC1.contains "B1"
  assert! ancsC2.size == 2 && ancsC2.contains "A2" && ancsC2.contains "B2"
  assert! !ancsC1.contains "A2" && !ancsC2.contains "A1"
  stderr.putStrLn "  ✓ Disconnected components handled correctly"

  -- Test 25: Verify allAncestors on disconnected graph
  stderr.putStrLn "Test 25: allAncestors on disconnected graph"
  let allAncsDisc := gDisconnected.allAncestors
  for node in ["A1", "B1", "C1", "A2", "B2", "C2"] do
    let expected := gDisconnected.ancestors node
    let actual := allAncsDisc.getD node {}
    assert! expected.size == actual.size
    for e in expected do
      assert! actual.contains e
  stderr.putStrLn "  ✓ allAncestors correct on disconnected graph"

def runTestsLattice : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 26: Binary tree structure
  stderr.putStrLn "Test 26: Binary tree (inverted)"
  let gBinaryTree : DAG String := DAG.empty
    |>.insertEdge "L1" "Root"
    |>.insertEdge "L2" "Root"
    |>.insertEdge "L3" "L1"
    |>.insertEdge "L4" "L1"
    |>.insertEdge "L5" "L2"
    |>.insertEdge "L6" "L2"

  let ancsRoot := gBinaryTree.ancestors "Root"
  assert! ancsRoot.size == 6
  let ancsL1 := gBinaryTree.ancestors "L1"
  assert! ancsL1.size == 2 && ancsL1.contains "L3" && ancsL1.contains "L4"
  stderr.putStrLn "  ✓ Binary tree handled correctly"

  -- Test 27: Lattice structure (meet-semilattice)
  stderr.putStrLn "Test 27: Lattice structure"
  let gLattice : DAG String := DAG.empty
    |>.insertEdge "0" "a"
    |>.insertEdge "0" "b"
    |>.insertEdge "0" "c"
    |>.insertEdge "a" "ab"
    |>.insertEdge "b" "ab"
    |>.insertEdge "a" "ac"
    |>.insertEdge "c" "ac"
    |>.insertEdge "b" "bc"
    |>.insertEdge "c" "bc"
    |>.insertEdge "ab" "abc"
    |>.insertEdge "ac" "abc"
    |>.insertEdge "bc" "abc"

  let ancsAbc := gLattice.ancestors "abc"
  assert! ancsAbc.size == 7
  assert! ancsAbc.contains "0" && ancsAbc.contains "a" && ancsAbc.contains "b"
  assert! ancsAbc.contains "c" && ancsAbc.contains "ab" && ancsAbc.contains "ac"
  assert! ancsAbc.contains "bc"
  stderr.putStrLn "  ✓ Lattice structure handled correctly"

  -- Test 28: Complete bipartite-like structure
  stderr.putStrLn "Test 28: Complete bipartite K3,3 style"
  let gBipartite : DAG String := DAG.empty
    |>.insertEdge "S1" "T1" |>.insertEdge "S1" "T2" |>.insertEdge "S1" "T3"
    |>.insertEdge "S2" "T1" |>.insertEdge "S2" "T2" |>.insertEdge "S2" "T3"
    |>.insertEdge "S3" "T1" |>.insertEdge "S3" "T2" |>.insertEdge "S3" "T3"

  let ancsT1 := gBipartite.ancestors "T1"
  assert! ancsT1.size == 3
  assert! ancsT1.contains "S1" && ancsT1.contains "S2" && ancsT1.contains "S3"
  let gBipartiteReduced := gBipartite.transitiveReduction
  let parentsT1_bip := gBipartiteReduced.parent.getD "T1" {}
  assert! parentsT1_bip.size == 3
  stderr.putStrLn "  ✓ Bipartite structure handled correctly"

def runTestsStress : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 29: Very long chain (20 nodes)
  stderr.putStrLn "Test 29: Very long chain (20 nodes)"
  let mut gVeryLong : DAG Nat := DAG.empty
  for i in [0:19] do
    gVeryLong := gVeryLong.insertEdge i (i + 1)

  let ancs19 := gVeryLong.ancestors 19
  assert! ancs19.size == 19
  for i in [0:19] do
    assert! ancs19.contains i
  stderr.putStrLn "  ✓ Very long chain handled correctly"

  -- Test 30: Wide graph (1 node with 10 parents)
  stderr.putStrLn "Test 30: Very wide graph (10 parents)"
  let mut gVeryWide : DAG Nat := DAG.empty
  for i in [0:10] do
    gVeryWide := gVeryWide.insertEdge i 100

  let ancs100 := gVeryWide.ancestors 100
  assert! ancs100.size == 10
  let gVeryWideReduced := gVeryWide.transitiveReduction
  let parents100 := gVeryWideReduced.parent.getD 100 {}
  assert! parents100.size == 10
  stderr.putStrLn "  ✓ Very wide graph handled correctly"

  -- Test 31: Chain with all skip edges
  stderr.putStrLn "Test 31: Fully connected chain (all transitive)"
  let mut gFullChain : DAG Nat := DAG.empty
  for i in [0:5] do
    for j in [i+1:6] do
      gFullChain := gFullChain.insertEdge i j

  let ancs5_full := gFullChain.ancestors 5
  assert! ancs5_full.size == 5
  let gFullChainReduced := gFullChain.transitiveReduction
  for i in [1:6] do
    let parents := gFullChainReduced.parent.getD i {}
    assert! parents.size == 1 && parents.contains (i - 1)
  stderr.putStrLn "  ✓ Fully connected chain reduced correctly"

def runTestsSpecialCases : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 32: Double diamond
  stderr.putStrLn "Test 32: Double diamond (stacked)"
  let gDoubleDiamond : DAG String := DAG.empty
    |>.insertEdge "A" "B1"
    |>.insertEdge "A" "B2"
    |>.insertEdge "B1" "C"
    |>.insertEdge "B2" "C"
    |>.insertEdge "C" "D1"
    |>.insertEdge "C" "D2"
    |>.insertEdge "D1" "E"
    |>.insertEdge "D2" "E"

  let ancsE := gDoubleDiamond.ancestors "E"
  assert! ancsE.size == 6
  assert! ancsE.contains "A" && ancsE.contains "B1" && ancsE.contains "B2"
  assert! ancsE.contains "C" && ancsE.contains "D1" && ancsE.contains "D2"
  stderr.putStrLn "  ✓ Double diamond handled correctly"

  -- Test 33: Cross pattern
  stderr.putStrLn "Test 33: Cross pattern (X shape)"
  let gCross : DAG String := DAG.empty
    |>.insertEdge "TL" "Center"
    |>.insertEdge "TR" "Center"
    |>.insertEdge "Center" "BL"
    |>.insertEdge "Center" "BR"

  let ancsBL := gCross.ancestors "BL"
  assert! ancsBL.size == 3
  assert! ancsBL.contains "TL" && ancsBL.contains "TR" && ancsBL.contains "Center"
  stderr.putStrLn "  ✓ Cross pattern handled correctly"

  -- Test 34: Hourglass pattern
  stderr.putStrLn "Test 34: Hourglass pattern"
  let gHourglass : DAG String := DAG.empty
    |>.insertEdge "T1" "M"
    |>.insertEdge "T2" "M"
    |>.insertEdge "T3" "M"
    |>.insertEdge "M" "B1"
    |>.insertEdge "M" "B2"
    |>.insertEdge "M" "B3"

  let ancsB1 := gHourglass.ancestors "B1"
  assert! ancsB1.size == 4
  assert! ancsB1.contains "M" && ancsB1.contains "T1"
  assert! ancsB1.contains "T2" && ancsB1.contains "T3"
  stderr.putStrLn "  ✓ Hourglass pattern handled correctly"

  -- Test 35: Parallel diamonds
  stderr.putStrLn "Test 35: Parallel diamonds merging"
  let gParallelDiamonds : DAG String := DAG.empty
    |>.insertEdge "A1" "B1"
    |>.insertEdge "A1" "C1"
    |>.insertEdge "B1" "D1"
    |>.insertEdge "C1" "D1"
    |>.insertEdge "A2" "B2"
    |>.insertEdge "A2" "C2"
    |>.insertEdge "B2" "D2"
    |>.insertEdge "C2" "D2"
    |>.insertEdge "D1" "E"
    |>.insertEdge "D2" "E"

  let ancsE_par := gParallelDiamonds.ancestors "E"
  assert! ancsE_par.size == 8
  stderr.putStrLn "  ✓ Parallel diamonds handled correctly"

def runTestsInsertEdge : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 36: Insert duplicate edge
  stderr.putStrLn "Test 36: Insert duplicate edge"
  let g1 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "B"

  let parentsB := g1.parent.getD "B" {}
  assert! parentsB.size == 1 && parentsB.contains "A"
  stderr.putStrLn "  ✓ Duplicate edge insertion idempotent"

  -- Test 37: Insert edge then remove then re-insert
  stderr.putStrLn "Test 37: Edge removal and re-insertion"
  let g2 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "C" "B"
    |>.removeEdge "A" "B"
    |>.insertEdge "A" "B"

  let parentsB2 := g2.parent.getD "B" {}
  assert! parentsB2.size == 2 && parentsB2.contains "A" && parentsB2.contains "C"
  stderr.putStrLn "  ✓ Edge re-insertion works correctly"

  -- Test 38: Multiple removals
  stderr.putStrLn "Test 38: Multiple edge removals"
  let g3 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "C" "B"
    |>.insertEdge "D" "B"
    |>.removeEdge "A" "B"
    |>.removeEdge "C" "B"

  let parentsB3 := g3.parent.getD "B" {}
  assert! parentsB3.size == 1 && parentsB3.contains "D"
  stderr.putStrLn "  ✓ Multiple removals work correctly"

def runTestsAncestorVariants : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 39: Ancestors at different depths
  stderr.putStrLn "Test 39: Ancestors at different depths"
  let gDepths : DAG String := DAG.empty
    |>.insertEdge "D3" "D2a"
    |>.insertEdge "D3" "D2b"
    |>.insertEdge "D2a" "D1"
    |>.insertEdge "D2b" "D1"
    |>.insertEdge "D1" "D0"

  let ancsD0 := gDepths.ancestors "D0"
  assert! ancsD0.size == 4
  let ancsD1 := gDepths.ancestors "D1"
  assert! ancsD1.size == 3
  let ancsD2a := gDepths.ancestors "D2a"
  assert! ancsD2a.size == 1 && ancsD2a.contains "D3"
  stderr.putStrLn "  ✓ Ancestors at different depths correct"

  -- Test 40: allAncestors completeness check
  stderr.putStrLn "Test 40: allAncestors includes all graph nodes"
  let gComplete : DAG String := DAG.empty
    |>.insertEdge "Root" "Mid"
    |>.insertEdge "Mid" "Leaf"

  let allAncsComplete := gComplete.allAncestors
  assert! allAncsComplete.contains "Root"
  assert! allAncsComplete.contains "Mid"
  assert! allAncsComplete.contains "Leaf"
  assert! (allAncsComplete.getD "Root" {}).size == 0
  assert! (allAncsComplete.getD "Mid" {}).size == 1
  assert! (allAncsComplete.getD "Leaf" {}).size == 2
  stderr.putStrLn "  ✓ allAncestors includes all nodes"

def runTestsTransitiveReductionEdgeCases : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 41: Transitive reduction on already reduced graph
  stderr.putStrLn "Test 41: Double transitive reduction is idempotent"
  let gIdempotent : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"

  let gReduced1 := gIdempotent.transitiveReduction
  let gReduced2 := gReduced1.transitiveReduction

  for (node, parents) in gReduced1.parent do
    let parents2 := gReduced2.parent.getD node {}
    assert! parents.size == parents2.size
    for p in parents do
      assert! parents2.contains p
  stderr.putStrLn "  ✓ Double reduction is idempotent"

  -- Test 42: Transitive reduction preserves reachability
  stderr.putStrLn "Test 42: Reduction preserves reachability"
  let gReach : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "C"
    |>.insertEdge "A" "D"
    |>.insertEdge "B" "D"

  let gReachReduced := gReach.transitiveReduction
  let ancsD_before := gReach.ancestors "D"
  let ancsD_after := gReachReduced.ancestors "D"
  assert! ancsD_before.size == ancsD_after.size
  for a in ancsD_before do
    assert! ancsD_after.contains a
  stderr.putStrLn "  ✓ Reduction preserves reachability"

  -- Test 43: Diamond with extra shortcut
  stderr.putStrLn "Test 43: Diamond with shortcut through both paths"
  let gDiamondShortcut : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"
    |>.insertEdge "B" "C"

  let gDSReduced := gDiamondShortcut.transitiveReduction
  let parentsD_ds := gDSReduced.parent.getD "D" {}
  assert! !parentsD_ds.contains "A"
  let parentsC_ds := gDSReduced.parent.getD "C" {}
  assert! parentsC_ds.size == 1 && parentsC_ds.contains "B"
  stderr.putStrLn "  ✓ Diamond with extra shortcut handled correctly"

def runTestsComplexTopologies : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 44: Crown graph (cycle-free bipartite)
  stderr.putStrLn "Test 44: Crown-like structure"
  let gCrown : DAG String := DAG.empty
    |>.insertEdge "U1" "V2"
    |>.insertEdge "U1" "V3"
    |>.insertEdge "U2" "V1"
    |>.insertEdge "U2" "V3"
    |>.insertEdge "U3" "V1"
    |>.insertEdge "U3" "V2"

  let ancsV1 := gCrown.ancestors "V1"
  assert! ancsV1.size == 2 && ancsV1.contains "U2" && ancsV1.contains "U3"
  let ancsV2 := gCrown.ancestors "V2"
  assert! ancsV2.size == 2 && ancsV2.contains "U1" && ancsV2.contains "U3"
  stderr.putStrLn "  ✓ Crown-like structure handled correctly"

  -- Test 45: Pyramid structure
  stderr.putStrLn "Test 45: Pyramid (4 levels)"
  let gPyramid : DAG String := DAG.empty
    |>.insertEdge "L0_0" "L1_0"
    |>.insertEdge "L0_0" "L1_1"
    |>.insertEdge "L0_1" "L1_1"
    |>.insertEdge "L0_1" "L1_2"
    |>.insertEdge "L1_0" "L2_0"
    |>.insertEdge "L1_1" "L2_0"
    |>.insertEdge "L1_1" "L2_1"
    |>.insertEdge "L1_2" "L2_1"
    |>.insertEdge "L2_0" "L3_0"
    |>.insertEdge "L2_1" "L3_0"

  let ancsL3 := gPyramid.ancestors "L3_0"
  assert! ancsL3.size == 7
  stderr.putStrLn "  ✓ Pyramid structure handled correctly"

  -- Test 46: Grid-like DAG (3x3)
  stderr.putStrLn "Test 46: Grid DAG (3x3)"
  let gGrid : DAG String := DAG.empty
    |>.insertEdge "0_0" "0_1" |>.insertEdge "0_1" "0_2"
    |>.insertEdge "0_0" "1_0" |>.insertEdge "0_1" "1_1" |>.insertEdge "0_2" "1_2"
    |>.insertEdge "1_0" "1_1" |>.insertEdge "1_1" "1_2"
    |>.insertEdge "1_0" "2_0" |>.insertEdge "1_1" "2_1" |>.insertEdge "1_2" "2_2"
    |>.insertEdge "2_0" "2_1" |>.insertEdge "2_1" "2_2"

  let ancs22 := gGrid.ancestors "2_2"
  assert! ancs22.size == 8
  stderr.putStrLn "  ✓ Grid DAG handled correctly"

  -- Test 47: Butterfly pattern
  stderr.putStrLn "Test 47: Butterfly pattern"
  let gButterfly : DAG String := DAG.empty
    |>.insertEdge "LT" "LM"
    |>.insertEdge "RT" "RM"
    |>.insertEdge "LM" "Center"
    |>.insertEdge "RM" "Center"
    |>.insertEdge "Center" "LB"
    |>.insertEdge "Center" "RB"

  let ancsLB := gButterfly.ancestors "LB"
  assert! ancsLB.size == 5
  assert! ancsLB.contains "LT" && ancsLB.contains "LM"
  assert! ancsLB.contains "RT" && ancsLB.contains "RM"
  assert! ancsLB.contains "Center"
  stderr.putStrLn "  ✓ Butterfly pattern handled correctly"

def runTestsMiscellaneous : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 48: Insert with existing parents
  stderr.putStrLn "Test 48: Insert overwrites parents"
  let g1 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "C" "B"
  let newParents : HashSet String := ({} : HashSet String).insert "D"
  let g2 := g1.insert "B" newParents
  let parentsB := g2.parent.getD "B" {}
  assert! parentsB.size == 1 && parentsB.contains "D"
  stderr.putStrLn "  ✓ Insert overwrites correctly"

  -- Test 49: Complex allAncestors consistency
  stderr.putStrLn "Test 49: allAncestors on pyramid"
  let gPyr : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "B" "E"
    |>.insertEdge "C" "E"
    |>.insertEdge "C" "F"
    |>.insertEdge "D" "G"
    |>.insertEdge "E" "G"
    |>.insertEdge "E" "H"
    |>.insertEdge "F" "H"

  let allAncsPyr := gPyr.allAncestors
  for node in ["A", "B", "C", "D", "E", "F", "G", "H"] do
    let expected := gPyr.ancestors node
    let actual := allAncsPyr.getD node {}
    assert! expected.size == actual.size
    for e in expected do
      assert! actual.contains e
  stderr.putStrLn "  ✓ allAncestors consistent on pyramid"

  -- Test 50: Transitive reduction count
  stderr.putStrLn "Test 50: Count edges before/after reduction"
  let gCount : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "C"
    |>.insertEdge "A" "D"
    |>.insertEdge "B" "D"

  let mut edgesBefore := 0
  for (_, parents) in gCount.parent do
    edgesBefore := edgesBefore + parents.size
  assert! edgesBefore == 6

  let gCountReduced := gCount.transitiveReduction
  let mut edgesAfter := 0
  for (_, parents) in gCountReduced.parent do
    edgesAfter := edgesAfter + parents.size
  assert! edgesAfter == 3
  stderr.putStrLn "  ✓ Edge count reduced from 6 to 3"

  -- Test 51: Self-edges are removed by transitive reduction
  stderr.putStrLn "Test 51: Self-edges removed"
  let gSelfEdge : DAG String := DAG.empty
    |>.insertEdge "A" "A"  -- self-edge
    |>.insertEdge "A" "B"

  let parentsA_before := gSelfEdge.parent.getD "A" {}
  assert! parentsA_before.contains "A"

  let gSelfEdgeReduced := gSelfEdge.transitiveReduction
  let parentsA_after := gSelfEdgeReduced.parent.getD "A" {}
  assert! !parentsA_after.contains "A"
  let parentsB_after := gSelfEdgeReduced.parent.getD "B" {}
  assert! parentsB_after.contains "A"
  stderr.putStrLn "  ✓ Self-edge A → A removed"

  -- Test 52: Multiple self-edges removed
  stderr.putStrLn "Test 52: Multiple self-edges removed"
  let gMultiSelf : DAG String := DAG.empty
    |>.insertEdge "A" "A"
    |>.insertEdge "B" "B"
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"

  let gMultiSelfReduced := gMultiSelf.transitiveReduction
  let parentsA_ms := gMultiSelfReduced.parent.getD "A" {}
  let parentsB_ms := gMultiSelfReduced.parent.getD "B" {}
  assert! !parentsA_ms.contains "A"
  assert! !parentsB_ms.contains "B"
  assert! parentsB_ms.contains "A"
  stderr.putStrLn "  ✓ Multiple self-edges removed"

def runTestsLeavesAndNodes : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 53: Nodes function
  stderr.putStrLn "Test 53: nodes function"
  let gNodes : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "D" "C"

  let allNodes := gNodes.nodes
  assert! allNodes.size == 4
  assert! allNodes.contains "A" && allNodes.contains "B"
  assert! allNodes.contains "C" && allNodes.contains "D"
  stderr.putStrLn "  ✓ nodes returns all nodes"

  -- Test 54: Leaves of a chain
  stderr.putStrLn "Test 54: Leaves of a chain"
  let gChain : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"

  let leavesChain := gChain.leaves
  assert! leavesChain.size == 1 && leavesChain.contains "C"
  stderr.putStrLn "  ✓ Chain has one leaf (C)"

  -- Test 55: Leaves of a diamond
  stderr.putStrLn "Test 55: Leaves of a diamond"
  let gDiamond : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"

  let leavesDiamond := gDiamond.leaves
  assert! leavesDiamond.size == 1 && leavesDiamond.contains "D"
  stderr.putStrLn "  ✓ Diamond has one leaf (D)"

  -- Test 56: Leaves of a tree (multiple leaves)
  stderr.putStrLn "Test 56: Leaves of a tree"
  let gTree : DAG String := DAG.empty
    |>.insertEdge "Root" "L1"
    |>.insertEdge "Root" "L2"
    |>.insertEdge "L1" "L3"
    |>.insertEdge "L1" "L4"

  let leavesTree := gTree.leaves
  assert! leavesTree.size == 3
  assert! leavesTree.contains "L2" && leavesTree.contains "L3" && leavesTree.contains "L4"
  stderr.putStrLn "  ✓ Tree has three leaves"

  -- Test 57: Leaves of empty graph
  stderr.putStrLn "Test 57: Leaves of empty graph"
  let gEmpty : DAG String := DAG.empty
  assert! gEmpty.leaves.size == 0
  assert! gEmpty.nodes.size == 0
  stderr.putStrLn "  ✓ Empty graph has no leaves"

  -- Test 58: removeNode function
  stderr.putStrLn "Test 58: removeNode function"
  let gRemove : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"

  let gAfterRemoveB := gRemove.removeNode "B"
  assert! !gAfterRemoveB.nodes.contains "B"
  let parentsC_rem := gAfterRemoveB.parent.getD "C" {}
  assert! parentsC_rem.contains "A" && !parentsC_rem.contains "B"
  stderr.putStrLn "  ✓ removeNode removes node and its edges"

  -- Test 59: removeNodes function
  stderr.putStrLn "Test 59: removeNodes function"
  let gRemoveMulti : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"

  let nodesToRemove : HashSet String := ({} : HashSet String).insert "B" |>.insert "C"
  let gAfterRemoveMulti := gRemoveMulti.removeNodes nodesToRemove
  assert! !gAfterRemoveMulti.nodes.contains "B"
  assert! !gAfterRemoveMulti.nodes.contains "C"
  let parentsD_rem := gAfterRemoveMulti.parent.getD "D" {}
  assert! parentsD_rem.contains "A"
  stderr.putStrLn "  ✓ removeNodes removes multiple nodes"

  -- Test 60: Leaves match between DAG and its transitive reduction
  stderr.putStrLn "Test 60: Leaves match transitive reduction"
  let gWithTransitive : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"  -- transitive edge
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"  -- transitive edge

  let leavesOriginal := gWithTransitive.leaves
  let leavesReduced := gWithTransitive.transitiveReduction.leaves
  assert! leavesOriginal.size == leavesReduced.size
  for leaf in leavesOriginal do
    assert! leavesReduced.contains leaf
  stderr.putStrLn "  ✓ Leaves match between original and reduced"

def runTestsIterativeLeafRemoval : IO Unit := do
  let stderr ← IO.getStderr

  -- Test 61: Iterative leaf removal stress test
  -- Build a large DAG, then repeatedly:
  -- 1. Check leaves match between DAG and transitive reduction
  -- 2. Remove leaves
  -- 3. Repeat until empty
  stderr.putStrLn "Test 61: Iterative leaf removal (large DAG)"

  -- Build a "layered" DAG with some transitive edges
  -- Layer 0: nodes 0-4 (roots)
  -- Layer 1: nodes 5-9 (each has 2 parents from layer 0)
  -- Layer 2: nodes 10-14 (each has 2 parents from layer 1)
  -- Layer 3: nodes 15-19 (each has 2 parents from layer 2)
  -- Plus some skip edges for transitivity

  let mut gLarge : DAG Nat := DAG.empty

  -- Layer 0 → Layer 1
  for i in [0:5] do
    gLarge := gLarge.insertEdge i (5 + i)
    gLarge := gLarge.insertEdge ((i + 1) % 5) (5 + i)

  -- Layer 1 → Layer 2
  for i in [0:5] do
    gLarge := gLarge.insertEdge (5 + i) (10 + i)
    gLarge := gLarge.insertEdge (5 + (i + 1) % 5) (10 + i)

  -- Layer 2 → Layer 3
  for i in [0:5] do
    gLarge := gLarge.insertEdge (10 + i) (15 + i)
    gLarge := gLarge.insertEdge (10 + (i + 1) % 5) (15 + i)

  -- Add some transitive edges (skip edges)
  for i in [0:5] do
    gLarge := gLarge.insertEdge i (10 + i)  -- Layer 0 → Layer 2
    gLarge := gLarge.insertEdge (5 + i) (15 + i)  -- Layer 1 → Layer 3

  let mut g := gLarge
  let mut iterations := 0
  let maxIterations := 100  -- Safety limit

  while g.nodes.size > 0 && iterations < maxIterations do
    iterations := iterations + 1

    -- Check that leaves match between original and transitive reduction
    let leavesG := g.leaves
    let gReduced := g.transitiveReduction
    let leavesReduced := gReduced.leaves

    -- Leaves should be the same
    assert! leavesG.size == leavesReduced.size
    for leaf in leavesG do
      assert! leavesReduced.contains leaf

    -- Remove leaves and continue
    g := g.removeNodes leavesG

  assert! g.nodes.size == 0
  stderr.putStrLn s!"  ✓ Completed in {iterations} iterations, graph is empty"

  -- Test 62: Another iterative test with a grid-like DAG
  stderr.putStrLn "Test 62: Iterative leaf removal (grid DAG)"

  -- Build a 4x4 grid DAG
  let mut gGrid : DAG Nat := DAG.empty
  for row in [0:4] do
    for col in [0:4] do
      let node := row * 4 + col
      -- Edge from left neighbor
      if col > 0 then
        gGrid := gGrid.insertEdge (row * 4 + col - 1) node
      -- Edge from top neighbor
      if row > 0 then
        gGrid := gGrid.insertEdge ((row - 1) * 4 + col) node

  let mut g2 := gGrid
  let mut iterations2 := 0

  while g2.nodes.size > 0 && iterations2 < 50 do
    iterations2 := iterations2 + 1

    let leavesG2 := g2.leaves
    let g2Reduced := g2.transitiveReduction
    let leavesReduced2 := g2Reduced.leaves

    assert! leavesG2.size == leavesReduced2.size
    for leaf in leavesG2 do
      assert! leavesReduced2.contains leaf

    g2 := g2.removeNodes leavesG2

  assert! g2.nodes.size == 0
  stderr.putStrLn s!"  ✓ Grid completed in {iterations2} iterations"

  -- Test 63: Stress test with random-ish structure
  stderr.putStrLn "Test 63: Iterative leaf removal (complex DAG)"

  -- Build a more complex DAG with various patterns
  let mut gComplex : DAG Nat := DAG.empty

  -- Chain backbone: 0 → 1 → 2 → ... → 9
  for i in [0:9] do
    gComplex := gComplex.insertEdge i (i + 1)

  -- Add diamond patterns
  for i in [0:3] do
    let base := i * 3
    gComplex := gComplex.insertEdge base (20 + i * 2)
    gComplex := gComplex.insertEdge base (21 + i * 2)
    gComplex := gComplex.insertEdge (20 + i * 2) (base + 1)
    gComplex := gComplex.insertEdge (21 + i * 2) (base + 1)

  -- Add some skip edges
  gComplex := gComplex.insertEdge 0 5
  gComplex := gComplex.insertEdge 0 9
  gComplex := gComplex.insertEdge 3 9

  let mut g3 := gComplex
  let mut iterations3 := 0

  while g3.nodes.size > 0 && iterations3 < 50 do
    iterations3 := iterations3 + 1

    let leavesG3 := g3.leaves
    let g3Reduced := g3.transitiveReduction
    let leavesReduced3 := g3Reduced.leaves

    assert! leavesG3.size == leavesReduced3.size
    for leaf in leavesG3 do
      assert! leavesReduced3.contains leaf

    g3 := g3.removeNodes leavesG3

  assert! g3.nodes.size == 0
  stderr.putStrLn s!"  ✓ Complex DAG completed in {iterations3} iterations"

def runTests : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn "Running tests..."
  runTestsBasic
  runTestsEdgeCases
  runTestsChains
  runTestsMultipleRoots
  runTestsDiamonds
  runTestsComplex
  runTestsDisconnected
  runTestsLattice
  runTestsStress
  runTestsSpecialCases
  runTestsInsertEdge
  runTestsAncestorVariants
  runTestsTransitiveReductionEdgeCases
  runTestsComplexTopologies
  runTestsMiscellaneous
  runTestsLeavesAndNodes
  runTestsIterativeLeafRemoval
  stderr.putStrLn "All tests passed! ✓"

def main : IO Unit := runTests
