def process_file_in_place(file_path, line_numbers):
    with open(file_path, 'r') as infile:
        lines = infile.readlines()

    # Process each line number in the input
    for line_number in line_numbers:
        # Convert to zero-indexed for Python list
        index = line_number - 1

        # Check if the line is within the file range
        if 0 <= index < len(lines):
            # First, find the first "variable" line before the current line
            before_index = None
            for i in range(index - 1, -1, -1):
                if lines[i] is not None and "variable" in lines[i]:
                    before_index = i
                    break

            # Then, find the first "variable" line after the current line
            after_index = None
            for i in range(index + 1, len(lines)):
                if lines[i] is not None and "variable" in lines[i]:
                    after_index = i
                    break

            # Modify the "variable" line before the input line (if found)
            if before_index is not None:
                # Append " in" to the line
                lines[before_index] = lines[before_index].strip() + " in\n"

                # Remove the "variable" line after the current one (if found)
                if after_index is not None:
                    lines[after_index] = None  # Mark for removal

                # Handle the empty lines: ensure exactly one empty line before the modified "variable" line
                # Remove all empty lines that precede the modified "variable" line
                while before_index - 1 >= 0 and lines[before_index - 1] and lines[before_index - 1].strip() == '':
                    lines[before_index - 1] = None  # Remove preceding empty lines
                    before_index -= 1

                # Ensure exactly one empty line before the "variable in" line
                if before_index - 1 >= 0 and lines[before_index - 1] and lines[before_index - 1].strip() != '':
                    lines.insert(before_index, '\n')  # Insert a single empty line before it

                # Remove all empty lines after the modified "variable in" line
                next_index = before_index + 3
                while next_index < len(lines) and (lines[next_index] is None or lines[next_index].strip() == ''):
                    lines[next_index] = None  # Remove empty lines after the "variable in" line
                    next_index += 1

                # Remove all empty lines after the removed "variable" line
                next_index = after_index+1
                #print(next_index)
                #print(lines[next_index])
                while next_index < len(lines) and (lines[next_index] is None or lines[next_index].strip() == ''):
                    lines[next_index] = None  # Remove empty lines after the "variable in" line
                    next_index += 1

    # Write the modified content back to the file
    with open(file_path, 'w') as outfile:
        for line in lines:
            # Avoid writing None lines (those marked for removal)
            if line is not None:
                outfile.write(line)

    print(f"File '{file_path}' has been modified in place.")

# Example usage
#line_numbers = [186, 234]  # Example line numbers
#process_file_in_place("Mathlib/Algebra/ContinuedFractions/Basic.lean", line_numbers)

# code -r -g  ././././Mathlib/Algebra/ContinuedFractions/Basic.lean:186
# code -r -g  ././././Mathlib/Algebra/ContinuedFractions/Basic.lean:232
#process_file_in_place("Mathlib/Algebra/Star/Basic.lean", [175,238])
##process_file_in_place("Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean", [210,241,278])
#process_file_in_place("Mathlib/Analysis/InnerProductSpace/Projection.lean", [749])
#process_file_in_place("Mathlib/CategoryTheory/Localization/Construction.lean", [128,192])
#process_file_in_place("Mathlib/RingTheory/Noetherian/Basic.lean", [68])
#process_file_in_place("Mathlib/Algebra/Category/ModuleCat/Basic.lean", [500])
#process_file_in_place("Mathlib/CategoryTheory/Limits/Constructions/BinaryProducts.lean", [88,194])
#process_file_in_place("Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean", [275,428])
#process_file_in_place("Mathlib/CategoryTheory/CommSq.lean", [230])
#process_file_in_place("Mathlib/Analysis/NormedSpace/OperatorNorm/NormedSpace.lean", [130])
#process_file_in_place("Mathlib/CategoryTheory/Shift/ShiftSequence.lean", [102])
##process_file_in_place("Mathlib/Topology/VectorBundle/Basic.lean", [194,200,206,244,413])
#process_file_in_place("Mathlib/Topology/Sheaves/Stalks.lean", [68])
#process_file_in_place("Mathlib/Topology/UniformSpace/Completion.lean", [336])
#process_file_in_place("Mathlib/Algebra/Module/LocalizedModule/Basic.lean", [983])
#process_file_in_place("Mathlib/Topology/Sets/Opens.lean", [60])
#process_file_in_place("Mathlib/Topology/Inseparable.lean", [534])
#process_file_in_place("Mathlib/Algebra/Group/Subgroup/Basic.lean", [385])
#process_file_in_place("Mathlib/Topology/ContinuousMap/Algebra.lean", [295])
#process_file_in_place("Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean", [84])
#process_file_in_place("Mathlib/LinearAlgebra/Trace.lean", [67])
#process_file_in_place("Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean", [484])
#process_file_in_place("Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean", [405])
#process_file_in_place("Mathlib/CategoryTheory/Sites/Plus.lean", [88,173,212])
#process_file_in_place("Mathlib/Topology/Separation/Basic.lean", [317])
#process_file_in_place("Mathlib/GroupTheory/GroupAction/SubMulAction.lean", [236])
#process_file_in_place("Mathlib/Data/DFinsupp/Order.lean", [218])
#process_file_in_place("Mathlib/Algebra/Field/Subfield/Basic.lean", [341])
#process_file_in_place("Mathlib/Topology/NoetherianSpace.lean", [79])
#process_file_in_place("Mathlib/AlgebraicTopology/DoldKan/FunctorGamma.lean", [97])
#process_file_in_place("Mathlib/Data/Nat/Nth.lean", [405])
#process_file_in_place("Mathlib/RingTheory/FiniteType.lean", [234])
#process_file_in_place("Mathlib/Analysis/CStarAlgebra/Multiplier.lean", [428])
#process_file_in_place("Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean", [307,474])
#process_file_in_place("Mathlib/Topology/Order/Basic.lean", [510])
#process_file_in_place("Mathlib/LinearAlgebra/AnnihilatingPolynomial.lean", [45])
#process_file_in_place("Mathlib/Data/W/Basic.lean", [64])
#process_file_in_place("Mathlib/Algebra/Module/Submodule/Bilinear.lean", [54])
#process_file_in_place("Mathlib/ModelTheory/LanguageMap.lean", [288])
#process_file_in_place("Mathlib/Analysis/Normed/Operator/LinearIsometry.lean", [936])
#process_file_in_place("Mathlib/Topology/Algebra/GroupCompletion.lean", [183])
#process_file_in_place("Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean", [74])
#process_file_in_place("Mathlib/RingTheory/Finiteness/Basic.lean", [367])
#process_file_in_place("Mathlib/RingTheory/FractionalIdeal/Operations.lean", [185,695])
#process_file_in_place("Mathlib/RingTheory/NonUnitalSubring/Basic.lean", [519])
#process_file_in_place("Mathlib/CategoryTheory/Triangulated/Rotate.lean", [127])
#process_file_in_place("Mathlib/Combinatorics/SimpleGraph/Connectivity/WalkCounting.lean", [115,139])
#process_file_in_place("Mathlib/Algebra/NoZeroSMulDivisors/Basic.lean", [60])
#process_file_in_place("Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean", [139,223])
#process_file_in_place("Mathlib/GroupTheory/GroupAction/Quotient.lean", [338,373])
#process_file_in_place("Mathlib/Algebra/Module/NatInt.lean", [67])
#process_file_in_place("Mathlib/CategoryTheory/Monad/EquivMon.lean", [48])
#process_file_in_place("Mathlib/Analysis/Normed/Lp/lpSpace.lean", [794])
#process_file_in_place("Mathlib/CategoryTheory/Subobject/MonoOver.lean", [236])
#process_file_in_place("Mathlib/CategoryTheory/Idempotents/Basic.lean", [93])
#process_file_in_place("Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean", [235])
#process_file_in_place("Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean", [124])
#process_file_in_place("Mathlib/RingTheory/Ideal/Operations.lean", [724])
#process_file_in_place("Mathlib/Algebra/Group/Subgroup/Lattice.lean", [391])
#process_file_in_place("Mathlib/LinearAlgebra/TensorProduct/Subalgebra.lean", [85])
#process_file_in_place("Mathlib/LinearAlgebra/PiTensorProduct.lean", [276])
#process_file_in_place("Mathlib/Analysis/Convex/Between.lean", [67])
#process_file_in_place("Mathlib/Analysis/CStarAlgebra/Basic.lean", [251])
#process_file_in_place("Mathlib/RingTheory/Jacobson/Ring.lean", [155])
#process_file_in_place("Mathlib/Algebra/QuaternionBasis.lean", [59])
#process_file_in_place("Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean", [252])
#process_file_in_place("Mathlib/RingTheory/Ideal/Maximal.lean", [75])
#process_file_in_place("Mathlib/GroupTheory/Perm/Sign.lean", [435])
#process_file_in_place("Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean", [211,270])
#process_file_in_place("Mathlib/Topology/MetricSpace/Contracting.lean", [104,166,274])
#process_file_in_place("Mathlib/Data/DFinsupp/Defs.lean", [49])
#process_file_in_place("Mathlib/Algebra/Polynomial/GroupRingAction.lean", [30])
process_file_in_place("Mathlib/LinearAlgebra/AffineSpace/AffineSubspace.lean", [73,680,687])
process_file_in_place("Mathlib/MeasureTheory/Measure/OpenPos.lean", [137])
process_file_in_place("Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean", [38])
process_file_in_place("Mathlib/CategoryTheory/Sites/Subsheaf.lean", [195])
process_file_in_place("Mathlib/Topology/EMetricSpace/Basic.lean", [211])
process_file_in_place("Mathlib/Algebra/Module/Submodule/Ker.lean", [177])
process_file_in_place("Mathlib/Analysis/LocallyConvex/BalancedCoreHull.lean", [132])
process_file_in_place("Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean", [69])
process_file_in_place("Mathlib/Control/Functor/Multivariate.lean", [109])
process_file_in_place("Mathlib/Data/Setoid/Partition.lean", [253])
process_file_in_place("Mathlib/Algebra/Ring/Subsemiring/Basic.lean", [538])
process_file_in_place("Mathlib/Analysis/Convex/Topology.lean", [307])
process_file_in_place("Mathlib/Topology/ContinuousMap/Ideals.lean", [320])
process_file_in_place("Mathlib/Analysis/LocallyConvex/Basic.lean", [56])
process_file_in_place("Mathlib/Algebra/MvPolynomial/Basic.lean", [827,834])
process_file_in_place("Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean", [453,608,709])
process_file_in_place("Mathlib/Geometry/Euclidean/Sphere/SecondInter.lean", [55])
process_file_in_place("Mathlib/LinearAlgebra/AffineSpace/Combination.lean", [728,944])
process_file_in_place("Mathlib/Algebra/Star/SelfAdjoint.lean", [114])
process_file_in_place("Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean", [504])
process_file_in_place("Mathlib/RingTheory/AdjoinRoot.lean", [142])
process_file_in_place("Mathlib/RingTheory/Norm/Basic.lean", [134])
process_file_in_place("Mathlib/Algebra/Category/BialgebraCat/Basic.lean", [46])
process_file_in_place("Mathlib/Analysis/Normed/Affine/Isometry.lean", [618,643,687])
process_file_in_place("Mathlib/Analysis/LocallyConvex/AbsConvex.lean", [155])
process_file_in_place("Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean", [217])
process_file_in_place("Mathlib/Analysis/Normed/Algebra/Spectrum.lean", [283])
process_file_in_place("Mathlib/Algebra/GradedMonoid.lean", [322])
process_file_in_place("Mathlib/RingTheory/Localization/Defs.lean", [124])
process_file_in_place("Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean", [205])
process_file_in_place("Mathlib/Analysis/Convex/Exposed.lean", [175])
process_file_in_place("Mathlib/Data/Prod/TProd.lean", [44])
process_file_in_place("Mathlib/RingTheory/Artinian/Module.lean", [97])
process_file_in_place("Mathlib/MeasureTheory/Integral/BochnerL1.lean", [485])
process_file_in_place("Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean", [596])
process_file_in_place("Mathlib/Topology/Instances/AddCircle.lean", [375,388])
process_file_in_place("Mathlib/Algebra/Module/ZLattice/Basic.lean", [183])
