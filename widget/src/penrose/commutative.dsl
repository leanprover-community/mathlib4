/*
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
*/

-- This is a Penrose (https://penrose.cs.cmu.edu/) domain file for commutative diagrams.

-- Any subclass can be the endpoint of a k-cell.
type Targettable

type Object <: Targettable
type Cell <: Targettable

-- We detect what kind of thing the targets are — objects or 1-cells or .. — and create a 1-cell
-- or 2-cell or .. based on that.
constructor MakeCell(Targettable A, Targettable B) -> Cell

-- Positioning predicates. These implicitly determine a grid layout in the diagram by positioning
-- objects relative to each other. For example, when f := MakeCell(A, B), IsRightHorizontal(f)
-- places B to the right of A. The placement is always one grid unit away. If you need to position
-- two objects further than that, do *not* use a position predicate. For example in the diagram
-- A   E
-- B C D
-- if A/B, B/C, C/D, D/E are all positioned one grid unit away, A/E will automatically take up two.
--
-- We need specific, conjunctive predicates such as IsLeftUpDiagonal(f) instead of IsLeft(f) and
-- IsUp(f) in order to fully determine the positioning.
--
-- Note that these do nothing when the targets are cells rather than objects.
predicate IsLeftHorizontal(Cell)
predicate IsRightHorizontal(Cell)
predicate IsUpVertical(Cell)
predicate IsDownVertical(Cell)

predicate IsLeftUpDiagonal(Cell)
predicate IsLeftDownDiagonal(Cell)
predicate IsRightUpDiagonal(Cell)
predicate IsRightDownDiagonal(Cell)

-- Styling-only (non-positioning) predicates.
predicate IsCurvedLeft(Cell)
predicate IsCurvedRight(Cell)

predicate IsLabelLeft(Cell)
predicate IsLabelRight(Cell)

predicate IsDashed(Cell)
predicate IsMono(Cell)
predicate IsEpi(Cell)
predicate IsEmbedding(Cell)
