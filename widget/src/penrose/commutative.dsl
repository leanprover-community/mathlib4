/*
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
*/

-- Any subclass can be the endpoint of a k-cell
type Targettable

type Object <: Targettable
type Cell <: Targettable

-- We detect what the target is and create a 1-cell or 2-cell or .. based on that
constructor MakeCell(Targettable A, Targettable B) -> Cell

-- Positioning predicates which determine directions of cells and consequently the relative
-- positions of their endpoints.
-- We need very specific, conjunctive predicates as opposed to e.g. `IsFacingRight`
-- or `IsHorizontal` mostly in order to optimize constraint solving by having fewer
-- objectives, and also to make positioning work reliably.
-- TODO: these might break when the target is a cell; can't force cell positioning, probably?
predicate IsLeftHorizontal(Cell)
predicate IsRightHorizontal(Cell)
predicate IsUpVertical(Cell)
predicate IsDownVertical(Cell)

predicate IsLeftUpDiagonal(Cell)
predicate IsLeftDownDiagonal(Cell)
predicate IsRightUpDiagonal(Cell)
predicate IsRightDownDiagonal(Cell)

-- Stylistic (non-positioning) predicates
predicate IsCurvedLeft(Cell)
predicate IsCurvedRight(Cell)

predicate IsLabelLeft(Cell)
predicate IsLabelRight(Cell)
