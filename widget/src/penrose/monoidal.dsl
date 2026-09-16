/*
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
*/

type Mor2
type Mor1

type Atom <: Mor2
type Id <: Mor2

predicate Left(Mor2, Mor2)
predicate Above(Mor2, Mor2)

constructor MakeString(Mor2 f, Mor2 g) -> Mor1
