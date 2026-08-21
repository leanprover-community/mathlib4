/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Commutative structures from unbundled commutativity

This file provides scoped instances that promote algebraic structures satisfying
`IsMulCommutative` or `IsAddCommutative` to their bundled commutative counterparts.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

open Function

variable {G : Type*}

namespace IsMulCommutative

/-- A magma which `IsMulCommutative` is a `CommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An additive magma which `IsMulCommutative` is a `AddCommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Mul M] [IsMulCommutative M] : CommMagma M where
  mul_comm := mul_comm'

/-- A `Semigroup` which `IsMulCommutative` is a `CommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddSemigroup` which `IsMulCommutative` is a `AddCommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Semigroup M] [IsMulCommutative M] :
    CommSemigroup M where

/-- A `Monoid` which `IsMulCommutative` is a `CommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `AddMonoid` which `IsMulCommutative` is a `AddCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Monoid M] [IsMulCommutative M] :
    CommMonoid M where

/-- A `DivisionMonoid` which `IsMulCommutative` is a `DivisionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `SubtractionMonoid` which `IsMulCommutative` is a `SubtractionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [DivisionMonoid M] [IsMulCommutative M] :
    DivisionCommMonoid M where

/-- A `Group` which `IsMulCommutative` is a `CommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddGroup` which `IsMulCommutative` is a `AddCommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {G : Type*} [Group G] [IsMulCommutative G] :
    CommGroup G where

end IsMulCommutative
