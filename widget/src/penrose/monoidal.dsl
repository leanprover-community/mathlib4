type Mor2
type Mor1

type Core <: Mor2
type Id <: Mor2

predicate Left(Mor2, Mor2)
predicate Above(Mor2, Mor2)

constructor MakeString(Mor2 f, Mor2 g) -> Mor1
