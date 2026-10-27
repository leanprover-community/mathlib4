# Algebra

This folder contains algebra in a broad sense.

## Algebraic hierarchy

The basic algebraic hierarchy is split across a series of subfolders that each depend on the
previous:
* `Algebra.Notation` for basic algebraic notation
* `Algebra.Group` for semigroups, monoids, groups
* `Algebra.GroupWithZero` for monoids with a zero adjoined, groups with a zero adjoined
* `Algebra.Ring` for additive monoids and groups with one, semirings, rings
* `Algebra.Field` for semifields, fields

Files in earlier subfolders should not import files in later ones.

## TODO: Succinctly explain the other subfolders
