# Order

This folder contains order theory in a broad sense.

## Order hierarchy

The basic order hierarchy is split across a series of subfolders that each depend on the previous:
* `Order.Preorder` for preorders, partial orders, lattices, linear orders
* `Order.BooleanAlgebra` for Heyting/bi-Heyting/co-Heyting/Boolean algebras
* `Order.CompleteLattice` for frames, coframes, complete lattices
* `Order.ConditionallyCompleteLattice` for conditionally complete lattices
* `Order.CompleteBooleanAlgebra` for complete Boolean algebras

Files in earlier subfolders should not import files in later ones.

## TODO

Succinctly explain the other subfolders.

The above is still very much a vision. We need to sort the content of existing files into those
order hierarchy subfolders.
