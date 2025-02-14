/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.LocallyClosed

/-!
# Intervals are locally closed

We prove that the intervals on a topological ordered space are locally closed.
-/

variable {X : Type*} [TopologicalSpace X] {a b : X}

theorem isLocallyClosed_Icc [Preorder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Icc a b) :=
  isClosed_Icc.isLocallyClosed

theorem isLocallyClosed_Ioo [LinearOrder X] [OrderClosedTopology X] :
    IsLocallyClosed (Set.Ioo a b) :=
  isOpen_Ioo.isLocallyClosed

theorem isLocallyClosed_Ici [Preorder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ici a) :=
  isClosed_Ici.isLocallyClosed

theorem isLocallyClosed_Iic [Preorder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Iic a) :=
  isClosed_Iic.isLocallyClosed

theorem isLocallyClosed_Ioi [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioi a) :=
  isOpen_Ioi.isLocallyClosed

theorem isLocallyClosed_Iio [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Iio a) :=
  isOpen_Iio.isLocallyClosed

theorem isLocallyClosed_Ioc [LinearOrder X] [ClosedIicTopology X] :
    IsLocallyClosed (Set.Ioc a b) := by
  rw [← Set.Iic_inter_Ioi]
  exact isLocallyClosed_Iic.inter isLocallyClosed_Ioi

theorem isLocallyClosed_Ico [LinearOrder X] [ClosedIciTopology X] :
    IsLocallyClosed (Set.Ico a b) := by
  rw [← Set.Iio_inter_Ici]
  exact isLocallyClosed_Iio.inter isLocallyClosed_Ici
