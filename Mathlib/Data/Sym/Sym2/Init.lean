/-
Copyright (c) 2023 Jannis Limperg All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

-- Aesop rule sets only become visible once the file in which they're declared
-- is imported. This is why we put this command in its own file.

-- porting note: using `aesop` in place of `tidy` to simplify proofs
declare_aesop_rule_sets [Sym2]
