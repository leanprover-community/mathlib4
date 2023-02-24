/-
Copyright (c) 2023 Jannis LIpmerg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

-- Aesop rule sets only become visible once the file in which they're declared
-- is imported. This is why we put this command in its own file.
declare_aesop_rule_sets [Continuous]
