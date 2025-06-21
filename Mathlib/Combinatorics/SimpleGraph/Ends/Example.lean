/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import Mathlib.Data.Finite.Set

/-!
# Git Hooks experiment

I have added

```bash
#!/bin/bash
lake exe mk_all
```

To `.git/hooks/pre-push`

I will now push this as a PR to see if it works.

---

Ok that didn't work, I'm running

`chmod +x .git/hooks/pre-push`

To see if that helps.

-/
