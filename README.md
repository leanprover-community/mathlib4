# mathlib4

![](https://github.com/leanprover-community/mathlib4/workflows/continuous%20integration/badge.svg?branch=master)
[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/37904)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)

This is the work in progress port of [mathlib](https://github.com/leanprover-community/mathlib) to [Lean 4](https://leanprover.github.io/).

## Contributing
A guide on how to port a file from mathlib3 to mathlib4 can be found in the [wiki](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki).
The porting effort is coordinated through [zulip](https://leanprover.zulipchat.com/),
if you want to contribute to the port please come to the `mathlib4` stream.

## Build instructions

* Make sure Lean is not running, and close all instances of VSCode running Lean processes.
* Get the newest version of `elan`. If you already have installed a version of Lean, you can run
  ```
  elan self update
  ```
  If the above command fails, or if you need to install `elan`, run
  ```
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```
  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To build `mathlib4` run `lake build`. To build and run all tests, run `make`.
* You can use `lake build +Mathlib.Import.Path` to build a particular file, e.g. `lake build +Mathlib.Algebra.Group.Defs`.
* If you added a new file, run the following command to update `Mathlib.lean`
  ```
  find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
  ```

### Downloading cached build files

Run `lake exe cache get` to download cached build files that are computed by `mathlib4`'s automated workflow.
If `tar` terminates with an error, it means that you might have ended up with corrupted files.
In this case, run `lake exe cache get!` to overwrite them (`get` won't try to download the same file again).

Call `lake exe cache` to see its help menu.

### Building HTML documentation
Building HTML documentation locally is straightforward:
```
lake -Kdoc=on build Mathlib:docs
```
The HTML files can then be found in `build/doc`.

### Dependencies
If you want to update dependencies, use `lake update -Kdoc=on`.
This will update the `lean_packages/manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

## Using `mathlib4` as a dependency

If you want to start a project that uses `mathlib4` as a dependency, you can run:
```
lake init MyProject math
```

Important: the command above requires a more recent toolchain set as default, which can be done with, for example:
```
elan default leanprover/lean4:nightly-2023-01-29
```

Or, if you already have a project and you want to be able to use `mathlib4`, add these lines to your `lakefile.lean`:
```
require std from git
  "https://github.com/leanprover-community/mathlib4" @ "<REVISION>"
```
Where `<REVISION>` can be a commit hash, a branch or a tag. You can check [this section](https://github.com/leanprover/lake/#adding-dependencies) from Lake's README for more info.

Either way, make sure that your project uses the same Lean 4 toolchain as the one used in `mathlib4`.

### Using `lake exe cache` on your project

Lake projects inherit executables declared with `lean_exe` from their dependencies.
It means that you can call `lake exe cache` on your project if you're using `mathlib4` as a dependency.
However, make sure to follow these guidelines:
* Call `lake exe cache get` (or other `cache` commands) from the root directory of your project
* If your project depends on `std4` or `quote4`, let `mathlib4` pull them transitively. That is, don't `require` them on your `lakefile.lean`

