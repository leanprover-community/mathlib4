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
This will update the `lake-manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

## Using `mathlib4` as a dependency

To start a new project that uses mathlib4 as a dependency:

1. Open a folder that contains no file named `lean-toolchain`.
2. Update your default toolchain to one that is sufficiently recent with `elan default leanprover/lean4:nightly-2023-02-04`

3. Run `lake new <your_project_name> math`.
4. You now have a folder named `your_project_name` that contains a new `lake` project. The `lakefile.lean` folder is configured with the `mathlib4` dependency.
5. Change your current directory to the project folder and run `lake update`. This step downloads `mathlib4` as well as its dependencies.
6. Run `cp lake-packages/mathlib/lean-toolchain .` to make sure your new project uses the same Lean version as `mathlib4`.
7. (Optional) In order to save time compiling all of mathlib and its dependencies, run `lake exe cache get`. This step requires that you have `curl 7.69`  or higher.
8. Run `lake build`. If you have get no build errors, you are good to go!


If you already have a project and you want to use `mathlib4`, add these lines to your `lakefile.lean`:
```
require mathlib from git
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
* Make sure that your project uses the same Lean 4 toolchain as the one used in `mathlib4`
