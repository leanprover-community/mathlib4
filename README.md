# mathlib4

![GitHub CI](https://github.com/leanprover-community/mathlib4/workflows/continuous%20integration/badge.svg?branch=master)
[![Bors enabled](https://bors.tech/images/badge_small.svg)](https://app.bors.tech/repositories/37904)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com)

This is the work in progress port of [mathlib](https://github.com/leanprover-community/mathlib) to [Lean 4](https://leanprover.github.io/).

## Documentation

The [mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/index.html) are
[generated automatically](https://github.com/leanprover/doc-gen4) from the source `.lean` files.

## Contributing

A guide on how to port a file from mathlib3 to mathlib4 can be found in the [wiki](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki).
The porting effort is coordinated through [zulip](https://leanprover.zulipchat.com/),
if you want to contribute to the port please come to the `mathlib4` stream.

## Build instructions

* Make sure Lean is not running, and close all instances of VSCode running Lean processes.
* Get the newest version of `elan`. If you already have installed a version of Lean, you can run

  ```shell
  elan self update
  ```

  If the above command fails, or if you need to install `elan`, run

  ```shell
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

  If this also fails, follow the instructions under `Regular install` [here](https://leanprover-community.github.io/get_started.html).
* To obtain precompiled `olean` files, run `lake exe cache get`. (Skipping this step means the next step will be very slow.)
* To build `mathlib4` run `lake build`.
* To build and run all tests, run `make`.
* You can use `lake build Mathlib.Import.Path` to build a particular file, e.g. `lake build Mathlib.Algebra.Group.Defs`.
* If you added a new file, run the following command to update `Mathlib.lean`

  ```shell
  find Mathlib -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Mathlib.lean
  ```

### Downloading cached build files

You can run `lake exe cache get` to download cached build files that are computed by `mathlib4`'s automated workflow.
If `tar` terminates with an error, it means that you might have ended up with corrupted files.
In this case, run `lake exe cache get!` to overwrite them (`get` won't try to download the same file again).

Call `lake exe cache` to see its help menu.

### Building HTML documentation

Building HTML documentation locally is straightforward:

```shell
lake -Kdoc=on build Mathlib:docs
```

The HTML files can then be found in `build/doc`.

### Dependencies

If you are a mathlib contributor and want to update dependencies, use `lake update -Kdoc=on`.
This will update the `lake-manifest.json` file correctly.
You will need to make a PR after committing the changes to this file.

## Using `mathlib4` as a dependency

Please refer to
[https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
