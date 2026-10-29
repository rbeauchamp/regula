# `lakefile.toml` lint example

A minimal adopter in the `lakefile.toml` format, which imports only the core of Lean. `lintDriver = "regula/lint"` runs Regula's checker over the finished build of each manifested surface. Here the surface is the `Gadget` library, claimed `choice-free` with `report` execution.

From this directory:

```sh
lake update
lake build --wfail
lake lint
```

To use it in a different place, replace `path = "../.."` with the Git form of the [adoption guide](../../docs/guides/adoption.md#1-require-regula). Use `lake build --wfail` and then `lake lint` locally and in CI.
