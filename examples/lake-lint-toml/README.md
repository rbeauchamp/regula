# `lakefile.toml` lint and editor example

A minimal Core-only adopter in `lakefile.toml` format. It shows the two ordinary entry
points of Regula:

- **`lake lint`**: `lintDriver = "regula/lint"` runs the project audit over every
  manifested surface (here the `Gadget` library, choice-free, `report` execution).
- **Editor feedback**: `Gadget/Double.lean` imports `Regula.Linter`, so VS Code with the
  Lean 4 extension shows `Regula.RG…` warnings at their declaration ranges, with a
  **View explanation** link in the infoview and the rule URL in the message text.

From this directory:

```sh
lake update
lake lint
```

Run in place, inside this repository, `regula` is an owned path dependency, since it is in the
same Git work tree. Its `Regula` and `RegulaPolicy` modules are the checker's own code, and the
audit does not own them. It replays and checks the other modules of `regula` that `Gadget`
imports, for example `RegulaCore.EditorPolicy`. The account names `regula` as a trusted
dependency for its own modules.

To use it elsewhere, replace `path = "../.."` with the git form in the
[adoption guide](../../docs/guides/adoption.md#1-require-regula).
`lakefile.toml` cannot declare the custom `policy` target of
[build-lint](../build-lint/README.md), so `lake build` here is an ordinary build, not
enforcement. Use `lake lint` locally and in CI.

A live finding is a compiler warning in the editor and in a plain `lake build`. `lake lint`
builds with live feedback off, whatever the source sets `linter.regula` to, and reports the
same rule as a policy violation (`VIOLATION`, exit 1), also after a plain `lake build` cached
the module with the warning and when the source re-enables it with
`set_option linter.regula true`. Disabling live feedback with `set_option linter.regula false`
does not waive the project check: `lake lint` still reports the violation (exit 1).
`lake exe checkerSelftest --build-bound --partition lint-driver` qualifies these behaviors.
The editor behavior was observed in VS Code on a copy of this example, not proved.
