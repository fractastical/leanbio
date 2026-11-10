# Contributing

LeanBio follows the conventions of [Physlib](https://github.com/leanprover-community/physlib)
(see [physlib.io/getting-started](https://physlib.io/getting-started)); the differences are in
[AGENTS.md](AGENTS.md).

1. Install Lean via [elan](https://github.com/leanprover/elan), then in the repo root:
   `lake update && lake exe cache get && lake build`.
2. A new law is a Lean file plus a `meta.json`, registered with
   `node lean/registry/propose.mjs <file.lean> --meta meta.json --write`. It enters as `proposed`;
   a human promotes it (see [lean/registry/README.md](lean/registry/README.md)).
3. Every file starts with the copyright header below. If you change a file substantially, add yourself
   to its author list (alphabetical by last name).

```lean
/-
Copyright (c) 2026 <your name>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <your name>
-/
```

If you used an AI tool, read [AI-POLICY.md](AI-POLICY.md) first.
