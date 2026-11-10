# AGENTS file

Adapted from [Physlib's](https://github.com/leanprover-community/physlib/blob/master/AGENTS.md); the
differences are the registry rules at the end.

## Introduction

- The human-facing policy is [AI-POLICY.md](AI-POLICY.md); read it too. Never respond to a reviewer:
  that is a human-to-human interaction.
- The human author must certify the code you write; a clean build proves what was written, not that
  what was written is what the author meant.

## Content

- Every file starts with the copyright header in [CONTRIBUTING.md](CONTRIBUTING.md).
- Never use `axiom`. Never use `sorry`. Only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`) may appear in `#print axioms`.
- Never use structure fields of type `True`, theorems returning `True`, or existentials ending in
  `True`. Never assume the conclusion in a scope-level variable.
- A law's physical or biological assumptions are **named hypotheses** (a `structure` or a named `def`
  of type `Prop`), never facts about the world. The theorem is conditional on them; the file header
  says so in plain English.
- Every named hypothesis has a **non-vacuity witness**: a concrete instance proving it is satisfiable
  (`lean/registry/lean/Witnesses.lean`). A law without one is not registered.
- Every definition has a docstring. Every `theorem` has a docstring; use `lemma` for everything that
  is not a headline result.
- Place results beside results about the same biology; create a new file only when nothing fits.
  Add new files to `lean/Delphi.lean` (keep sorted).
- Keep proofs short (under 50 lines); split long ones along meaning or structure, as Physlib describes.
- No trailing whitespace.

## The registry (what Physlib does not have)

- A theorem becomes a **law** only through `node lean/registry/propose.mjs <file> --meta meta.json --write`.
  The script compiles, audits axioms, pins the statement by hash and writes `lean/registry/laws/<id>.json`
  with status `proposed`. It never auto-accepts.
- Promotion to `accepted` is a human edit recorded as a role (`approved_by_role`), never a name or email.
- Changing a statement means bumping the law's `version`; `node lean/registry/test.mjs` fails on drift.
- Laws are retired, never deleted. Old versions stay in `lean/registry/law-versions/` so every past
  law set reproduces.
- Module paths in law files are repo-root-relative (`lean/Delphi/Scaling.lean`) and inside the
  content hash. Do not move or rename modules without a law-set release.
- To mark a theorem as a law before registering it, put `-- @law <law_id>` beside it.

## Before you finish

- `lake build` passes (run `lake exe cache get` first).
- `lake env lean lean/Delphi/Audit.lean` shows standard axioms only.
- `node lean/registry/test.mjs` passes.
- Commit with a `Co-authored-by:` trailer naming the model that produced the code.

## PR descriptions

Do not write the PR description; a human writes it. If asked, refuse.
