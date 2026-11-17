/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shingai Thornton
-/
/-
# Rosen's (M,R)-systems: when replication comes "for free"

Source: Louie, A. H. (2012). Anticipation in (M,R)-systems. International Journal of General
Systems 41(1), 5–22, pp. 7–9. doi:10.1080/03081079.2011.622088. The construction is Rosen's;
Louie's paper is the statement used here.

## The model

Louie's simplest (M,R)-system is the chain

    A --f--> B --Φ--> H(A,B)

with metabolism `f ∈ H(A,B)` and repair `Φ ∈ H(B, H(A,B))`. A replication map
`β : H(A,B) → H(B, H(A,B))` is obtained by inverting evaluation at a point `b ∈ B` (`Φ ↦ Φ b`),
which is possible, in Rosen's words as Louie quotes them (p. 8), "under stringent but not
prohibitively strong conditions".

The hom-sets are predicates on function types (`Network`): `Met f` says `f ∈ H(A,B)` and `Rep Φ`
says `Φ ∈ H(B, H(A,B))`. Which maps are admissible is the modelling choice the theorems turn on.

## What is proved here, and from what

* `replicates_iff_evalInjective`: replication at `b` exists **if and only if** evaluation at `b`
  is one-to-one on the admissible repairs (`EvalInjective`). The condition is necessary as well
  as sufficient.
* `not_replicates_full`: if every map `B → (A → B)` counts as a repair, `B` has a second point
  and there are two different maps `A → B`, replication at `b` does not exist.
* `replicates_constant`: if only constant repairs are admissible, replication exists at every `b`.

So "replication comes for free" holds under one reading of the hom-set of repairs and fails under
another. `witness` shows the hypothesis `EvalInjective` is satisfiable.

Prior work: Letelier, Soto-Andrade, Guíñez Abarzúa, Cornish-Bowden & Cárdenas (2006), Journal of
Theoretical Biology 238(4), 949–961, doi:10.1016/j.jtbi.2005.07.007, state the one-to-one
condition in prose and attribute it to Rosen (p. 955, footnote 11).

## What is not proved here

* Nothing about organisms: that a cell realises an (M,R)-system, or which reading of the hom-sets
  a living system realises, is an empirical question.
* Nothing about other encodings: category-theoretic, λ-calculus and process-algebra encodings of
  (M,R)-systems are not covered.
* Nothing about closure to efficient causation or computability.

No `sorry`, no additional axioms: see `lean/Delphi/Audit.lean`.
-/
import Mathlib

namespace Delphi.Relational

/-- An (M,R)-network in Louie's simplest form, `A --f--> B --Φ--> H(A,B)`. The hom-sets are
predicates: `Met f` says `f` is an admissible metabolism, `Rep Φ` says `Φ` is an admissible
repair. -/
structure Network (A B : Type*) where
  /-- The admissible metabolisms, `H(A,B)`, as a predicate on maps `A → B`. -/
  Met : (A → B) → Prop
  /-- The admissible repairs, `H(B, H(A,B))`, as a predicate on maps `B → (A → B)`. -/
  Rep : (B → A → B) → Prop

variable {A B : Type*}

/-- Replication at `b`: a map `β` from metabolisms to repairs that recovers every admissible
repair `Φ` from the metabolism `Φ b` it produces at `b`. -/
def Replicates (N : Network A B) (b : B) : Prop :=
  ∃ β : (A → B) → (B → A → B), ∀ Φ, N.Rep Φ → β (Φ b) = Φ

/-- Rosen's condition, the named hypothesis of the law: evaluation at `b` (`Φ ↦ Φ b`) is
one-to-one on the admissible repairs. -/
def EvalInjective (N : Network A B) (b : B) : Prop :=
  ∀ Φ Ψ, N.Rep Φ → N.Rep Ψ → Φ b = Ψ b → Φ = Ψ

/-- **The replication condition.** In an (M,R)-network, replication at `b` exists if and only if
evaluation at `b` is one-to-one on the admissible repairs. The left-hand side is `Replicates N b`
written out, so the statement can be read without unfolding a definition. -/
theorem replicates_iff_evalInjective (N : Network A B) (b : B) :
    (∃ β : (A → B) → (B → A → B), ∀ Φ, N.Rep Φ → β (Φ b) = Φ) ↔ EvalInjective N b := by
  constructor
  · rintro ⟨β, hβ⟩ Φ Ψ hΦ hΨ h
    rw [← hβ Φ hΦ, ← hβ Ψ hΨ, h]
  · intro hinj
    classical
    refine ⟨fun f => if h : ∃ Φ, N.Rep Φ ∧ Φ b = f then Classical.choose h else fun _ => f, ?_⟩
    intro Φ hΦ
    have h : ∃ Ψ, N.Rep Ψ ∧ Ψ b = Φ b := ⟨Φ, hΦ, rfl⟩
    simp only [h, ↓reduceDIte]
    have hs := Classical.choose_spec h
    exact hinj _ _ hs.1 hΦ hs.2

/-- The full-function-space reading: every map `B → (A → B)` counts as a repair. -/
def full (Met : (A → B) → Prop) : Network A B where
  Met := Met
  Rep := fun _ => True

/-- **No free replication under the full reading.** If every map counts as a repair, `B` has a
second point `b' ≠ b` and there are two different maps `f ≠ g` from `A` to `B`, then replication
at `b` does not exist. -/
theorem not_replicates_full (Met : (A → B) → Prop) (b b' : B) (hb : b' ≠ b)
    (f g : A → B) (hfg : f ≠ g) : ¬ Replicates (full Met) b := by
  unfold Replicates
  rw [replicates_iff_evalInjective]
  intro hinj
  classical
  have h := hinj (fun _ => f) (fun x => if x = b then f else g) trivial trivial (by simp)
  have h' := congrFun h b'
  simp only [hb, ↓reduceIte] at h'
  exact hfg h'

/-- A restricted reading: only constant repairs are admissible (the same metabolism rebuilt
from any input). -/
def constant (Met : (A → B) → Prop) : Network A B where
  Met := Met
  Rep := fun Φ => ∃ f, Met f ∧ Φ = fun _ => f

/-- **Replication under the constant-repair reading.** If only constant repairs are admissible,
replication exists at every `b`. -/
theorem replicates_constant (Met : (A → B) → Prop) (b : B) :
    Replicates (constant Met) b := by
  unfold Replicates
  rw [replicates_iff_evalInjective]
  rintro Φ Ψ ⟨f, -, rfl⟩ ⟨g, -, rfl⟩ h
  simp only at h
  rw [h]

/-- A concrete network on `Bool` satisfying the hypothesis `EvalInjective` at a point `b`, together
with a repair `Φ` that is actually admissible, so the hypothesis is not satisfied emptily. -/
structure Instance where
  N : Network Bool Bool
  b : Bool
  inj : EvalInjective N b
  Φ : Bool → Bool → Bool
  hΦ : N.Rep Φ

/-- Non-vacuity witness: the constant-repair network on `Bool`, with every map a metabolism,
satisfies `EvalInjective` at `true` and has an admissible repair. -/
theorem witness : Nonempty Instance :=
  ⟨{ N := constant fun _ => True
     b := true
     inj := (replicates_iff_evalInjective _ _).mp (replicates_constant _ _)
     Φ := fun _ => id
     hΦ := ⟨id, trivial, rfl⟩ }⟩

end Delphi.Relational
