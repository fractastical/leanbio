# Where LeanBio restates physics that Physlib might already have

Checked 10 November 2026 against [Physlib](https://github.com/leanprover-community/physlib) commit
`31a3730` (10 November 2026, "feat(SpaceAndTime/WaveVectorSpace)"), the whole `Physlib/`,
`PhyslibAlpha/` and `QuantumInfo/` trees. Both libraries pin Mathlib `v4.35.0`, so a dependency
would build. The search was a text search of the `.lean` files for the names below and for
`diffusion`, `surface tension`, `Young–Laplace`, `foam`, `Miller`, `glancing` and `hydrostatic`.

**None of the five laws the README names is a Physlib theorem, so LeanBio does not depend on
Physlib.** The nearest result is recorded under Boyle. This file is the check; it should be redone
when Physlib ships one of these statements.

| law here | what LeanBio actually states | what Physlib has |
|---|---|---|
| Boyle | Not a theorem. `Delphi.Hydro.closed_bladder_rules_out` takes `P(d) · V(d)` constant as the hypothesis `hboyle`, and proves the swim-bladder bound under `P = p0 + ρ g d` (`lean/Delphi/Hydrostatics.lean`). | `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas.ideal_gas_law`: `P * V = n * R * T` with `R = 1`. The next line is a comment that Boyle's law, `P` and `V` inversely proportional at fixed `n`, is a trivial consequence, and the file ends there. No hydrostatic pressure. |
| Fick | Not a theorem. `Delphi.aerobicPower` is the formula `η E Q (Ca − Cv)`, Fick's principle used as a definition (`lean/Delphi/Flight.lean`). | Nothing. No diffusion law and no oxygen-delivery identity. |
| Bragg | `Delphi.Crystals.bragg_ratio`: from `n λ = 2 d sin θ` on a cubic lattice, the sines of the `(100)`, `(110)` and `(111)` angles are in the ratio `1 : √2 : √3`. | Nothing. `Crystal.Bravais` is `ℤᵈ` with primitive vectors and an embedding. No Miller indices, no glancing angle. |
| Crystallographic restriction | `Delphi.Crystals.crystallographic_restriction`: a rotation carrying a plane lattice onto itself has order in `{1, 2, 3, 4, 6}`. | Nothing equating a rotation angle to an integer trace. `Crystal.Symmetry` decomposes a symmetry into a lattice automorphism, a site permutation and offsets, and says the construction is algebraic and needs no Euclidean embedding. |
| Plateau's rules | `Delphi.CellGeometry.tripleJunction_120` and `tetrahedralJunction_angle`: three equal-tension walls meet at 120°, four at `arccos (−1/3)`. | Nothing. No soap films, no surface tension, no triple junction. |

The other laws tagged `kind: physical` (square–cube scaling, wing loading, bending strength, glide
range, altitude, Laplace wall stress of a vessel, the tetrahedral bond angle, hexagonal packing)
were part of the same search. Physlib's Laplace results are the Laplace–Runge–Lenz vector and the
Laplacian, not wall stress, and its crystal `Bond` is a pair of sites in two cells, not a bond
angle.
