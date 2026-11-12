/-
Copyright (c) 2026 Joel Dietz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joel Dietz
-/
import Mathlib

/-!
# Crystals and form

Formalizations of the mathematical core of claims in `claim-sources/crystals-and-form/claims.json`
(Steno 1669, Haüy 1801, Bravais 1850, the Braggs 1913–1915). They live in the Thompson Lake project
for the same reason the hygromorph claims do: Lean reports are keyed by claim id across projects and
a second Mathlib checkout would be large.

Each theorem is about an ideal lattice. None of them says that rock salt, calcite or a sponge
spicule obeys it; that is what the data tests in `test-data/claim-tests/crystals-and-form/` and
`thompson-growth-form/thompson1917-ch09-10` are for. `crystals/obey.mjs` checks whether the drawn
structures in the film obey the exact constants proved here.
-/

namespace ThompsonLaws.Crystals

noncomputable section

open Real Matrix

/-! ## bravais1850-01: the crystallographic restriction

A lattice can only have two-, three-, four- or six-fold rotation axes. The argument is Bravais'
own: a rotation that maps a lattice to itself has an integer matrix in a lattice basis, so its
trace is an integer; in the plane the trace of a rotation by `θ` is `2 cos θ`; and `2 cos (2π/n)`
is an integer only for `n ∈ {1, 2, 3, 4, 6}`. -/

/-- The arithmetic heart: `2 cos (2π/n)` is an integer only for `n = 1, 2, 3, 4, 6`. -/
theorem two_cos_two_pi_div_int (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : 2 * cos (2 * π / n) = m) : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hπ : 0 < π := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- Rule out `n = 5` and `n ≥ 7` by trapping `m` strictly between two integers.
  have key : ∀ (lo hi : ℝ), lo < 2 * cos (2 * π / n) → 2 * cos (2 * π / n) < hi →
      ∀ (a : ℤ), (a : ℝ) = lo → hi = (a : ℝ) + 1 → False := by
    intro lo hi h1 h2 a ha hb
    rw [h, ← ha] at h1
    rw [h, hb] at h2
    have h1' : a < m := by exact_mod_cast h1
    have h2' : m < a + 1 := by exact_mod_cast h2
    omega
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · interval_cases n
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · -- n = 5: π/3 < 2π/5 < π/2, so 0 < 2 cos (2π/5) < 1.
      exfalso
      have c1 : cos (2 * π / (5 : ℕ)) < cos (π / 3) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two <;> push_cast <;> nlinarith
      have c2 : cos (π / 2) < cos (2 * π / (5 : ℕ)) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two <;> push_cast <;> nlinarith
      rw [Real.cos_pi_div_three] at c1
      rw [Real.cos_pi_div_two] at c2
      exact key 0 1 (by linarith) (by linarith) 0 (by norm_num) (by norm_num)
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · -- n ≥ 7: 0 < 2π/n < π/3, so 1 < 2 cos (2π/n) < 2.
    exfalso
    have hn7 : (7 : ℝ) ≤ n := by exact_mod_cast hge
    have hpos : 0 < 2 * π / n := by positivity
    have hsmall : 2 * π / n < π / 3 := by
      rw [div_lt_div_iff₀ hn' (by norm_num : (0:ℝ) < 3)]
      nlinarith
    have c1 : cos (2 * π / n) < cos 0 := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) <;> linarith
    have c2 : cos (π / 3) < cos (2 * π / n) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_of_lt hpos) <;> linarith
    rw [Real.cos_zero] at c1
    rw [Real.cos_pi_div_three] at c2
    exact key 1 2 (by linarith) (by linarith) 1 (by norm_num) (by norm_num)

/-- The plane rotation by `θ`. -/
def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos θ, -sin θ; sin θ, cos θ]

/-- Its trace is `2 cos θ`. -/
theorem trace_rot (θ : ℝ) : trace (rot θ) = 2 * cos θ := by
  simp [rot, Matrix.trace_fin_two]; ring

/-- A symmetry of a plane lattice: a rotation whose matrix in some lattice basis `P` has integer
entries `M`. (`P` is the change of basis from lattice coordinates to Cartesian ones.) -/
def IsLatticeRotation (θ : ℝ) : Prop :=
  ∃ (P : (Matrix (Fin 2) (Fin 2) ℝ)ˣ) (M : Matrix (Fin 2) (Fin 2) ℤ),
    rot θ = (P : Matrix (Fin 2) (Fin 2) ℝ) * M.map (Int.cast : ℤ → ℝ) * (P⁻¹ : (Matrix (Fin 2) (Fin 2) ℝ)ˣ)

/-- The trace of a lattice rotation is an integer. -/
theorem IsLatticeRotation.trace_int {θ : ℝ} (h : IsLatticeRotation θ) : ∃ m : ℤ, 2 * cos θ = m := by
  obtain ⟨P, M, hM⟩ := h
  refine ⟨trace M, ?_⟩
  rw [← trace_rot, hM, Matrix.trace_units_conj]
  simp [Matrix.trace, Matrix.diag]

/-- **The crystallographic restriction** (bravais1850-01). An `n`-fold rotation axis of a plane
lattice has `n ∈ {1, 2, 3, 4, 6}`: no five-fold axis, none of order seven or more. -/
theorem crystallographic_restriction (n : ℕ) (hn : 0 < n)
    (h : IsLatticeRotation (2 * π / n)) : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨m, hm⟩ := h.trace_int
  exact two_cos_two_pi_div_int n hn m hm

/-- Non-vacuity: the four-fold rotation (by `π/2`) is a lattice rotation of the square lattice,
with integer matrix `!![0, -1; 1, 0]` in the standard basis. -/
theorem fourfold_is_lattice_rotation : IsLatticeRotation (2 * π / (4 : ℕ)) := by
  refine ⟨1, !![0, -1; 1, 0], ?_⟩
  have : (2 : ℝ) * π / (4 : ℕ) = π / 2 := by push_cast; ring
  rw [this]
  simp [rot, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ## bragg1915-03 and thompson1917-ch09-10: the tetrahedral angle

In diamond each carbon has four neighbours at the corners of a regular tetrahedron; the angle
between any two bonds is `arccos (-1/3) ≈ 109.47°`. Thompson's four-rayed sponge spicules, rays
meeting at the junction of four equal cells, are claimed to make the same angle. -/

/-- Dot product on `Fin 3 → ℝ`. -/
def dot (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

/-- The four bond directions of the diamond lattice, as multiples of the cube edge `a`:
`(a/4)(±1, ±1, ±1)` with an even number of minus signs. -/
def bond (a : ℝ) : Fin 4 → (Fin 3 → ℝ)
  | 0 => fun i => a / 4 * ![1, 1, 1] i
  | 1 => fun i => a / 4 * ![1, -1, -1] i
  | 2 => fun i => a / 4 * ![-1, 1, -1] i
  | 3 => fun i => a / 4 * ![-1, -1, 1] i

/-- Every bond has squared length `3a²/16`, i.e. length `a√3/4` (1.54 Å for `a = 3.56 Å`). -/
theorem bond_sq (a : ℝ) (i : Fin 4) : dot (bond a i) (bond a i) = 3 * a ^ 2 / 16 := by
  fin_cases i <;> simp [dot, bond, Fin.sum_univ_three] <;> ring

/-- Any two distinct bonds have dot product `-a²/16`. -/
theorem bond_dot (a : ℝ) (i j : Fin 4) (hij : i ≠ j) : dot (bond a i) (bond a j) = -(a ^ 2) / 16 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (simp [dot, bond, Fin.sum_univ_three]; ring)

/-- Cosine of the angle between two vectors. -/
def cosAngle (v w : Fin 3 → ℝ) : ℝ := dot v w / (Real.sqrt (dot v v) * Real.sqrt (dot w w))

/-- **The tetrahedral angle.** For any cube edge `a > 0` and any two distinct bonds, the cosine of
the bond angle is exactly `-1/3`; the angle is `arccos (-1/3)`, independent of `a`. -/
theorem tetrahedral_cos (a : ℝ) (ha : 0 < a) (i j : Fin 4) (hij : i ≠ j) :
    cosAngle (bond a i) (bond a j) = -1 / 3 := by
  unfold cosAngle
  rw [bond_dot a i j hij, bond_sq, bond_sq, ← Real.sqrt_mul (by positivity)]
  have h : (3 * a ^ 2 / 16) * (3 * a ^ 2 / 16) = (3 * a ^ 2 / 16) ^ 2 := by ring
  rw [h, Real.sqrt_sq (by positivity)]
  field_simp

/-- `arccos (-1/3)` lies strictly between a right angle and `120°`: the bonds are neither
perpendicular nor coplanar at `120°` (the three-rayed spicule's angle). -/
theorem tetrahedral_angle_bounds : π / 2 < arccos (-1 / 3) ∧ arccos (-1 / 3) < 2 * π / 3 := by
  constructor
  · rw [Real.pi_div_two_lt_arccos]; norm_num
  · have h1 : arccos (-(1 / 2 : ℝ)) = 2 * π / 3 := by
      rw [Real.arccos_neg, ← Real.cos_pi_div_three, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
      ring
    rw [← h1]
    apply Real.strictAntiOn_arccos <;> norm_num [Set.mem_Icc]

/-- The three-rayed case: three coplanar rays at `120°` have pairwise cosine `-1/2`. -/
theorem triradiate_cos : cos (2 * π / 3) = -1 / 2 := by
  have : 2 * π / 3 = π - π / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

/-! ## bragg1913s-01: Bragg's law on a cubic lattice

`n λ = 2 d sin θ`. In a cubic lattice of edge `a` the spacing of the `(hkl)` planes is
`a / √(h² + k² + l²)`, so the sines of the glancing angles for `(100)`, `(110)` and `(111)`
stand as `1 : √2 : √3`. That ratio is what Bragg measured in 1913 to tell face-centred from
simple cubic. -/

/-- Spacing of the `(hkl)` planes in a cubic lattice of edge `a`. -/
def dSpacing (a : ℝ) (h k l : ℤ) : ℝ := a / Real.sqrt ((h : ℝ) ^ 2 + k ^ 2 + l ^ 2)

/-- Bragg's condition for order `n`: `n λ = 2 d sin θ`. -/
def BraggReflects (n : ℕ) (lam d θ : ℝ) : Prop := (n : ℝ) * lam = 2 * d * sin θ

/-- Under Bragg's law, `sin θ` for the `(hkl)` reflection is `n λ √(h²+k²+l²) / (2a)`. -/
theorem sin_of_bragg (a lam θ : ℝ) (n : ℕ) (h k l : ℤ) (ha : 0 < a)
    (hhkl : (0 : ℝ) < (h : ℝ) ^ 2 + k ^ 2 + l ^ 2)
    (hb : BraggReflects n lam (dSpacing a h k l) θ) :
    sin θ = n * lam * Real.sqrt ((h : ℝ) ^ 2 + k ^ 2 + l ^ 2) / (2 * a) := by
  unfold BraggReflects dSpacing at hb
  have hs : 0 < Real.sqrt ((h : ℝ) ^ 2 + k ^ 2 + l ^ 2) := Real.sqrt_pos.mpr hhkl
  field_simp at hb ⊢
  nlinarith [hb, Real.sq_sqrt hhkl.le]

/-- The `(100) : (110) : (111)` ratio: `sin θ₁₁₀ / sin θ₁₀₀ = √2` and `sin θ₁₁₁ / sin θ₁₀₀ = √3`
for the same order and wavelength. -/
theorem bragg_ratio (a lam θ₁ θ₂ θ₃ : ℝ) (n : ℕ) (ha : 0 < a)
    (h1 : BraggReflects n lam (dSpacing a 1 0 0) θ₁)
    (h2 : BraggReflects n lam (dSpacing a 1 1 0) θ₂)
    (h3 : BraggReflects n lam (dSpacing a 1 1 1) θ₃) :
    sin θ₂ = Real.sqrt 2 * sin θ₁ ∧ sin θ₃ = Real.sqrt 3 * sin θ₁ := by
  have e1 := sin_of_bragg a lam θ₁ n 1 0 0 ha (by norm_num) h1
  have e2 := sin_of_bragg a lam θ₂ n 1 1 0 ha (by norm_num) h2
  have e3 := sin_of_bragg a lam θ₃ n 1 1 1 ha (by norm_num) h3
  norm_num at e1 e2 e3
  rw [e1, e2, e3]
  constructor <;> ring

/-! ## bragg1915-01 and hauy1801-01: the rock-salt cell

Sodium chloride is two interpenetrating face-centred cubic lattices; the nearest Na–Cl distance
is half the cube edge, and a cube of edge `a` holds four formula units, so
`a³ = 4 M / (ρ N_A)`. The constants below are what the film's `rocksalt()` draws. -/

/-- Fractional coordinates of the eight atoms of the conventional rock-salt cell: the four `Na`
at the fcc positions, the four `Cl` shifted by `(1/2, 0, 0)`. -/
def rockSalt : List (Bool × (Fin 3 → ℚ)) :=
  [ (true,  ![0, 0, 0]), (true,  ![1/2, 1/2, 0]), (true,  ![1/2, 0, 1/2]), (true,  ![0, 1/2, 1/2]),
    (false, ![1/2, 0, 0]), (false, ![0, 1/2, 0]), (false, ![0, 0, 1/2]), (false, ![1/2, 1/2, 1/2]) ]

/-- Squared distance in fractional units. -/
def sqDist (v w : Fin 3 → ℚ) : ℚ := ∑ i, (v i - w i) ^ 2

/-- Four of each kind. -/
theorem rockSalt_count : (rockSalt.filter (·.1)).length = 4 ∧ (rockSalt.filter (!·.1)).length = 4 := by
  decide

/-- The nearest `Na` to the `Cl` at `(1/2, 0, 0)` is at squared distance `1/4`: the Na–Cl bond is
`a/2` (2.81 Å for `a = 5.63 Å`). -/
theorem rockSalt_nn : sqDist ![1/2, 0, 0] ![0, 0, 0] = 1 / 4 := by
  simp [sqDist, Fin.sum_univ_three]; norm_num

/-- Bragg's density relation (bragg1915-02): with `Z` formula units per cell, `a³ = Z M / (ρ N_A)`,
so two salts with the same structure have cell volumes in the ratio of their molecular volumes
`M/ρ`. -/
theorem cell_volume_ratio (Z M₁ M₂ ρ₁ ρ₂ NA a₁ a₂ : ℝ) (hZ : 0 < Z) (hN : 0 < NA)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hM₂ : 0 < M₂)
    (h₁ : a₁ ^ 3 = Z * M₁ / (ρ₁ * NA)) (h₂ : a₂ ^ 3 = Z * M₂ / (ρ₂ * NA)) :
    a₁ ^ 3 / a₂ ^ 3 = (M₁ / ρ₁) / (M₂ / ρ₂) := by
  rw [h₁, h₂]
  field_simp

/-! ## steno1669-01: constancy of interfacial angles, in the lattice reading

On a lattice the angle between two faces depends only on their Miller indices and the lattice
metric, never on how large the faces grew. For a cubic lattice the cube–rhombic-dodecahedron
angle `(100)∧(110)` is `45°` and the cube–octahedron angle `(100)∧(111)` is `arccos (1/√3)`,
whatever the edge `a`. -/

/-- Normal to the `(hkl)` plane of a cubic lattice (the metric is a multiple of the identity, so
the normal is the index vector itself, scaled by `1/a`). -/
def cubicNormal (a : ℝ) (h k l : ℤ) : Fin 3 → ℝ := fun i => (1 / a) * ![(h : ℝ), k, l] i

/-- `(100)∧(110)` has cosine `1/√2`: the angle is `45°`, independent of `a`. -/
theorem cube_dodecahedron_cos (a : ℝ) (ha : 0 < a) :
    cosAngle (cubicNormal a 1 0 0) (cubicNormal a 1 1 0) = 1 / Real.sqrt 2 := by
  unfold cosAngle cubicNormal dot
  simp [Fin.sum_univ_three]
  have hb : 0 < a⁻¹ := inv_pos.mpr ha
  rw [show a⁻¹ * a⁻¹ + a⁻¹ * a⁻¹ = 2 * (a⁻¹ * a⁻¹) by ring, Real.sqrt_mul_self hb.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul_self hb.le]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  field_simp

/-- `(100)∧(111)` has cosine `1/√3`, independent of `a`. -/
theorem cube_octahedron_cos (a : ℝ) (ha : 0 < a) :
    cosAngle (cubicNormal a 1 0 0) (cubicNormal a 1 1 1) = 1 / Real.sqrt 3 := by
  unfold cosAngle cubicNormal dot
  simp [Fin.sum_univ_three]
  have hb : 0 < a⁻¹ := inv_pos.mpr ha
  rw [show a⁻¹ * a⁻¹ + a⁻¹ * a⁻¹ + a⁻¹ * a⁻¹ = 3 * (a⁻¹ * a⁻¹) by ring, Real.sqrt_mul_self hb.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_mul_self hb.le]
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  field_simp

end

/-! ## Computable twins, for export

`claim-sources/crystals-and-form/obey/export.mjs` runs `#eval exportJson` and pins the output to this
file's hash. The rational data below are proved equal to the real-valued definitions above, so what the
film draws is what the theorems are about. -/

/-- The diamond bond directions over `ℚ`, for `a = 1`. -/
def bondQ : Fin 4 → (Fin 3 → ℚ) :=
  ![![1/4, 1/4, 1/4], ![1/4, -1/4, -1/4], ![-1/4, 1/4, -1/4], ![-1/4, -1/4, 1/4]]

/-- `bond a i = a • bondQ i`, coordinate by coordinate. -/
theorem bond_eq_bondQ (a : ℝ) (i : Fin 4) (k : Fin 3) : bond a i k = a * (bondQ i k : ℝ) := by
  fin_cases i <;> fin_cases k <;> simp [bond, bondQ] <;> ring

/-- Exact invariants restated over `ℚ`, each checked by `decide`/`norm_num` on the exported data. -/
theorem bondQ_sq (i : Fin 4) : sqDist (bondQ i) 0 = 3 / 16 := by
  fin_cases i <;> simp [sqDist, bondQ, Fin.sum_univ_three] <;> norm_num

theorem rockSalt_nn_all :
    ∀ p ∈ rockSalt, ∃ q ∈ rockSalt, p.1 ≠ q.1 ∧ sqDist p.2 q.2 = 1 / 4 := by
  simp only [rockSalt, List.forall_mem_cons, List.exists_mem_cons_iff, List.not_mem_nil, sqDist,
    Fin.sum_univ_three]
  norm_num

/-- Rational to `[num, den]`. -/
private def qj (q : ℚ) : String := s!"[{q.num},{q.den}]"
private def vj (v : Fin 3 → ℚ) : String := s!"[{qj (v 0)},{qj (v 1)},{qj (v 2)}]"

/-- The exported JSON. Positions in fractional coordinates; invariants as exact rationals with the
theorem that proves each. -/
def exportJson : String :=
  let rs := ",".intercalate (rockSalt.map fun p => s!"\{\"species\":\"{if p.1 then "Na" else "Cl"}\",\"frac\":{vj p.2}}")
  let bd := ",".intercalate ((List.finRange 4).map fun i => vj (bondQ i))
  "{" ++
  s!"\"rock_salt\":\{\"atoms\":[{rs}],\"invariants\":[" ++
    s!"\{\"name\":\"nearest_unlike_sqdist\",\"value\":{qj (1/4)},\"theorem\":\"ThompsonLaws.Crystals.rockSalt_nn\"}," ++
    s!"\{\"name\":\"atoms_per_species\",\"value\":{qj 4},\"theorem\":\"ThompsonLaws.Crystals.rockSalt_count\"}]}," ++
  s!"\"diamond\":\{\"bonds\":[{bd}],\"invariants\":[" ++
    s!"\{\"name\":\"bond_sqlen\",\"value\":{qj (3/16)},\"theorem\":\"ThompsonLaws.Crystals.bond_sq\"}," ++
    s!"\{\"name\":\"bond_pair_dot\",\"value\":{qj (-1/16)},\"theorem\":\"ThompsonLaws.Crystals.bond_dot\"}," ++
    s!"\{\"name\":\"bond_cos\",\"value\":{qj (-1/3)},\"theorem\":\"ThompsonLaws.Crystals.tetrahedral_cos\"}]}," ++
  s!"\"lattice_rotation_orders\":\{\"allowed\":[1,2,3,4,6],\"theorem\":\"ThompsonLaws.Crystals.crystallographic_restriction\"}," ++
  s!"\"cubic_interfacial_cos_sq\":[\{\"planes\":[\"100\",\"110\"],\"value\":{qj (1/2)},\"theorem\":\"ThompsonLaws.Crystals.cube_dodecahedron_cos\"}," ++
    s!"\{\"planes\":[\"100\",\"111\"],\"value\":{qj (1/3)},\"theorem\":\"ThompsonLaws.Crystals.cube_octahedron_cos\"}]," ++
  s!"\"bragg_sin_sq_ratio\":[\{\"planes\":[\"110\",\"100\"],\"value\":{qj 2},\"theorem\":\"ThompsonLaws.Crystals.bragg_ratio\"}," ++
    s!"\{\"planes\":[\"111\",\"100\"],\"value\":{qj 3},\"theorem\":\"ThompsonLaws.Crystals.bragg_ratio\"}]" ++
  "}"

end ThompsonLaws.Crystals
