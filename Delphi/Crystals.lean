import Mathlib

/-!
# Crystal laws

Registry port of the crystal theorems in
`claim-sources/thompson-growth-form/lean/ThompsonLaws/Crystals.lean` (claims in
`claim-sources/crystals-and-form/claims.json`: Bravais 1850, the Braggs 1913–1915). Three laws:

* `crystallographic_restriction` (bravais1850-01): a lattice has only 1-, 2-, 3-, 4- or 6-fold
  rotation axes;
* `tetrahedral_cos` (bragg1915-03, and Thompson's four-rayed spicule, thompson1917-ch09-10): the
  angle between any two bonds of the diamond lattice has cosine exactly `-1/3`;
* `bragg_ratio` (bragg1913s-01): under Bragg's law `n λ = 2 d sin θ` on a cubic lattice, the sines
  of the `(100)`, `(110)`, `(111)` glancing angles stand as `1 : √2 : √3`.

Each is a theorem about an ideal lattice; whether a mineral or a spicule obeys it is for the data
tests in `test-data/claim-tests/`. The statements are kept identical to the claim-source module so
the two stay provably the same object; the witnesses are the registry's non-vacuity requirement.
-/

namespace Delphi.Crystals

noncomputable section

open Real Matrix

/-! ## The crystallographic restriction -/

/-- The arithmetic heart: `2 cos (2π/n)` is an integer only for `n = 1, 2, 3, 4, 6`. -/
theorem two_cos_two_pi_div_int (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : 2 * cos (2 * π / n) = m) : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hπ : 0 < π := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
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
    · exfalso
      have c1 : cos (2 * π / (5 : ℕ)) < cos (π / 3) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two <;> push_cast <;> nlinarith
      have c2 : cos (π / 2) < cos (2 * π / (5 : ℕ)) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two <;> push_cast <;> nlinarith
      rw [Real.cos_pi_div_three] at c1
      rw [Real.cos_pi_div_two] at c2
      exact key 0 1 (by linarith) (by linarith) 0 (by norm_num) (by norm_num)
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exfalso
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
entries `M`. -/
def IsLatticeRotation (θ : ℝ) : Prop :=
  ∃ (P : (Matrix (Fin 2) (Fin 2) ℝ)ˣ) (M : Matrix (Fin 2) (Fin 2) ℤ),
    rot θ = (P : Matrix (Fin 2) (Fin 2) ℝ) * M.map (Int.cast : ℤ → ℝ) * (P⁻¹ : (Matrix (Fin 2) (Fin 2) ℝ)ˣ)

/-- The trace of a lattice rotation is an integer. -/
theorem IsLatticeRotation.trace_int {θ : ℝ} (h : IsLatticeRotation θ) : ∃ m : ℤ, 2 * cos θ = m := by
  obtain ⟨P, M, hM⟩ := h
  refine ⟨trace M, ?_⟩
  rw [← trace_rot, hM, Matrix.trace_units_conj]
  simp [Matrix.trace, Matrix.diag]

/-- **The crystallographic restriction.** An `n`-fold rotation axis of a plane lattice has
`n ∈ {1, 2, 3, 4, 6}`: no five-fold axis, none of order seven or more. -/
theorem crystallographic_restriction (n : ℕ) (hn : 0 < n)
    (h : IsLatticeRotation (2 * π / n)) : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  obtain ⟨m, hm⟩ := h.trace_int
  exact two_cos_two_pi_div_int n hn m hm

/-- The four-fold rotation (by `π/2`) is a lattice rotation of the square lattice, with integer
matrix `!![0, -1; 1, 0]` in the standard basis. -/
theorem fourfold_is_lattice_rotation : IsLatticeRotation (2 * π / (4 : ℕ)) := by
  refine ⟨1, !![0, -1; 1, 0], ?_⟩
  have : (2 : ℝ) * π / (4 : ℕ) = π / 2 := by push_cast; ring
  rw [this]
  simp [rot, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Non-vacuity: the hypotheses of `crystallographic_restriction` are satisfiable (`n = 4`). -/
theorem crystallographic_restriction_witness : ∃ n : ℕ, 0 < n ∧ IsLatticeRotation (2 * π / n) :=
  ⟨4, by norm_num, fourfold_is_lattice_rotation⟩

/-! ## The tetrahedral angle -/

/-- Dot product on `Fin 3 → ℝ`. -/
def dot (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

/-- The four bond directions of the diamond lattice, as multiples of the cube edge `a`:
`(a/4)(±1, ±1, ±1)` with an even number of minus signs. -/
def bond (a : ℝ) : Fin 4 → (Fin 3 → ℝ)
  | 0 => fun i => a / 4 * ![1, 1, 1] i
  | 1 => fun i => a / 4 * ![1, -1, -1] i
  | 2 => fun i => a / 4 * ![-1, 1, -1] i
  | 3 => fun i => a / 4 * ![-1, -1, 1] i

/-- Every bond has squared length `3a²/16`. -/
theorem bond_sq (a : ℝ) (i : Fin 4) : dot (bond a i) (bond a i) = 3 * a ^ 2 / 16 := by
  fin_cases i <;> simp [dot, bond, Fin.sum_univ_three] <;> ring

/-- Any two distinct bonds have dot product `-a²/16`. -/
theorem bond_dot (a : ℝ) (i j : Fin 4) (hij : i ≠ j) : dot (bond a i) (bond a j) = -(a ^ 2) / 16 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (simp [dot, bond, Fin.sum_univ_three]; ring)

/-- Cosine of the angle between two vectors. -/
def cosAngle (v w : Fin 3 → ℝ) : ℝ := dot v w / (Real.sqrt (dot v v) * Real.sqrt (dot w w))

/-- **The tetrahedral angle.** For any cube edge `a > 0` and any two distinct bonds, the cosine of
the bond angle is exactly `-1/3`, independent of `a`. -/
theorem tetrahedral_cos (a : ℝ) (ha : 0 < a) (i j : Fin 4) (hij : i ≠ j) :
    cosAngle (bond a i) (bond a j) = -1 / 3 := by
  unfold cosAngle
  rw [bond_dot a i j hij, bond_sq, bond_sq, ← Real.sqrt_mul (by positivity)]
  have h : (3 * a ^ 2 / 16) * (3 * a ^ 2 / 16) = (3 * a ^ 2 / 16) ^ 2 := by ring
  rw [h, Real.sqrt_sq (by positivity)]
  field_simp

/-- `arccos (-1/3)` lies strictly between a right angle and `120°`. -/
theorem tetrahedral_angle_bounds : π / 2 < arccos (-1 / 3) ∧ arccos (-1 / 3) < 2 * π / 3 := by
  constructor
  · rw [Real.pi_div_two_lt_arccos]; norm_num
  · have h1 : arccos (-(1 / 2 : ℝ)) = 2 * π / 3 := by
      rw [Real.arccos_neg, ← Real.cos_pi_div_three, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
      ring
    rw [← h1]
    apply Real.strictAntiOn_arccos <;> norm_num [Set.mem_Icc]

/-- Non-vacuity: the hypotheses of `tetrahedral_cos` are satisfiable (`a = 1`, bonds 0 and 1). -/
theorem tetrahedral_cos_witness : ∃ a : ℝ, 0 < a ∧ cosAngle (bond a 0) (bond a 1) = -1 / 3 :=
  ⟨1, one_pos, tetrahedral_cos 1 one_pos 0 1 (by decide)⟩

/-! ## Bragg's law on a cubic lattice -/

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

/-- **Bragg's `(100) : (110) : (111)` ratio.** For the same order and wavelength,
`sin θ₁₁₀ = √2 sin θ₁₀₀` and `sin θ₁₁₁ = √3 sin θ₁₀₀`. -/
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

/-- Non-vacuity: the hypotheses of `bragg_ratio` are satisfiable: `a = 1`, first order, `λ = 2`
and a glancing angle of `π/2` on `(100)`. -/
theorem bragg_ratio_witness : ∃ (a lam θ : ℝ) (n : ℕ), 0 < a ∧ BraggReflects n lam (dSpacing a 1 0 0) θ := by
  refine ⟨1, 2, π / 2, 1, one_pos, ?_⟩
  simp [BraggReflects, dSpacing]

end

end Delphi.Crystals
