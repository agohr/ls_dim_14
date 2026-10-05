import QuaternionicSymmetry.QuarticOrbitalEleven

/-! Exact symbolic quartic orbital separators at dimensions 13 and 14.

The five vectors below are the power-sum coefficients of the degree-four
Schur functions, ordered by the partitions `(4)`, `(3,1)`, `(2,2)`,
`(2,1,1)`, `(1,1,1,1)`. The polynomial variables are the first four
power sums of an arbitrary spectrum. No sample spectrum or analytic orbital
integral is used.
-/

namespace QuaternionicSymmetry.QuarticOrbitalSeparators

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 4) ℚ

private def A1 : P := X 0
private def A2 : P := X 1
private def A3 : P := X 2
private def A4 : P := X 3

/-- Polynomial in the ordered quartic power-sum basis. -/
def quartic (c : Fin 5 → ℚ) : P :=
  C (c 0) * A1 ^ 4 + C (c 1) * A1 ^ 2 * A2 + C (c 2) * A2 ^ 2 +
    C (c 3) * A1 * A3 + C (c 4) * A4

def s4 : Fin 5 → ℚ := ![1/24, 1/4, 1/8, 1/3, 1/4]
def s31 : Fin 5 → ℚ := ![1/8, 1/4, -1/8, 0, -1/4]
def s22 : Fin 5 → ℚ := ![1/12, 0, 1/4, -1/3, 0]
def s211 : Fin 5 → ℚ := ![1/8, -1/4, -1/8, 0, 1/4]
def s1111 : Fin 5 → ℚ := ![1/24, -1/4, 1/8, 1/3, -1/4]

/-- The coefficient-vector presentation is exactly the Jacobi--Trudi
construction used for the checked dimension-eleven orbital witnesses. -/
theorem schur_vectors :
    quartic s4 = QuarticOrbitalEleven.s₄ ∧
    quartic s31 = QuarticOrbitalEleven.s₃₁ ∧
    quartic s22 = QuarticOrbitalEleven.s₂₂ ∧
    quartic s211 = QuarticOrbitalEleven.s₂₁₁ ∧
    quartic s1111 = QuarticOrbitalEleven.s₁₁₁₁ := by
  constructor
  · apply MvPolynomial.funext
    intro a
    simp [quartic, s4, QuarticOrbitalEleven.s₄,
      QuarticOrbitalEleven.h₄, QuarticOrbitalEleven.p₁,
      QuarticOrbitalEleven.p₂, QuarticOrbitalEleven.p₃,
      QuarticOrbitalEleven.p₄, A1, A2, A3, A4]
    ring
  constructor
  · apply MvPolynomial.funext
    intro a
    simp [quartic, s31, QuarticOrbitalEleven.s₃₁,
      QuarticOrbitalEleven.h₁, QuarticOrbitalEleven.h₃,
      QuarticOrbitalEleven.h₄, QuarticOrbitalEleven.p₁,
      QuarticOrbitalEleven.p₂, QuarticOrbitalEleven.p₃,
      QuarticOrbitalEleven.p₄, A1, A2, A3, A4]
    ring
  constructor
  · apply MvPolynomial.funext
    intro a
    simp [quartic, s22, QuarticOrbitalEleven.s₂₂,
      QuarticOrbitalEleven.h₂, QuarticOrbitalEleven.h₃,
      QuarticOrbitalEleven.h₁, QuarticOrbitalEleven.p₁,
      QuarticOrbitalEleven.p₂, QuarticOrbitalEleven.p₃,
      A1, A2, A3, A4]
    ring
  constructor
  · apply MvPolynomial.funext
    intro a
    simp [quartic, s211, QuarticOrbitalEleven.s₂₁₁,
      QuarticOrbitalEleven.h₁, QuarticOrbitalEleven.h₂,
      QuarticOrbitalEleven.h₃, QuarticOrbitalEleven.h₄,
      QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
      QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄,
      A1, A2, A3, A4]
    ring
  · apply MvPolynomial.funext
    intro a
    simp [quartic, s1111, QuarticOrbitalEleven.s₁₁₁₁,
      QuarticOrbitalEleven.h₁, QuarticOrbitalEleven.h₂,
      QuarticOrbitalEleven.h₃, QuarticOrbitalEleven.h₄,
      QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
      QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄,
      A1, A2, A3, A4]
    ring

/-- Every type-C factor used below is recovered from the same factorial
formula as the dimension-eleven and -twelve witnesses. -/
theorem rho13_factorials :
    256 * QuarticOrbitalEleven.factorialRho 13 [4] = (1 / 2186754570 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 13 [3, 1] = (2 / 2484948375 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 13 [2, 2] = (2 / 1875735225 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 13 [2, 1, 1] = (2 / 1352025675 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 13 [1, 1, 1, 1] =
      (2 / 699323625 : ℚ) := by
  norm_num [QuarticOrbitalEleven.factorialRho, Nat.factorial]

theorem rho14_factorials :
    256 * QuarticOrbitalEleven.factorialRho 14 [4] = (1 / 3706891650 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 14 [3, 1] = (1 / 2186754570 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 14 [2, 2] = (4 / 6725926935 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 14 [2, 1, 1] = (2 / 2484948375 : ℚ) ∧
    256 * QuarticOrbitalEleven.factorialRho 14 [1, 1, 1, 1] =
      (2 / 1352025675 : ℚ) := by
  norm_num [QuarticOrbitalEleven.factorialRho, Nat.factorial]

/-- A functional on the ordered quartic power-sum coefficients. -/
def pair (v c : Fin 5 → ℚ) : ℚ :=
  v 0 * c 0 + v 1 * c 1 + v 2 * c 2 + v 3 * c 3 + v 4 * c 4

def L13 : Fin 5 → ℚ := ![32231, -53169, 301931, -19969, 81681]
def L14 : Fin 5 → ℚ := ![33248, -94256, 878742, -28008, 227741]

/-- The five `4⁴ ρ_λ` factors in the normalized type-C orbital polynomial. -/
def orbitalImage13 : P :=
  C (pair L13 s4 / 2186754570) * quartic s4 +
  C (2 * pair L13 s31 / 2484948375) * quartic s31 +
  C (2 * pair L13 s22 / 1875735225) * quartic s22 +
  C (2 * pair L13 s211 / 1352025675) * quartic s211 +
  C (2 * pair L13 s1111 / 699323625) * quartic s1111

def orbitalImage14 : P :=
  C (pair L14 s4 / 3706891650) * quartic s4 +
  C (pair L14 s31 / 2186754570) * quartic s31 +
  C (4 * pair L14 s22 / 6725926935) * quartic s22 +
  C (2 * pair L14 s211 / 2484948375) * quartic s211 +
  C (2 * pair L14 s1111 / 1352025675) * quartic s1111

/-- The n=13 separating functional is a square on every formal spectrum. -/
theorem orbitalImage13_eq_square :
    orbitalImage13 = C (1 / 221130) * (3 * A2 - A1 ^ 2) ^ 2 := by
  apply MvPolynomial.funext
  intro a
  simp [orbitalImage13, pair, quartic, L13, s4, s31, s22, s211,
    s1111, A1, A2, A3, A4]
  ring

/-- The n=14 separating functional is a square on every formal spectrum. -/
theorem orbitalImage14_eq_square :
    orbitalImage14 = C (1 / 246645) * (4 * A2 - A1 ^ 2) ^ 2 := by
  apply MvPolynomial.funext
  intro a
  simp [orbitalImage14, pair, quartic, L14, s4, s31, s22, s211,
    s1111, A1, A2, A3, A4]
  ring

/-- The symbolic separator identities persist after substitution into any
commutative rational algebra, including one with nilpotents. -/
theorem orbitalImage13_eq_square_eval {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : Fin 4 → R) :
    aeval a orbitalImage13 =
      algebraMap ℚ R (1 / 221130) * (3 * a 1 - a 0 ^ 2) ^ 2 := by
  rw [orbitalImage13_eq_square]
  simp [A1, A2]

theorem orbitalImage14_eq_square_eval {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : Fin 4 → R) :
    aeval a orbitalImage14 =
      algebraMap ℚ R (1 / 246645) * (4 * a 1 - a 0 ^ 2) ^ 2 := by
  rw [orbitalImage14_eq_square]
  simp [A1, A2]

/-- Both separating functionals are nonnegative on every real formal
spectrum; in particular they are nonnegative on nonnegative spectra. -/
theorem orbitalImage13_nonneg (a : Fin 4 → ℝ) :
    0 ≤ aeval a orbitalImage13 := by
  rw [orbitalImage13_eq_square_eval]
  positivity

theorem orbitalImage14_nonneg (a : Fin 4 → ℝ) :
    0 ≤ aeval a orbitalImage14 := by
  rw [orbitalImage14_eq_square_eval]
  positivity

/-- The exact quartic coefficient vectors independently printed by the
rational reconstruction script. Their derivation from the universal density
recurrence is a separate obligation. -/
def target13 : Fin 5 → ℚ :=
  ![9911/127575, 16042/212625, 26423/4465125, 284456/16372125, 8894/19348875]
def target14 : Fin 5 → ℚ :=
  ![4904/42525, 23024/212625, 36256/4465125, 1084576/49116375, -170152/212837625]

theorem pair_target13 : pair L13 target13 = -6426988888 / 212837625 := by
  change (32231 : ℚ) * (9911 / 127575) + (-53169) * (16042 / 212625) +
    301931 * (26423 / 4465125) + (-19969) * (284456 / 16372125) +
    81681 * (8894 / 19348875) = _
  norm_num

theorem pair_target14 : pair L14 target14 = -80840728 / 2149875 := by
  change (33248 : ℚ) * (4904 / 42525) + (-94256) * (23024 / 212625) +
    878742 * (36256 / 4465125) +
    (-28008) * (1084576 / 49116375) + 227741 * (-170152 / 212837625) = _
  norm_num

end
end QuaternionicSymmetry.QuarticOrbitalSeparators
