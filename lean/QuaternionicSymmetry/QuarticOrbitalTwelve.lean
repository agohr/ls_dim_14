import QuaternionicSymmetry.QuarticOrbitalEleven

/-!
# The dimension-twelve quartic orbital certificate

This module reuses the Jacobi--Trudi Schur polynomials and spectrum evaluator
from `QuarticOrbitalEleven`, changing only the factorial orbital normalization,
the five numerical spectra, and the rational witness coefficients.
-/

namespace QuaternionicSymmetry.QuarticOrbitalTwelve

open MvPolynomial QuarticOrbitalEleven
noncomputable section

/-- The weight-four portion of the independent dimension-twelve density,
in the reduced power sums `p_j=z_j/2`. -/
def Q₁₂₄ : P :=
  C (146 / 3645) * p₁ ^ 4 + C (604 / 14175) * p₁ ^ 2 * p₂ +
  C (158 / 42525) * p₂ ^ 2 + C (1616 / 127575) * p₁ * p₃ +
  C (268 / 155925) * p₄

theorem Q₁₂₄_schur :
    Q₁₂₄ = C (15712 / 155925) * s₄ + C (2944 / 18711) * s₃₁ +
      C (3184 / 42525) * s₂₂ + C (35344 / 467775) * s₂₁₁ +
      C (1888 / 155925) * s₁₁₁₁ := by
  apply MvPolynomial.funext
  intro v
  simp [Q₁₂₄, s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁,
    h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]
  ring

def b₁ : List ℕ := QuarticOrbitalEleven.a₁
def b₂ : List ℕ := [1, 1, 1]
def b₃ : List ℕ := QuarticOrbitalEleven.a₂
def b₄ : List ℕ := QuarticOrbitalEleven.a₄
def b₅ : List ℕ := [10, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Each nonnegative integer spectrum fits in the twelve available slots;
missing coordinates are zero. -/
theorem spectra_admissible :
    b₁.length ≤ 12 ∧ b₂.length ≤ 12 ∧ b₃.length ≤ 12 ∧
      b₄.length ≤ 12 ∧ b₅.length ≤ 12 := by
  norm_num [b₁, b₂, b₃, b₄, b₅, QuarticOrbitalEleven.a₁,
    QuarticOrbitalEleven.a₂, QuarticOrbitalEleven.a₄]

theorem schurValues_b₁ : schurValues b₁ = ![5, 3, 1, 0, 0] := by
  exact QuarticOrbitalEleven.schurValues_a₁

theorem schurValues_b₂ : schurValues b₂ = ![15, 15, 6, 3, 0] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, b₂, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

theorem schurValues_b₃ : schurValues b₃ = ![57, 47, 17, 8, 0] := by
  exact QuarticOrbitalEleven.schurValues_a₂

theorem schurValues_b₄ : schurValues b₄ = ![23130, 17910, 5616, 5418, 630] := by
  exact QuarticOrbitalEleven.schurValues_a₄

theorem schurValues_b₅ : schurValues b₅ = ![25645, 22140, 7440, 7470, 966] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, b₅, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

def ρ₄ : ℚ := 1 / 318073392000
def ρ₃₁ : ℚ := 1 / 173059286400
def ρ₂₂ : ℚ := 1 / 127876320000
def ρ₂₁₁ : ℚ := 1 / 89513424000
def ρ₁₁₁₁ : ℚ := 1 / 43609104000

theorem rho_factorials :
    factorialRho 12 [4] = ρ₄ ∧
    factorialRho 12 [3, 1] = ρ₃₁ ∧
    factorialRho 12 [2, 2] = ρ₂₂ ∧
    factorialRho 12 [2, 1, 1] = ρ₂₁₁ ∧
    factorialRho 12 [1, 1, 1, 1] = ρ₁₁₁₁ := by
  norm_num [factorialRho, ρ₄, ρ₃₁, ρ₂₂, ρ₂₁₁, ρ₁₁₁₁, Nat.factorial]

/-- The finite quartic type-C orbital polynomial in dimension twelve. -/
def orbital (a : List ℕ) : P :=
  C (256 * ρ₄ * schurValues a 0) * s₄ +
  C (256 * ρ₃₁ * schurValues a 1) * s₃₁ +
  C (256 * ρ₂₂ * schurValues a 2) * s₂₂ +
  C (256 * ρ₂₁₁ * schurValues a 3) * s₂₁₁ +
  C (256 * ρ₁₁₁₁ * schurValues a 4) * s₁₁₁₁

def c₁ : ℚ := 2298362246 / 9933
def c₂ : ℚ := 194400388184 / 148995
def c₃ : ℚ := 7327263802 / 9933
def c₄ : ℚ := 178334456 / 148995
def c₅ : ℚ := 4485216 / 3311

theorem coefficients_positive : 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ := by
  norm_num [c₁, c₂, c₃, c₄, c₅]

theorem Q₁₂₄_orbital :
    Q₁₂₄ = C c₁ * orbital b₁ + C c₂ * orbital b₂ +
      C c₃ * orbital b₃ + C c₄ * orbital b₄ + C c₅ * orbital b₅ := by
  apply MvPolynomial.funext
  intro v
  rw [Q₁₂₄_schur]
  simp only [orbital, schurValues_b₁, schurValues_b₂, schurValues_b₃,
    schurValues_b₄, schurValues_b₅]
  simp only [Matrix.cons_val]
  simp [c₁, c₂, c₃, c₄, c₅, ρ₄, ρ₃₁, ρ₂₂, ρ₂₁₁, ρ₁₁₁₁]
  ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem Q₁₂₄_orbital_eval (v : Fin 4 → R) :
    aeval v Q₁₂₄ =
      aeval v (C c₁ * orbital b₁ + C c₂ * orbital b₂ +
        C c₃ * orbital b₃ + C c₄ * orbital b₄ + C c₅ * orbital b₅) :=
  congrArg (aeval v) Q₁₂₄_orbital

end
end QuaternionicSymmetry.QuarticOrbitalTwelve
