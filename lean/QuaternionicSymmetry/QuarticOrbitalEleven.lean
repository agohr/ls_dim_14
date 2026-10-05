import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-!
# The dimension-eleven quartic orbital certificate

The power sums `p₁,…,p₄` are independent polynomial variables.  The five
quartic Schur polynomials below are constructed from the complete symmetric
polynomials by the Jacobi--Trudi determinants.  Numerical Schur values are
obtained by substituting the power sums of the stated nonnegative spectra.
The orbital polynomials use the finite type-C formula of Chapter 7 with its
dimension-eleven factorial factors.  No analytic integral or positivity
interpretation is included in these definitions.
-/

namespace QuaternionicSymmetry.QuarticOrbitalEleven

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 4) ℚ

def p₁ : P := X 0
def p₂ : P := X 1
def p₃ : P := X 2
def p₄ : P := X 3

def h₁ : P := p₁
def h₂ : P := (C (1 / 2)) * (p₁ ^ 2 + p₂)
def h₃ : P := (C (1 / 6)) * (p₁ ^ 3 + C 3 * p₁ * p₂ + C 2 * p₃)
def h₄ : P := (C (1 / 24)) *
  (p₁ ^ 4 + C 6 * p₁ ^ 2 * p₂ + C 3 * p₂ ^ 2 + C 8 * p₁ * p₃ + C 6 * p₄)

/-- Newton recurrences characterize these finite complete symmetric
functions in the power-sum alphabet. -/
theorem h₂_newton : 2 * h₂ = p₁ * h₁ + p₂ := by
  apply MvPolynomial.funext
  intro v
  simp [h₁, h₂, p₁, p₂]
  ring

theorem h₃_newton : 3 * h₃ = p₁ * h₂ + p₂ * h₁ + p₃ := by
  apply MvPolynomial.funext
  intro v
  simp [h₁, h₂, h₃, p₁, p₂, p₃]
  ring

theorem h₄_newton : 4 * h₄ = p₁ * h₃ + p₂ * h₂ + p₃ * h₁ + p₄ := by
  apply MvPolynomial.funext
  intro v
  simp [h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]
  ring

/-- The five Schur functions for partitions of four, in Chapter 6 order. -/
def s₄ : P := h₄
def s₃₁ : P := h₃ * h₁ - h₄
def s₂₂ : P := h₂ ^ 2 - h₃ * h₁
def s₂₁₁ : P := h₂ * (h₁ ^ 2 - h₂) - h₃ * h₁ + h₄
def s₁₁₁₁ : P := h₁ ^ 4 - C 3 * h₁ ^ 2 * h₂ + h₂ ^ 2 + C 2 * h₁ * h₃ - h₄

/-- The quartic power-sum target from Chapter 6, with `p_j=z_j/2`. -/
def Q₁₁₄ : P := C (4 / 1403325) *
  (C 8470 * p₁ ^ 4 + C 9207 * p₁ ^ 2 * p₂ + C 825 * p₂ ^ 2 +
    C 2882 * p₁ * p₃ + C 450 * p₄)

/-- The printed Schur-coordinate vector is recovered by polynomial arithmetic. -/
theorem Q₁₁₄_schur :
    Q₁₁₄ =
      C (9704 / 155925) * s₄ + C (44456 / 467775) * s₃₁ +
      C (272 / 6075) * s₂₂ + C (21104 / 467775) * s₂₁₁ +
      C (32 / 4455) * s₁₁₁₁ := by
  apply MvPolynomial.funext
  intro v
  simp [Q₁₁₄, s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁,
    h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]
  ring

/-- Numerical power sums of a finite nonnegative integer spectrum. -/
def powerSum (a : List ℕ) (j : ℕ) : ℚ := (a.map fun x => (x : ℚ) ^ j).sum

def evalSpectrum (a : List ℕ) : P →ₐ[ℚ] ℚ :=
  aeval (fun i => powerSum a (i.val + 1))

def schurValues (a : List ℕ) : Fin 5 → ℚ :=
  ![evalSpectrum a s₄, evalSpectrum a s₃₁, evalSpectrum a s₂₂,
    evalSpectrum a s₂₁₁, evalSpectrum a s₁₁₁₁]

def a₁ : List ℕ := [1, 1]
def a₂ : List ℕ := [2, 1, 1]
def a₃ : List ℕ := [5, 1, 1, 1, 1]
def a₄ : List ℕ := [10, 1, 1, 1, 1, 1, 1, 1, 1]
def a₅ : List ℕ := [10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Each nonnegative integer spectrum fits in the eleven available slots;
missing coordinates are zero. -/
theorem spectra_admissible :
    a₁.length ≤ 11 ∧ a₂.length ≤ 11 ∧ a₃.length ≤ 11 ∧
      a₄.length ≤ 11 ∧ a₅.length ≤ 11 := by
  norm_num [a₁, a₂, a₃, a₄, a₅]

/-- The five integer columns of the Chapter 6 Schur matrix, checked by
substituting the spectra into the Jacobi--Trudi polynomials. -/
theorem schurValues_a₁ : schurValues a₁ = ![5, 3, 1, 0, 0] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, a₁, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

theorem schurValues_a₂ : schurValues a₂ = ![57, 47, 17, 8, 0] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, a₂, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

theorem schurValues_a₃ : schurValues a₃ = ![1510, 1145, 370, 285, 21] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, a₃, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

theorem schurValues_a₄ : schurValues a₄ = ![23130, 17910, 5616, 5418, 630] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, a₄, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

theorem schurValues_a₅ : schurValues a₅ = ![28415, 26985, 9625, 9990, 1410] := by
  funext i
  fin_cases i <;> norm_num [schurValues, evalSpectrum, a₅, powerSum,
    s₄, s₃₁, s₂₂, s₂₁₁, s₁₁₁₁, h₁, h₂, h₃, h₄, p₁, p₂, p₃, p₄]

/-- The dimension-eleven type-C orbital factors, in partition order. -/
def ρ₄ : ℚ := 1 / 173059286400
def ρ₃₁ : ℚ := 1 / 89513424000
def ρ₂₂ : ℚ := 1 / 64521072000
def ρ₂₁₁ : ℚ := 1 / 43609104000
def ρ₁₁₁₁ : ℚ := 1 / 19769460480

/-- The exact type-C factorial factor from the Chapter 7 orbital formula.
The list entries are a partition, and `zipIdx` supplies the zero-based row
index; the formula has the corresponding `i+1` shift. -/
def factorialRho (n : ℕ) (lam : List ℕ) : ℚ :=
  (lam.zipIdx.map fun (part, i) =>
    ((Nat.factorial (2 * (n - (i + 1)) + 1) : ℚ) /
      (Nat.factorial (2 * (part + n - (i + 1)) + 1) : ℚ))).prod

theorem rho_factorials :
    factorialRho 11 [4] = ρ₄ ∧
    factorialRho 11 [3, 1] = ρ₃₁ ∧
    factorialRho 11 [2, 2] = ρ₂₂ ∧
    factorialRho 11 [2, 1, 1] = ρ₂₁₁ ∧
    factorialRho 11 [1, 1, 1, 1] = ρ₁₁₁₁ := by
  norm_num [factorialRho, ρ₄, ρ₃₁, ρ₂₂, ρ₂₁₁, ρ₁₁₁₁, Nat.factorial]

/-- The finite quartic orbital polynomial for an integer spectrum. -/
def orbital (a : List ℕ) : P :=
  C (256 * ρ₄ * schurValues a 0) * s₄ +
  C (256 * ρ₃₁ * schurValues a 1) * s₃₁ +
  C (256 * ρ₂₂ * schurValues a 2) * s₂₂ +
  C (256 * ρ₂₁₁ * schurValues a 3) * s₂₁₁ +
  C (256 * ρ₁₁₁₁ * schurValues a 4) * s₁₁₁₁

def c₁ : ℚ := 1008851484437 / 2142693
def c₂ : ℚ := 151204920425 / 714231
def c₃ : ℚ := 10770035384 / 714231
def c₄ : ℚ := 51654964 / 6428079
def c₅ : ℚ := 252882056 / 1530495

theorem coefficients_positive : 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ := by
  norm_num [c₁, c₂, c₃, c₄, c₅]

/-- The reconstructed five-orbit quartic certificate.  This is an identity
of rational polynomials and hence remains valid after evaluation in every
commutative rational algebra, including those with nilpotents. -/
theorem Q₁₁₄_orbital :
    Q₁₁₄ = C c₁ * orbital a₁ + C c₂ * orbital a₂ +
      C c₃ * orbital a₃ + C c₄ * orbital a₄ + C c₅ * orbital a₅ := by
  apply MvPolynomial.funext
  intro v
  rw [Q₁₁₄_schur]
  simp only [orbital, schurValues_a₁, schurValues_a₂, schurValues_a₃,
    schurValues_a₄, schurValues_a₅]
  simp only [Matrix.cons_val]
  simp [c₁, c₂, c₃, c₄, c₅, ρ₄, ρ₃₁, ρ₂₂, ρ₂₁₁, ρ₁₁₁₁]
  ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem Q₁₁₄_orbital_eval (v : Fin 4 → R) :
    aeval v Q₁₁₄ =
      aeval v (C c₁ * orbital a₁ + C c₂ * orbital a₂ +
        C c₃ * orbital a₃ + C c₄ * orbital a₄ + C c₅ * orbital a₅) :=
  congrArg (aeval v) Q₁₁₄_orbital

end
end QuaternionicSymmetry.QuarticOrbitalEleven
