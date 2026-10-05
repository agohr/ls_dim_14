import QuaternionicSymmetry.QuarticOrbitalEleven

/-!
# The finite cubic Gaussian orbital decomposition

This proves the `F3orb` identity in Chapter 8 for every integer dimension
`5 ≤ n ≤ 14`.  The orbitals are the finite type-C Schur polynomials with the
factorial normalization of Chapter 7, using the existing `factorialRho`.
The result is a polynomial identity; an analytic Haar interpretation or the
pointwise orbital sign is not asserted here.
-/

namespace QuaternionicSymmetry.CubicGaussianOrbital

open MvPolynomial
noncomputable section

abbrev P := MvPolynomial (Fin 3) ℚ

def p1 : P := X 0
def p2 : P := X 1
def p3 : P := X 2

def h2 : P := C (1 / 2) * (p1 ^ 2 + p2)
def h3 : P := C (1 / 6) * (p1 ^ 3 + C 3 * p1 * p2 + C 2 * p3)

/-- The three Schur polynomials at weight three, from Jacobi--Trudi. -/
def s3 : P := h3
def s21 : P := h2 * p1 - h3
def s111 : P := p1 ^ 3 - 2 * p1 * h2 + h3

def powerSum (a : List ℕ) (j : ℕ) : ℚ :=
  (a.map fun x => (x : ℚ) ^ j).sum

def evalSpectrum (a : List ℕ) : P →ₐ[ℚ] ℚ :=
  aeval (fun i => powerSum a (i.val + 1))

def e1 : List ℕ := [1]
def e2 : List ℕ := [1, 1]
def e4 : List ℕ := [1, 1, 1, 1]

theorem schurValues_e1 :
    evalSpectrum e1 s3 = 1 ∧ evalSpectrum e1 s21 = 0 ∧
      evalSpectrum e1 s111 = 0 := by
  norm_num [evalSpectrum, e1, powerSum, s3, s21, s111,
    h2, h3, p1, p2, p3]

theorem schurValues_e2 :
    evalSpectrum e2 s3 = 4 ∧ evalSpectrum e2 s21 = 2 ∧
      evalSpectrum e2 s111 = 0 := by
  norm_num [evalSpectrum, e2, powerSum, s3, s21, s111,
    h2, h3, p1, p2, p3]

theorem schurValues_e4 :
    evalSpectrum e4 s3 = 20 ∧ evalSpectrum e4 s21 = 20 ∧
      evalSpectrum e4 s111 = 4 := by
  norm_num [evalSpectrum, e4, powerSum, s3, s21, s111,
    h2, h3, p1, p2, p3]

/-- The weight-three case of the finite type-C orbital formula.  A spectrum
shorter than `n` is padded with zeros. -/
def orbital3 (n : ℕ) (a : List ℕ) : P :=
  C (64 * QuarticOrbitalEleven.factorialRho n [3] * evalSpectrum a s3) * s3 +
  C (64 * QuarticOrbitalEleven.factorialRho n [2, 1] * evalSpectrum a s21) * s21 +
  C (64 * QuarticOrbitalEleven.factorialRho n [1, 1, 1] *
    evalSpectrum a s111) * s111

private theorem orbital_e1 (n : ℕ) :
    orbital3 n e1 = C (64 * QuarticOrbitalEleven.factorialRho n [3]) * s3 := by
  obtain ⟨h1, h2, h3⟩ := schurValues_e1
  simp only [orbital3, h1, h2, h3, mul_one, mul_zero,
    map_zero, zero_mul, add_zero]

private theorem orbital_e2 (n : ℕ) :
    orbital3 n e2 =
      C (256 * QuarticOrbitalEleven.factorialRho n [3]) * s3 +
      C (128 * QuarticOrbitalEleven.factorialRho n [2, 1]) * s21 := by
  obtain ⟨h1, h2, h3⟩ := schurValues_e2
  simp only [orbital3, h1, h2, h3, mul_zero,
    map_zero, zero_mul, add_zero]
  congr 1 <;> congr 1 <;> ring

private theorem orbital_e4 (n : ℕ) :
    orbital3 n e4 =
      C (1280 * QuarticOrbitalEleven.factorialRho n [3]) * s3 +
      C (1280 * QuarticOrbitalEleven.factorialRho n [2, 1]) * s21 +
      C (256 * QuarticOrbitalEleven.factorialRho n [1, 1, 1]) * s111 := by
  obtain ⟨h1, h2, h3⟩ := schurValues_e4
  simp only [orbital3, h1, h2, h3]
  congr 1 <;> congr 1 <;> ring

/-- The Gaussian coefficient `F₃` in the convention `pⱼ=zⱼ/2`. -/
def gaussian3 : P :=
  C (1 / 10368) * p1 ^ 3 + C (1 / 17280) * p1 * p2 + C (1 / 90720) * p3

def D1 (n : ℚ) : ℚ :=
  n * (2 * n + 1) * (4 * n ^ 4 - 36 * n ^ 3 + 463 * n ^ 2 + 161 * n + 108) /
    161280

def D2 (n : ℚ) : ℚ :=
  n * (n - 1) * (2 * n - 1) * (2 * n + 1) * (-8 * n ^ 2 + 160 * n - 57) /
    967680

def D4 (n : ℚ) : ℚ :=
  n * (n - 1) * (n - 2) * (2 * n - 3) * (2 * n - 1) * (2 * n + 1) /
    645120

/-- Exact Chapter 8 finite decomposition. -/
theorem gaussian3_orbital (n : ℕ) (hn5 : 5 ≤ n) (hn14 : n ≤ 14) :
    gaussian3 =
      C (D1 n) * orbital3 n e1 +
      C (D2 n) * orbital3 n e2 +
      C (D4 n) * orbital3 n e4 := by
  rw [orbital_e1, orbital_e2, orbital_e4]
  apply MvPolynomial.funext
  intro v
  simp [gaussian3, s3, s21, s111, h2, h3, p1, p2, p3]
  interval_cases n <;>
    norm_num [QuarticOrbitalEleven.factorialRho, D1, D2, D4,
      Nat.factorial] <;>
    ring

/-- All three orbital coefficients are strictly positive on the claimed
integer range. -/
theorem coefficients_positive (n : ℕ) (hn5 : 5 ≤ n) (hn14 : n ≤ 14) :
    0 < D1 n ∧ 0 < D2 n ∧ 0 < D4 n := by
  interval_cases n <;> norm_num [D1, D2, D4]

theorem spectra_admissible (n : ℕ) (hn5 : 5 ≤ n) :
    e1.length ≤ n ∧ e2.length ≤ n ∧ e4.length ≤ n := by
  norm_num [e1, e2, e4]
  omega

end
end QuaternionicSymmetry.CubicGaussianOrbital
