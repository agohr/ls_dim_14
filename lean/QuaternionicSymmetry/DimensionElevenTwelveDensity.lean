import QuaternionicSymmetry.AlgebraReconstruction
import QuaternionicSymmetry.WeightFiveAhat
import QuaternionicSymmetry.FifthGaussianPolynomial
import QuaternionicSymmetry.HigherCharacters
import Mathlib.Algebra.MvPolynomial.Funext

/-! The universal dimensions 11 and 12 density calculations of Chapter 6.

All equalities below are in a rational polynomial ring with independent
variables `u,p₁,…,p₅`.  In particular the powers of `u` have been restored,
and specialization is valid in a commutative rational algebra with nilpotents.
These polynomials do not themselves identify differential forms, classes, or
characteristic numbers. -/

namespace QuaternionicSymmetry.DimensionElevenTwelveDensity

open MvPolynomial
open AlgebraCertificates

noncomputable section

abbrev P := MvPolynomial (Fin 6) ℚ

def u : P := X 0
def p1 : P := X 1
def p2 : P := X 2
def p3 : P := X 3
def p4 : P := X 4
def p5 : P := X 5

/-- Evaluate the existing five-variable `u,z₁,…,z₄` interface using
`z_j=2p_j`, leaving `u,p₁,…,p₅` algebraically independent. -/
def old (q : AlgebraCertificates.P) : P :=
  AlgebraCertificates.evaluate u (2 * p1) (2 * p2) (2 * p3) (2 * p4) q

def b1 (n : ℚ) : P := old (AlgebraCertificates.b₁ n)
def b2 (n : ℚ) : P := old (AlgebraCertificates.b₂ n)
def b3 (n : ℚ) : P := old (AlgebraCertificates.b₃ n)
def b4 (n : ℚ) : P := old (AlgebraCertificates.b₄ n)

/-- Chapter 6's weight-five root term, in the existing convention `z_j=2p_j`. -/
def b5 (n : ℚ) : P :=
  C (-(n - 511) / 239500800) * u ^ 5 + C (1 / 5322240) * u ^ 4 * p1
    - C (1 / 1140480) * u ^ 3 * p2 + C (1 / 1140480) * u ^ 2 * p3
    - C (1 / 5322240) * u * p4 + C (1 / 239500800) * p5

def a0 : P := 1
def a1 (n : ℚ) : P := old (AlgebraCertificates.A₁ n)
def a2 (n : ℚ) : P := old (AlgebraCertificates.A₂ n)
def a3 (n : ℚ) : P := old (AlgebraCertificates.A₃ n)
def a4 (n : ℚ) : P := old (AlgebraCertificates.A₄ n)

/-- The fifth exponential coefficient extends the existing `A₀,…,A₄`.
The formula is the expanded recurrence proved in `LogAhat.A5_recurrence`. -/
def a5 (n : ℚ) : P :=
  b5 n + b1 n * b4 n + b2 n * b3 n + C (1 / 2) * b1 n ^ 2 * b3 n
    + C (1 / 2) * b1 n * b2 n ^ 2 + C (1 / 6) * b1 n ^ 3 * b2 n
    + C (1 / 120) * b1 n ^ 5

/-- The Laurent-character convolution in dimension eleven, with its genuine
Taylor coefficients and every power of `u` retained. -/
def density11 : P :=
  C 8192 * u ^ 6 * a5 11 + C 20480 * u ^ 7 * a4 11
    + C (121856 / 5) * u ^ 8 * a3 11
    + C (3492352 / 189) * u ^ 9 * a2 11
    + C (6796864 / 675) * u ^ 10 * a1 11
    + C (46368 / 11) * u ^ 11 * a0

/-- The corresponding convolution in dimension twelve. -/
def density12 : P :=
  C 16384 * u ^ 7 * a5 12 + C (114688 / 3) * u ^ 8 * a4 12
    + C (1949696 / 45) * u ^ 9 * a3 12
    + C (4292608 / 135) * u ^ 10 * a2 12
    + C (34422784 / 2025) * u ^ 11 * a1 12
    + C (2097152 / 297) * u ^ 12 * a0

def q11 : P :=
  C (4 / 1403325) * (C 8470 * p1 ^ 4 + C 9207 * p1 ^ 2 * p2
    + C 825 * p2 ^ 2 + C 2882 * p1 * p3 + C 450 * p4)

def q12 : P :=
  C (146 / 3645) * p1 ^ 4 + C (604 / 14175) * p1 ^ 2 * p2
    + C (158 / 42525) * p2 ^ 2 + C (1616 / 127575) * p1 * p3
    + C (268 / 155925) * p4

/-- The printed fifth Gaussian polynomial, now embedded in the six-variable
ring so that it can be compared with the complete density. -/
def f5 : P :=
  C (1 / 11496038400) *
    (C 385 * p1 ^ 5 + C 770 * p1 ^ 3 * p2 + C 440 * p1 ^ 2 * p3
      + C 231 * p1 * p2 ^ 2 + C 198 * p1 * p4
      + C 88 * p2 * p3 + C 48 * p5)

/-- The complete reconstructed polynomial in Weyl power sums, with
`u` restored according to each monomial's weight. -/
def printed11 : P :=
  C 288 * u ^ 11 + C (4965304 / 51975) * p1 * u ^ 10
    + (C (35416 / 2835) * p1 ^ 2 + C (154736 / 93555) * p2) * u ^ 9
    + (C (33772 / 42525) * p1 ^ 3 + C (16052 / 42525) * p1 * p2
       + C (18848 / 467775) * p3) * u ^ 8
    + q11 * u ^ 7 + C 8192 * f5 * u ^ 6

def printed12 : P :=
  C 336 * u ^ 12 + C (6101552 / 51975) * p1 * u ^ 11
    + (C (33368 / 2025) * p1 ^ 2 + C (962072 / 467775) * p2) * u ^ 10
    + (C (49064 / 42525) * p1 ^ 3 + C (22408 / 42525) * p1 * p2
       + C (22384 / 467775) * p3) * u ^ 9
    + q12 * u ^ 8 + C 16384 * f5 * u ^ 7

private theorem old_eval (q : AlgebraCertificates.P) (v : Fin 6 → ℚ) :
    MvPolynomial.eval v (old q) =
      AlgebraCertificates.evaluate (v 0) (2 * v 1) (2 * v 2) (2 * v 3) (2 * v 4) q := by
  change aeval v (old q) = _
  unfold old AlgebraCertificates.evaluate
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun i : Fin 5 => (aeval v) (![u, 2 * p1, 2 * p2, 2 * p3, 2 * p4] i)) =
      ![v 0, 2 * v 1, 2 * v 2, 2 * v 3, 2 * v 4] := by
    funext i
    fin_cases i <;> simp [u, p1, p2, p3, p4]
  rw [h]

theorem density11_printed : density11 = printed11 := by
  apply MvPolynomial.funext
  intro v
  simp only [density11, printed11, q11, f5, a5, a4, a3, a2, a1, a0,
    b5, b4, b3, b2, b1, map_add, map_sub, map_mul, map_pow, old_eval]
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.A₄,
    AlgebraCertificates.A₃, AlgebraCertificates.A₂,
    AlgebraCertificates.A₁, AlgebraCertificates.b₄, AlgebraCertificates.b₃,
    AlgebraCertificates.b₂, AlgebraCertificates.b₁, AlgebraCertificates.c,
    AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    u, p1, p2, p3, p4, p5]
  ring

theorem density12_printed : density12 = printed12 := by
  apply MvPolynomial.funext
  intro v
  simp only [density12, printed12, q12, f5, a5, a4, a3, a2, a1, a0,
    b5, b4, b3, b2, b1, map_add, map_sub, map_mul, map_pow, old_eval]
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.A₄,
    AlgebraCertificates.A₃, AlgebraCertificates.A₂,
    AlgebraCertificates.A₁, AlgebraCertificates.b₄, AlgebraCertificates.b₃,
    AlgebraCertificates.b₂, AlgebraCertificates.b₁, AlgebraCertificates.c,
    AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    u, p1, p2, p3, p4, p5]
  ring

/-- The new logarithmic polynomial really is the fifth root coefficient
already computed from Bernoulli numbers in `WeightFiveAhat`. -/
theorem b5_evaluate (n : ℕ) (v : Fin 6 → ℚ) :
    MvPolynomial.eval v (b5 n) =
      LogAhat.B5 n (v 0) (2 * v 1) (2 * v 2) (2 * v 3) (2 * v 4) (2 * v 5) := by
  simp [b5, LogAhat.B5, u, p1, p2, p3, p4, p5]
  ring

/-- The extension through weight five obeys the same exponential recurrence
as the existing first four coefficients. -/
theorem a5_recurrence (n : ℚ) :
    5 * a5 n = b1 n * a4 n + 2 * b2 n * a3 n +
      3 * b3 n * a2 n + 4 * b4 n * a1 n + 5 * b5 n * a0 := by
  apply MvPolynomial.funext
  intro v
  simp only [a5, a4, a3, a2, a1, a0,
    b5, b4, b3, b2, b1, map_add, map_sub, map_mul, map_pow, old_eval]
  simp [AlgebraCertificates.evaluate, AlgebraCertificates.A₄,
    AlgebraCertificates.A₃, AlgebraCertificates.A₂,
    AlgebraCertificates.A₁, AlgebraCertificates.b₄, AlgebraCertificates.b₃,
    AlgebraCertificates.b₂, AlgebraCertificates.b₁, AlgebraCertificates.c,
    AlgebraCertificates.U, AlgebraCertificates.Z₁, AlgebraCertificates.Z₂,
    AlgebraCertificates.Z₃, AlgebraCertificates.Z₄,
    u, p1, p2, p3, p4, p5]
  ring

/-- The embedded top-weight term is exactly the separately checked `F₅`.
The embedding is polynomial, so this is valid before any substitution into
real curvature or an algebra with nilpotents. -/
theorem f5_from_existing :
    f5 = MvPolynomial.aeval ![p1, p2, p3, p4, p5]
      FifthGaussianPolynomial.F5 := by
  rw [FifthGaussianPolynomial.F5_printed]
  simp [f5, FifthGaussianPolynomial.p1, FifthGaussianPolynomial.p2,
    FifthGaussianPolynomial.p3, FifthGaussianPolynomial.p4,
    FifthGaussianPolynomial.p5]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem old_aeval (q : AlgebraCertificates.P) (v : Fin 6 → R) :
    MvPolynomial.aeval v (old q) =
      AlgebraCertificates.evaluate (v 0) (2 * v 1) (2 * v 2) (2 * v 3) (2 * v 4) q := by
  unfold old AlgebraCertificates.evaluate
  rw [MvPolynomial.comp_aeval_apply]
  have h : (fun i : Fin 5 => (aeval v) (![u, 2 * p1, 2 * p2, 2 * p3, 2 * p4] i)) =
      ![v 0, 2 * v 1, 2 * v 2, 2 * v 3, 2 * v 4] := by
    funext i
    fin_cases i <;> simp [u, p1, p2, p3, p4]
  rw [h]

/-- Exact density equality in any commutative rational algebra, including
algebras with nilpotents. -/
theorem density11_evaluate (v : Fin 6 → R) :
    MvPolynomial.aeval v density11 = MvPolynomial.aeval v printed11 := by
  rw [density11_printed]

theorem density12_evaluate (v : Fin 6 → R) :
    MvPolynomial.aeval v density12 = MvPolynomial.aeval v printed12 := by
  rw [density12_printed]

/-- The existing convolution `fullDensity` agrees with the complete
dimension-eleven polynomial.  Its tail is the genuine fifth coefficient;
all positions above five vanish by the proven character coefficients. -/
theorem fullDensity_eleven (v : Fin 6 → R) :
    AlgebraReconstruction.fullDensity 11 (v 0) (2 * v 1) (2 * v 2)
        (2 * v 3) (2 * v 4) (fun _ => MvPolynomial.aeval v (a5 11)) =
      MvPolynomial.aeval v density11 := by
  have h := HigherCharacters.taylor_eleven
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩
  simp only [AlgebraReconstruction.fullDensity, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, AlgebraReconstruction.Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁]
  simp [density11, a0, a1, a2, a3, a4, old_aeval,
    AlgebraCertificates.A₀, u]
  ring

theorem fullDensity_twelve (v : Fin 6 → R) :
    AlgebraReconstruction.fullDensity 12 (v 0) (2 * v 1) (2 * v 2)
        (2 * v 3) (2 * v 4) (fun _ => MvPolynomial.aeval v (a5 12)) =
      MvPolynomial.aeval v density12 := by
  have h := HigherCharacters.taylor_twelve
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩
  simp only [AlgebraReconstruction.fullDensity, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, AlgebraReconstruction.Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂]
  simp [density12, a0, a1, a2, a3, a4, old_aeval,
    AlgebraCertificates.A₀, u]
  ring

/-- Characteristic weight eleven: `u` and `p_j` scale by weights `1` and
`j`, respectively.  This is an identity of polynomials, not a degree claim
made only after setting `u=1`. -/
theorem density11_homogeneous (t : P) :
    MvPolynomial.aeval ![t * u, t * p1, t ^ 2 * p2, t ^ 3 * p3,
      t ^ 4 * p4, t ^ 5 * p5] density11 = t ^ 11 * density11 := by
  rw [density11_printed]
  simp [printed11, q11, f5, u, p1, p2, p3, p4, p5]
  ring

theorem density12_homogeneous (t : P) :
    MvPolynomial.aeval ![t * u, t * p1, t ^ 2 * p2, t ^ 3 * p3,
      t ^ 4 * p4, t ^ 5 * p5] density12 = t ^ 12 * density12 := by
  rw [density12_printed]
  simp [printed12, q12, f5, u, p1, p2, p3, p4, p5]
  ring

end
end QuaternionicSymmetry.DimensionElevenTwelveDensity
