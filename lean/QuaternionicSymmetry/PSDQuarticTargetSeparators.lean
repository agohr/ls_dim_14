import QuaternionicSymmetry.QuarticOrbitalDensityBridge
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The dimension-eleven and -twelve PSD separator target values

This module checks the negative values of the printed linear functionals on
the quartic terms of the independently reconstructed index densities.  It does
not assert nonnegativity on the PSD generator cone: that requires the universal
quaternionic/zonal moment polynomial and its normalization, neither of which
is currently an interface in this development.
-/

namespace QuaternionicSymmetry.PSDQuarticTargetSeparators

open MvPolynomial

noncomputable section

abbrev P := QuarticOrbitalEleven.P

/-- The ordered coefficient-vector realization in independent power sums. -/
def quartic (c : Fin 5 → ℚ) : P :=
  C (c 0) * X 0 ^ 4 + C (c 1) * X 0 ^ 2 * X 1 + C (c 2) * X 1 ^ 2 +
    C (c 3) * X 0 * X 2 + C (c 4) * X 3

def pair (v c : Fin 5 → ℚ) : ℚ :=
  v 0 * c 0 + v 1 * c 1 + v 2 * c 2 + v 3 * c 3 + v 4 * c 4

/-- Chapter 8's functionals on the ordered power-sum monomials
`p₁⁴, p₁²p₂, p₂², p₁p₃, p₄`. -/
def P11 : Fin 5 → ℚ := ![2695, -4585, 25339, -1295, 4361]
def P12 : Fin 5 → ℚ := ![15138, -26651, 150977, -6873, 23971]

/-- Coefficients of the quartic term of the reconstructed density in dimension 11. -/
def target11 : Fin 5 → ℚ :=
  ![4 * 8470 / 1403325, 4 * 9207 / 1403325,
    4 * 825 / 1403325, 4 * 2882 / 1403325, 4 * 450 / 1403325]

/-- Coefficients of the quartic term of the reconstructed density in dimension 12. -/
def target12 : Fin 5 → ℚ :=
  ![146 / 3645, 604 / 14175, 158 / 42525, 1616 / 127575, 268 / 155925]

/-- The coefficient vector reproduces the independently checked quartic
polynomial, rather than merely its reported separator value. -/
theorem target11_quartic :
    quartic target11 = QuarticOrbitalEleven.Q₁₁₄ := by
  apply MvPolynomial.funext
  intro v
  simp [quartic, target11, QuarticOrbitalEleven.Q₁₁₄,
    QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
    QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄]
  ring

theorem target12_quartic :
    quartic target12 = QuarticOrbitalTwelve.Q₁₂₄ := by
  apply MvPolynomial.funext
  intro v
  simp [quartic, target12, QuarticOrbitalTwelve.Q₁₂₄,
    QuarticOrbitalEleven.p₁, QuarticOrbitalEleven.p₂,
    QuarticOrbitalEleven.p₃, QuarticOrbitalEleven.p₄]

/-- The same quartic polynomials are the terms of the dimension-11/12
density recurrence, with full `u` powers recorded in that recurrence. -/
theorem target11_density :
    QuarticOrbitalDensityBridge.includeQuartic (quartic target11) =
      DimensionElevenTwelveDensity.q11 := by
  rw [target11_quartic]
  exact QuarticOrbitalDensityBridge.include_Q₁₁₄

theorem target12_density :
    QuarticOrbitalDensityBridge.includeQuartic (quartic target12) =
      DimensionElevenTwelveDensity.q12 := by
  rw [target12_quartic]
  exact QuarticOrbitalDensityBridge.include_Q₁₂₄

/-- The two printed negative target values are exact rational identities. -/
theorem P11_target11 : pair P11 target11 = -67336 / 93555 := by
  change (2695 : ℚ) * (4 * 8470 / 1403325) + (-4585) * (4 * 9207 / 1403325) +
    25339 * (4 * 825 / 1403325) + (-1295) * (4 * 2882 / 1403325) +
    4361 * (4 * 450 / 1403325) = _
  norm_num

theorem P12_target12 : pair P12 target12 = -245414 / 17325 := by
  change (15138 : ℚ) * (146 / 3645) + (-26651) * (604 / 14175) +
    150977 * (158 / 42525) + (-6873) * (1616 / 127575) +
    23971 * (268 / 155925) = _
  norm_num

theorem P11_target11_neg : pair P11 target11 < 0 := by
  rw [P11_target11]
  norm_num

theorem P12_target12_neg : pair P12 target12 < 0 := by
  rw [P12_target12]
  norm_num

end
end QuaternionicSymmetry.PSDQuarticTargetSeparators
