import QuaternionicSymmetry.ElevenTwelveProjectionCertificates

/-! The Chapter 6 cubic Schur--Weyl interpolation formula. This is an
identity of universal rational polynomials, including after substitution
into a commutative rational algebra with nilpotents. -/

namespace QuaternionicSymmetry.CubicProjectionInterpolation

open MvPolynomial
open ElevenTwelveProjectionCertificates
noncomputable section

/-- At rank `r>2`, every cubic rank-`ell` moment is determined by the
rank-one, rank-two, and full-rank moments. The coefficients may have either
sign; this is an algebraic change of coordinates, not a positivity claim. -/
theorem interpolate (r ell : ℚ) (hr : 2 < r) :
    m3 r ell =
      C (ell * (r - ell) * (2 - ell) / (r - 1)) * m3 r 1 +
      C (ell * (r - ell) * (ell - 1) / (2 * (r - 2))) * m3 r 2 +
      C (ell * (ell - 1) * (ell - 2) / (r * (r - 1) * (r - 2))) * m3 r r := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hr2 : r - 2 ≠ 0 := by linarith
  have hpr1 : r + 1 ≠ 0 := by linarith
  have hpr2 : r + 2 ≠ 0 := by linarith
  apply MvPolynomial.funext
  intro v
  simp [m3, schur3, schur21, schur111, z1, z2, z3,
    DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
    DimensionElevenTwelveDensity.p3]
  field_simp
  ring

theorem interpolate_evaluate {R : Type*} [CommRing R] [Algebra ℚ R]
    (r ell : ℚ) (hr : 2 < r) (v : Fin 6 → R) :
    aeval v (m3 r ell) =
      aeval v
        (C (ell * (r - ell) * (2 - ell) / (r - 1)) * m3 r 1 +
         C (ell * (r - ell) * (ell - 1) / (2 * (r - 2))) * m3 r 2 +
         C (ell * (ell - 1) * (ell - 2) / (r * (r - 1) * (r - 2))) * m3 r r) :=
  congrArg (aeval v) (interpolate r ell hr)

end
end QuaternionicSymmetry.CubicProjectionInterpolation
