import QuaternionicSymmetry.GaussianQuadraticPolynomial
import QuaternionicSymmetry.HermitianGaussianPolynomialMoments

/-! Universal trace-polynomial formulas for complex Gaussian quadratic moments. -/

namespace QuaternionicSymmetry.UniversalGaussianMatrixMoments

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [CommRing S] [Algebra ℂ S]

private theorem eval_trace_one (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ))) =
      Matrix.trace Y := by
  simpa only [pow_one] using
    GaussianQuadraticPolynomial.eval_universal_trace_pow Y 1

private theorem eval_trace_two (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 2)) =
      Matrix.trace (Y ^ 2) :=
  GaussianQuadraticPolynomial.eval_universal_trace_pow Y 2

private theorem eval_trace_three (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 3)) =
      Matrix.trace (Y ^ 3) :=
  GaussianQuadraticPolynomial.eval_universal_trace_pow Y 3

private theorem eval_trace_four (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 4)) =
      Matrix.trace (Y ^ 4) :=
  GaussianQuadraticPolynomial.eval_universal_trace_pow Y 4

/-- The second complex Gaussian quadratic moment is a universal trace polynomial. -/
theorem moment_two (Y : Matrix κ κ S) :
    GaussianQuadraticPolynomial.moment Y 2 =
      Matrix.trace Y ^ 2 + Matrix.trace (Y ^ 2) := by
  let p : MvPolynomial (κ × κ) ℂ :=
    Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) ^ 2 +
      Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 2)
  have h := GaussianQuadraticPolynomial.extend_moment_identity 2 p
    (fun A hA => by
      simpa only [p, map_add, map_mul, map_pow, map_ofNat,
        eval_trace_one, eval_trace_two, eval_trace_three, eval_trace_four] using
        HermitianGaussianPolynomialMoments.moment_two_complex A hA) Y
  rw [h]
  simp only [p, map_add, map_pow, eval_trace_one, eval_trace_two]

/-- The third complex Gaussian quadratic moment is a universal trace polynomial. -/
theorem moment_three (Y : Matrix κ κ S) :
    GaussianQuadraticPolynomial.moment Y 3 =
      Matrix.trace Y ^ 3 + 3 * Matrix.trace Y * Matrix.trace (Y ^ 2) +
        2 * Matrix.trace (Y ^ 3) := by
  let p : MvPolynomial (κ × κ) ℂ :=
    Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) ^ 3 +
      3 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) *
        Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 2) +
      2 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 3)
  have h := GaussianQuadraticPolynomial.extend_moment_identity 3 p
    (fun A hA => by
      simpa only [p, map_add, map_mul, map_pow, map_ofNat,
        eval_trace_one, eval_trace_two, eval_trace_three, eval_trace_four] using
        HermitianGaussianPolynomialMoments.moment_three_complex A hA) Y
  rw [h]
  simp only [p, map_add, map_mul, map_pow, map_ofNat,
    eval_trace_one, eval_trace_two, eval_trace_three]

/-- The fourth complex Gaussian quadratic moment is a universal trace polynomial. -/
theorem moment_four (Y : Matrix κ κ S) :
    GaussianQuadraticPolynomial.moment Y 4 =
      Matrix.trace Y ^ 4 + 6 * Matrix.trace Y ^ 2 * Matrix.trace (Y ^ 2) +
        3 * Matrix.trace (Y ^ 2) ^ 2 + 8 * Matrix.trace Y * Matrix.trace (Y ^ 3) +
          6 * Matrix.trace (Y ^ 4) := by
  let p : MvPolynomial (κ × κ) ℂ :=
    Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) ^ 4 +
      6 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) ^ 2 *
        Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 2) +
      3 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 2) ^ 2 +
      8 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) *
        Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 3) +
      6 * Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ) ^ 4)
  have h := GaussianQuadraticPolynomial.extend_moment_identity 4 p
    (fun A hA => by
      simpa only [p, map_add, map_mul, map_pow, map_ofNat,
        eval_trace_one, eval_trace_two, eval_trace_three, eval_trace_four] using
        HermitianGaussianPolynomialMoments.moment_four_complex A hA) Y
  rw [h]
  simp only [p, map_add, map_mul, map_pow, map_ofNat,
    eval_trace_one, eval_trace_two, eval_trace_three, eval_trace_four]

end
end QuaternionicSymmetry.UniversalGaussianMatrixMoments
