import QuaternionicSymmetry.HermitianProjectionMoments
import QuaternionicSymmetry.GaussianQuadraticPolynomial

/-! Rank-two cubic projection moments as universal matrix identities over
any commutative complex algebra, including exterior-algebra coefficients. -/

namespace QuaternionicSymmetry.UniversalProjectionMatrixMoments

open Matrix MvPolynomial UnitaryProjectionMoments

noncomputable section

variable {κ S T : Type*} [Fintype κ] [DecidableEq κ]
  [CommRing S] [Algebra ℂ S] [CommRing T] [Algebra ℂ T]

omit [DecidableEq κ] in
theorem map_tracePolynomial (s : Finset κ) (f : S →ₐ[ℂ] T) (Y : Matrix κ κ S) :
    MvPolynomial.map f.toRingHom (tracePolynomial s Y) = tracePolynomial s (Y.map f) := by
  have h : f.toRingHom.comp (algebraMap ℂ S) = algebraMap ℂ T := by
    ext z
    exact f.commutes z
  simp only [tracePolynomial, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, h]
  rfl

theorem map_moment (s : Finset κ) (f : S →ₐ[ℂ] T) (Y : Matrix κ κ S) (k : ℕ) :
    f (moment s Y k) = moment s (Y.map f) k := by
  unfold moment
  change (f.restrictScalars ℝ)
    (UnitaryPolynomialExpectation.expectation (tracePolynomial s Y ^ k)) = _
  rw [UnitaryPolynomialExpectation.expectation_map]
  simp only [map_pow]
  rw [show (f.restrictScalars ℝ).toRingHom = f.toRingHom from rfl, map_tracePolynomial]

theorem eval_universal_moment (s : Finset κ) (Y : Matrix κ κ S) (k : ℕ) :
    aeval (fun p => Y p.1 p.2) (moment s GaussianQuadraticPolynomial.universalMatrix k) =
      moment s Y k := by
  rw [map_moment, GaussianQuadraticPolynomial.eval_universalMatrix]

theorem extend_moment_identity (s : Finset κ) (k : ℕ) (p : MvPolynomial (κ × κ) ℂ)
    (h : ∀ Y : Matrix κ κ ℂ, Y.IsHermitian →
      moment s Y k = aeval (fun a => Y a.1 a.2) p)
    (Y : Matrix κ κ S) : moment s Y k = aeval (fun a => Y a.1 a.2) p := by
  have hp : moment s (GaussianQuadraticPolynomial.universalMatrix (κ := κ)) k = p := by
    apply HermitianPolynomialExt.ext
    intro A hA
    change aeval (fun a => A a.1 a.2)
      (moment s GaussianQuadraticPolynomial.universalMatrix k) =
      aeval (fun a => A a.1 a.2) p
    rw [eval_universal_moment]
    exact h A hA
  rw [← eval_universal_moment s Y k, hp]

private theorem eval_trace_one (Y : Matrix κ κ S) :
    aeval (fun a : κ × κ => Y a.1 a.2)
      (Matrix.trace (GaussianQuadraticPolynomial.universalMatrix (κ := κ))) =
      Matrix.trace Y := by
  simpa only [pow_one] using GaussianQuadraticPolynomial.eval_universal_trace_pow Y 1

theorem moment_three (s : Finset κ) (hs : s.card = 2) (hr : 3 ≤ Fintype.card κ)
    (Y : Matrix κ κ S) :
    moment s Y 3 =
      algebraMap ℂ S (4 / ((Fintype.card κ : ℂ) * (Fintype.card κ - 1) *
        (Fintype.card κ + 1) * (Fintype.card κ + 2))) *
      ((2 * (Fintype.card κ : S) + 1) * Matrix.trace Y ^ 3 +
        3 * (Fintype.card κ - 1) * Matrix.trace Y * Matrix.trace (Y ^ 2) +
        (Fintype.card κ - 4) * Matrix.trace (Y ^ 3)) := by
  let X : Matrix κ κ (MvPolynomial (κ × κ) ℂ) := GaussianQuadraticPolynomial.universalMatrix
  let d : ℂ := 4 / ((Fintype.card κ : ℂ) * (Fintype.card κ - 1) *
    (Fintype.card κ + 1) * (Fintype.card κ + 2))
  let p : MvPolynomial (κ × κ) ℂ := C d *
    ((2 * (Fintype.card κ : MvPolynomial (κ × κ) ℂ) + 1) * Matrix.trace (X ^ 1) ^ 3 +
      3 * ((Fintype.card κ : MvPolynomial (κ × κ) ℂ) - 1) * Matrix.trace (X ^ 1) * Matrix.trace (X ^ 2) +
      ((Fintype.card κ : MvPolynomial (κ × κ) ℂ) - 4) * Matrix.trace (X ^ 3))
  have he (Z : Matrix κ κ S) : aeval (fun a => Z a.1 a.2) p =
      algebraMap ℂ S d * ((2 * (Fintype.card κ : S) + 1) * Matrix.trace Z ^ 3 +
        3 * (Fintype.card κ - 1) * Matrix.trace Z * Matrix.trace (Z ^ 2) +
        (Fintype.card κ - 4) * Matrix.trace (Z ^ 3)) := by
    simp only [p, X, map_mul, aeval_C, map_add, map_sub, map_pow, map_ofNat,
      map_natCast, map_one, GaussianQuadraticPolynomial.eval_universal_trace_pow, pow_one,
      eval_trace_one]
  rw [extend_moment_identity s 3 p ?_ Y, he]
  intro A hA
  simpa only [p, X, map_mul, aeval_C, map_add, map_sub, map_pow, map_ofNat,
    map_natCast, map_one, GaussianQuadraticPolynomial.eval_universal_trace_pow, pow_one,
    eval_trace_one, Algebra.algebraMap_self_apply, d] using
    HermitianProjectionMoments.moment_three_complex s hs hr A hA

theorem moment_three_real (s : Finset κ) (hs : s.card = 2) (hr : 3 ≤ Fintype.card κ)
    (Y : Matrix κ κ S) :
    moment s Y 3 =
      (4 / ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) *
        (Fintype.card κ + 1) * (Fintype.card κ + 2))) •
      ((2 * (Fintype.card κ : ℝ) + 1) • Matrix.trace Y ^ 3 +
        (3 * ((Fintype.card κ : ℝ) - 1)) • (Matrix.trace Y * Matrix.trace (Y ^ 2)) +
        ((Fintype.card κ : ℝ) - 4) • Matrix.trace (Y ^ 3)) := by
  rw [moment_three s hs hr]
  simp only [Algebra.smul_def]
  have hd : algebraMap ℝ S (4 / ((Fintype.card κ : ℝ) * (Fintype.card κ - 1) *
      (Fintype.card κ + 1) * (Fintype.card κ + 2))) =
      algebraMap ℂ S (4 / ((Fintype.card κ : ℂ) * (Fintype.card κ - 1) *
        (Fintype.card κ + 1) * (Fintype.card κ + 2))) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ S]
    congr 1
    norm_cast
  rw [hd]
  simp only [map_add, map_sub, map_mul, map_ofNat, map_natCast, map_one]
  ring

end
end QuaternionicSymmetry.UniversalProjectionMatrixMoments
