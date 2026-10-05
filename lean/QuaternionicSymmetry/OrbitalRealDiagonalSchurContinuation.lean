import QuaternionicSymmetry.OrbitalRealSchurPolynomial
import QuaternionicSymmetry.OrbitalHaarFiniteSchurBridge
import QuaternionicSymmetry.OrbitalDiagonalMomentPolynomial
import QuaternionicSymmetry.OrbitalDiagonalLeftMomentPolynomial

/-! Polynomial continuation of the diagonal Haar-Schur identity through
repeated and zero right spectra. -/

namespace QuaternionicSymmetry.OrbitalRealDiagonalSchurContinuation

open MvPolynomial CompactSymplecticHaar OrbitalDiagonalSpectra
open OrbitalDiagonalMomentPolynomial OrbitalRealSchurPolynomial
open OrbitalHaarFiniteSchurBridge OrbitalOddDeterminantBase
open ForresterDiagonalInput
open OrbitalDiagonalLeftMomentPolynomial OrbitalRegularPolynomialContinuation

noncomputable section

theorem fixedLeft_momentPolynomial_eq_schur
    (hsource : ForresterDiagonalFormula) (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x : Fin (m+6) → ℚ)
    (hx : ∀ i, 0 < x i) (hΔx : oddVandermonde x ≠ 0) :
    momentPolynomial
      (hermitianDiagonal (fun i => (x i : ℝ))) k =
      MvPolynomial.C (((2*k).factorial : ℝ)) *
        finiteSchurPolynomial (m+6) k (fun i => (x i : ℝ)) := by
  apply momentPolynomial_eq_of_regular
  intro y hy hΔy
  have hΔ : oddVandermonde x * oddVandermonde y ≠ 0 :=
    mul_ne_zero hΔx hΔy
  have h := diagonal_evenMoment_finiteSchur hsource m k hm hk x y hx hy hΔ
  rw [← finiteSchurSum_rat (m+6) k x y] at h
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hfact : (((2*k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hfact).mp at h
  simpa only [mul_comm] using h

theorem diagonal_evenMoment_finiteSchur_fixedLeft
    (hsource : ForresterDiagonalFormula) (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x : Fin (m+6) → ℚ)
    (hx : ∀ i, 0 < x i) (hΔx : oddVandermonde x ≠ 0)
    (y : Fin (m+6) → ℝ) :
    evenMoment (standardJ (m+6))
      (hermitianDiagonal (fun i => (x i : ℝ)))
      (hermitianDiagonal y) k /
        ((2*k).factorial : ℝ) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          realSchurValue (fun i => (x i : ℝ)) lam *
            realSchurValue y lam := by
  have h := congrArg (fun p : MvPolynomial (Fin (m+6)) ℝ => p.eval y)
    (fixedLeft_momentPolynomial_eq_schur hsource m k hm hk x hx hΔx)
  dsimp only at h
  rw [eval_momentPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_finiteSchurPolynomial] at h
  have hfact : (((2*k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  exact (div_eq_iff hfact).mpr (by simpa only [mul_comm] using h)

/-- The finite Schur identity for the actual normalized Haar integral holds
at every real diagonal pair, including zero and repeated eigenvalues. -/
theorem diagonal_evenMoment_finiteSchur_allReal
    (hsource : ForresterDiagonalFormula) (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x y : Fin (m+6) → ℝ) :
    evenMoment (standardJ (m+6))
      (hermitianDiagonal x) (hermitianDiagonal y) k /
        ((2*k).factorial : ℝ) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          realSchurValue x lam * realSchurValue y lam := by
  have hpoly : leftMomentPolynomial (hermitianDiagonal y) k =
      MvPolynomial.C (((2*k).factorial : ℝ)) *
        finiteSchurPolynomial (m+6) k y := by
    apply polynomial_eq_of_positive_nondegenerate
    intro xr hxr hΔxr
    rw [eval_leftMomentPolynomial, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, eval_finiteSchurPolynomial]
    have h := diagonal_evenMoment_finiteSchur_fixedLeft
      hsource m k hm hk xr hxr hΔxr y
    have hsum :
        (∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
          (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
            realSchurValue (fun i => (xr i : ℝ)) lam *
              realSchurValue y lam) =
        ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
          (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
            realSchurValue y lam *
              realSchurValue (fun i => (xr i : ℝ)) lam := by
      apply Finset.sum_congr rfl
      intro lam _
      ring
    rw [hsum] at h
    have hfact : (((2*k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
    apply (div_eq_iff hfact).mp at h
    simpa only [mul_comm] using h
  have heval := congrArg
    (fun p : MvPolynomial (Fin (m+6)) ℝ => p.eval x) hpoly
  dsimp only at heval
  rw [eval_leftMomentPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_finiteSchurPolynomial] at heval
  have hsum :
      (∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          realSchurValue y lam * realSchurValue x lam) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          realSchurValue x lam * realSchurValue y lam := by
    apply Finset.sum_congr rfl
    intro lam _
    ring
  rw [hsum] at heval
  have hfact : (((2*k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  exact (div_eq_iff hfact).mpr (by simpa only [mul_comm] using heval)

end
end QuaternionicSymmetry.OrbitalRealDiagonalSchurContinuation
