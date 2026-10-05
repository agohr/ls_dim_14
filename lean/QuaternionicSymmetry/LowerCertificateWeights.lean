import QuaternionicSymmetry.CertificateHomogeneity
import QuaternionicSymmetry.PrintedTwoSixLinearAssembly
import QuaternionicSymmetry.ManifoldSevenVariableClosedEvaluation

namespace QuaternionicSymmetry.LowerCertificateWeights

open MvPolynomial
noncomputable section

/-- Weighted homogeneity survives substituting homogeneous polynomials of the
same weights for the variables. -/
theorem aeval_weighted {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    (w : σ → ℕ) (w' : τ → ℕ) (v : σ → MvPolynomial τ ℚ)
    (hv : ∀ i, IsWeightedHomogeneous w' (v i) (w i))
    {p : MvPolynomial σ ℚ} {n : ℕ}
    (hp : IsWeightedHomogeneous w p n) :
    IsWeightedHomogeneous w' (aeval v p) n := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa using (isWeightedHomogeneous_zero ℚ w' n)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
      rw [aeval_monomial]
      have hprod : IsWeightedHomogeneous w'
          (∏ i ∈ d.support, (v i) ^ d i)
          (∑ i ∈ d.support, d i * w i) := by
        apply IsWeightedHomogeneous.prod
        intro i hi
        simpa [nsmul_eq_mul] using (hv i).pow (d i)
      have hw : (∑ i ∈ d.support, d i * w i) = n := by
        simpa [Finsupp.weight, Finsupp.sum] using hr
      simpa [Finsupp.prod, hw] using hprod.C_mul r

private def grade6 : Fin 6 → ℕ := ![1, 1, 2, 3, 4, 5]

private theorem old_variables (i : Fin 5) :
    IsWeightedHomogeneous grade6
      (![DimensionElevenTwelveDensity.u, 2 * DimensionElevenTwelveDensity.p1,
        2 * DimensionElevenTwelveDensity.p2, 2 * DimensionElevenTwelveDensity.p3,
        2 * DimensionElevenTwelveDensity.p4] i)
      (CertificateHomogeneity.weights i) := by
  fin_cases i <;> simp only [CertificateHomogeneity.weights, grade6]
  all_goals
    first
    | simpa [DimensionElevenTwelveDensity.u] using
        (isWeightedHomogeneous_X (R := ℚ) grade6 (0 : Fin 6))
    | simpa [DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
        using (isWeightedHomogeneous_X (R := ℚ) grade6 (1 : Fin 6)).C_mul 2
    | simpa [DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
        using (isWeightedHomogeneous_X (R := ℚ) grade6 (2 : Fin 6)).C_mul 2
    | simpa [DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
        using (isWeightedHomogeneous_X (R := ℚ) grade6 (3 : Fin 6)).C_mul 2
    | simpa [DimensionElevenTwelveDensity.p1, DimensionElevenTwelveDensity.p2,
        DimensionElevenTwelveDensity.p3, DimensionElevenTwelveDensity.p4]
        using (isWeightedHomogeneous_X (R := ℚ) grade6 (4 : Fin 6)).C_mul 2

theorem old_weighted {p : AlgebraCertificates.P} {n : ℕ}
    (hp : IsWeightedHomogeneous CertificateHomogeneity.weights p n) :
    IsWeightedHomogeneous grade6 (DimensionElevenTwelveDensity.old p) n := by
  exact aeval_weighted CertificateHomogeneity.weights grade6 _ old_variables hp

private theorem lift_variables (i : Fin 6) :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (![DimensionThirteenFourteenDensity.u, DimensionThirteenFourteenDensity.p1,
        DimensionThirteenFourteenDensity.p2, DimensionThirteenFourteenDensity.p3,
        DimensionThirteenFourteenDensity.p4, DimensionThirteenFourteenDensity.p5] i)
      (grade6 i) := by
  fin_cases i <;> simp only [grade6]
  all_goals
    first
    | simpa [DimensionThirteenFourteenDensity.u,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (0 : Fin 7))
    | simpa [DimensionThirteenFourteenDensity.p1,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (1 : Fin 7))
    | simpa [DimensionThirteenFourteenDensity.p2,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (2 : Fin 7))
    | simpa [DimensionThirteenFourteenDensity.p3,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (3 : Fin 7))
    | simpa [DimensionThirteenFourteenDensity.p4,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (4 : Fin 7))
    | simpa [DimensionThirteenFourteenDensity.p5,
        ManifoldSevenVariableClosedEvaluation.slotGrade] using
        (isWeightedHomogeneous_X (R := ℚ)
          ManifoldSevenVariableClosedEvaluation.slotGrade (5 : Fin 7))

theorem lift_weighted {p : DimensionElevenTwelveDensity.P} {n : ℕ}
    (hp : IsWeightedHomogeneous grade6 p n) :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift p) n := by
  exact aeval_weighted grade6 _ _ lift_variables hp

theorem lift_old_weighted {p : AlgebraCertificates.P} {n : ℕ}
    (hp : IsWeightedHomogeneous CertificateHomogeneity.weights p n) :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift (DimensionElevenTwelveDensity.old p)) n :=
  lift_weighted (old_weighted hp)

theorem density2_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedTwoSixLinearAssembly.density2) 2 := by
  exact lift_old_weighted CertificateHomogeneity.K₂_wh

theorem density3_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedTwoSixLinearAssembly.density3) 3 := by
  exact lift_old_weighted CertificateHomogeneity.K₃_wh

theorem density4_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedTwoSixLinearAssembly.density4) 4 := by
  exact lift_old_weighted CertificateHomogeneity.K₄_wh

theorem density5_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift ReconstructionExamples.k5) 5 := by
  exact lift_old_weighted CertificateHomogeneity.K₅_wh

theorem density6_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift ReconstructionExamples.k6) 6 := by
  exact lift_old_weighted CertificateHomogeneity.K₆_wh

theorem rhs7_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedCertificatesSevenTen.rhs7) 7 := by
  rw [← PrintedCertificatesSevenTen.certificate7]
  exact lift_old_weighted CertificateHomogeneity.K₇_wh

theorem rhs8_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedCertificatesSevenTen.rhs8) 8 := by
  rw [← PrintedCertificatesSevenTen.certificate8]
  exact lift_old_weighted CertificateHomogeneity.K₈_wh

theorem rhs9_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedCertificatesSevenTen.rhs9) 9 := by
  rw [← PrintedCertificatesSevenTen.certificate9]
  exact lift_old_weighted CertificateHomogeneity.K₉_wh

theorem rhs10_weighted :
    IsWeightedHomogeneous ManifoldSevenVariableClosedEvaluation.slotGrade
      (DimensionThirteenFourteenDensity.lift PrintedCertificatesSevenTen.rhs10) 10 := by
  rw [← PrintedCertificatesSevenTen.certificate10]
  exact lift_old_weighted CertificateHomogeneity.K₁₀_wh

end
end LowerCertificateWeights
