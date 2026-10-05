import QuaternionicSymmetry.PrintedGaussianProjectionPositivity
import QuaternionicSymmetry.PrintedCertificatesSevenTen

/-! The printed quartic Gaussian term is the actual fourth weighted
Gaussian coefficient in the six-variable density convention. -/
namespace QuaternionicSymmetry.PrintedLowerGaussianPositivity
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedProjectionCubicPositivity PrintedGaussianProjectionPositivity
  QuaternionicAhatPositivity QuaternionicTraceConventionBridge
  ReconstructionExamples DimensionElevenTwelveDensity
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem f4_as_tracePolynomial :
    f4 = C (1/7962624) * (2*p1)^4 +
      C (1/3317760) * (2*p1)^2 * (2*p2) +
      C (1/16588800) * (2*p2)^2 +
      C (1/4354560) * (2*p1) * (2*p3) +
      C (1/9676800) * (2*p4) := by
  apply MvPolynomial.funext
  intro v
  simp [f4, p1, p2, p3, p4]
  ring


omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem f4_eval_rat (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (η : β → E V) :
    MvPolynomial.aeval (densityValues Q c B η) f4 =
      algebraMap ℚ (CE V) (1/7962624) * (2 * (densityValues Q c B η) 1)^4 +
      algebraMap ℚ (CE V) (1/3317760) * (2 * (densityValues Q c B η) 1)^2 *
        (2 * (densityValues Q c B η) 2) +
      algebraMap ℚ (CE V) (1/16588800) * (2 * (densityValues Q c B η) 2)^2 +
      algebraMap ℚ (CE V) (1/4354560) * (2 * (densityValues Q c B η) 1) *
        (2 * (densityValues Q c B η) 3) +
      algebraMap ℚ (CE V) (1/9676800) * (2 * (densityValues Q c B η) 4) := by
  rw [f4_as_tracePolynomial]
  simp only [map_add, map_mul, map_pow, aeval_C]
  simp [p1, p2, p3, p4]


omit [FiniteDimensional ℝ V] in
private theorem rat_to_real (q : ℚ) :
    algebraMap ℚ (CE V) q = algebraMap ℝ (CE V) (q : ℝ) := by
  exact (IsScalarTower.algebraMap_apply ℚ ℝ (CE V) q).symm


omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem f4_eval (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) :
    MvPolynomial.aeval (densityValues Q c B η) f4 =
      algebraMap ℝ (CE V) (1 / 7962624) * tracePower B η 1 ^ 4 +
        algebraMap ℝ (CE V) (1 / 3317760) * tracePower B η 1 ^ 2 * tracePower B η 2 +
        algebraMap ℝ (CE V) (1 / 16588800) * tracePower B η 2 ^ 2 +
        algebraMap ℝ (CE V) (1 / 4354560) * tracePower B η 1 * tracePower B η 3 +
        algebraMap ℝ (CE V) (1 / 9676800) * tracePower B η 4 := by
  have hv1 : 2 * (densityValues Q c B η) 1 = tracePower B η 1 := by
    simp [densityValues, tracePower_eq_twice_halfTrace B hB η]
  have hv2 : 2 * (densityValues Q c B η) 2 = tracePower B η 2 := by
    simp [densityValues, tracePower_eq_twice_halfTrace B hB η]
  have hv3 : 2 * (densityValues Q c B η) 3 = tracePower B η 3 := by
    simp [densityValues, tracePower_eq_twice_halfTrace B hB η]
  have hv4 : 2 * (densityValues Q c B η) 4 = tracePower B η 4 := by
    simp [densityValues, tracePower_eq_twice_halfTrace B hB η]
  rw [f4_eval_rat, rat_to_real, rat_to_real, rat_to_real, rat_to_real, rat_to_real]
  rw [show 2 * (densityValues Q c B η) 1 = tracePower B η 1 from hv1,
    show 2 * (densityValues Q c B η) 2 = tracePower B η 2 from hv2,
    show 2 * (densityValues Q c B η) 3 = tracePower B η 3 from hv3,
    show 2 * (densityValues Q c B η) 4 = tracePower B η 4 from hv4]
  norm_num


theorem f4_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (B : β → Matrix κ κ ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 4 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) f4 *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 4)) := by
  rw [f4_eval Q c B hB η]
  exact F₄_mixed_in_positive_ray Q c B hB η hη hk

end
end QuaternionicSymmetry.PrintedLowerGaussianPositivity
