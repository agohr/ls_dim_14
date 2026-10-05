import QuaternionicSymmetry.PrintedProjectionCubicPositivity
import QuaternionicSymmetry.QuaternionicAhatFifthPositivity
import QuaternionicSymmetry.QuaternionicLowMomentPositivity

/-! Remaining Gaussian and low projection generator signs in the printed
six-variable dimension-eleven/twelve density convention. -/
namespace QuaternionicSymmetry.PrintedGaussianProjectionPositivity

open Module QuaternionicFundamental QuaternionicTracePositivity MatrixTracePolynomial
  QuaternionicTraceConventionBridge PrintedProjectionCubicPositivity
  QuaternionicAhatPositivity QuaternionicAhatFifthPositivity

set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 800000

noncomputable section
private theorem f5_eval_values {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) :
    MvPolynomial.aeval v DimensionElevenTwelveDensity.f5 =
      algebraMap ℚ R (1 / 11496038400) *
        (385 * v 1 ^ 5 + 770 * v 1 ^ 3 * v 2 + 440 * v 1 ^ 2 * v 3 +
         231 * v 1 * v 2 ^ 2 + 198 * v 1 * v 4 + 88 * v 2 * v 3 + 48 * v 5) := by
  simp [DimensionElevenTwelveDensity.f5, DimensionElevenTwelveDensity.p1,
    DimensionElevenTwelveDensity.p2, DimensionElevenTwelveDensity.p3,
    DimensionElevenTwelveDensity.p4, DimensionElevenTwelveDensity.p5, map_ofNat]

private theorem m2One_eval_values {R : Type*} [CommRing R] [Algebra ℚ R]
    (r : ℚ) (v : Fin 6 → R) :
    MvPolynomial.aeval v (ElevenTwelveProjectionCertificates.m2One r) =
      algebraMap ℚ R (1 / (r * (r + 1))) * ((2 * v 1)^2 + 2 * v 2) := by
  simp [ElevenTwelveProjectionCertificates.m2One, ElevenTwelveProjectionCertificates.z1,
    ElevenTwelveProjectionCertificates.z2, DimensionElevenTwelveDensity.p1,
    DimensionElevenTwelveDensity.p2, map_ofNat]

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem f5_eval (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian) (η : β → E V) :
    MvPolynomial.aeval (densityValues Q c B η) DimensionElevenTwelveDensity.f5 =
      fifthTraceCoefficient B η := by
  unfold fifthTraceCoefficient
  simp only [tracePower_eq_twice_halfTrace B hB η]
  rw [AhatFifthCoefficientLimits.coefficient_two_p_printed]
  rw [f5_eval_values]
  congr 1
  norm_num [IsScalarTower.algebraMap_apply ℚ ℝ (CE V)]

theorem f5_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 5 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) DimensionElevenTwelveDensity.f5 *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 5)) := by
  rw [f5_eval Q c B hB η]
  exact F₅_mixed_in_positive_ray Q c B hB η hη hk

theorem m1_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 1 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) ElevenTwelveProjectionCertificates.m1Full *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 1)) := by
  have h := QuaternionicLowMomentPositivity.tracePower_one_pow_mixed_in_positive_ray
    Q c B hB η hη 1 hk
  rw [tracePower_eq_twice_halfTrace B hB η] at h
  simpa [ElevenTwelveProjectionCertificates.m1Full, ElevenTwelveProjectionCertificates.z1,
    DimensionElevenTwelveDensity.p1, densityValues] using h

theorem m2Full_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) ElevenTwelveProjectionCertificates.m2Full *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 2)) := by
  have h := QuaternionicLowMomentPositivity.tracePower_one_pow_mixed_in_positive_ray
    Q c B hB η hη 2 hk
  rw [tracePower_eq_twice_halfTrace B hB η] at h
  simpa [ElevenTwelveProjectionCertificates.m2Full, ElevenTwelveProjectionCertificates.z1,
    DimensionElevenTwelveDensity.p1, densityValues] using h

theorem m2One_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 2 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η)
        (ElevenTwelveProjectionCertificates.m2One (Fintype.card κ)) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 2)) := by
  have h := QuaternionicLowMomentPositivity.M₂₁_mixed_in_positive_ray Q c B hB η hη hk
  simp only [tracePower_eq_twice_halfTrace B hB η] at h
  rw [m2One_eval_values]
  have hc : algebraMap ℚ (CE V) (1 / ((Fintype.card κ : ℚ) * (Fintype.card κ + 1))) =
      algebraMap ℝ (CE V) (1 / ((Fintype.card κ : ℝ) * (Fintype.card κ + 1))) := by
    rw [IsScalarTower.algebraMap_apply ℚ ℝ (CE V)]
    congr 1
    simp
  rw [hc, ← Algebra.smul_def]
  simpa only [one_div] using h

end
end QuaternionicSymmetry.PrintedGaussianProjectionPositivity
