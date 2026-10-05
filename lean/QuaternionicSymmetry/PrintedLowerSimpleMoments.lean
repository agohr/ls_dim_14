import QuaternionicSymmetry.PrintedLowerGaussianPositivity

/-! The full first and third trace powers in the dimensions 7–10 tables
are exact positive-ray moments, including the printed first-moment scale. -/
namespace QuaternionicSymmetry.PrintedLowerSimpleMoments
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  QuaternionicTraceConventionBridge PrintedProjectionCubicPositivity
  PrintedGaussianProjectionPositivity PrintedCertificatesSevenTen
  QuaternionicLowMomentPositivity DimensionElevenTwelveDensity
  QuaternionicAhatPositivity
  ElevenTwelveProjectionCertificates
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 150000

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem m3Full_eval (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) :
    MvPolynomial.aeval (densityValues Q c B η) m3Full =
      tracePower B η 1 ^ 3 := by
  unfold m3Full z1 p1
  simp [densityValues]
  rw [tracePower_eq_twice_halfTrace B hB η 1]


theorem m3Full_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (B : β → Matrix κ κ ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (hk : 3 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) m3Full *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 3)) := by
  rw [m3Full_eval Q c B hB η]
  exact tracePower_one_pow_mixed_in_positive_ray Q c B hB η hη 3 hk


omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem m1_eval (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (r ell : ℚ) :
    MvPolynomial.aeval (densityValues Q c B η) (m1 r ell) =
      algebraMap ℚ (CE V) (ell/r) * tracePower B η 1 := by
  simp [m1, z1, p1, densityValues, tracePower_eq_twice_halfTrace B hB η]


theorem m1_mixed_in_positive_ray (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (B : β → Matrix κ κ ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (r ell : ℚ) (hr : 0 ≤ ell/r)
    (hk : 1 ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (MvPolynomial.aeval (densityValues Q c B η) (m1 r ell) *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - 1)) := by
  rw [m1_eval Q c B hB η]
  have hs : algebraMap ℚ (CE V) (ell/r) =
      algebraMap ℝ (CE V) ((ell/r : ℚ) : ℝ) :=
    (IsScalarTower.algebraMap_apply ℚ ℝ (CE V) (ell/r)).symm
  rw [hs]
  have hp := tracePower_one_pow_mixed_in_positive_ray Q c B hB η hη 1 hk
  have hn : (0:ℝ) ≤ ((ell/r : ℚ) : ℝ) := by exact_mod_cast hr
  have hsm := PositiveRay.smul hp hn
  rw [← Algebra.smul_def]
  simpa only [pow_one, smul_mul_assoc] using hsm

end
end QuaternionicSymmetry.PrintedLowerSimpleMoments
