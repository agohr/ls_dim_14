import QuaternionicSymmetry.PrintedLowerSimpleMoments
import QuaternionicSymmetry.QuaternionicZeroBlockPadding

/-! The six nonscalar terms of the printed dimension-ten certificate
are actual positive-ray forms for Hermitian matrix coefficients. -/
namespace QuaternionicSymmetry.QuaternionicTenPointwise
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedLowerSimpleMoments PrintedLowerGaussianPositivity
  PrintedProjectionCubicPositivity PrintedGaussianProjectionPositivity
  QuaternionicZeroBlockPadding PrintedCertificatesSevenTen
  ElevenTwelveProjectionCertificates DimensionElevenTwelveDensity
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

private theorem eval_mul_u {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) (p : DimensionElevenTwelveDensity.P) (j : ℕ) :
    aeval v (p * DimensionElevenTwelveDensity.u ^ j) = aeval v p * v 0 ^ j := by
  simp only [map_mul, map_pow, DimensionElevenTwelveDensity.u, aeval_X]

def generators10 : Fin 7 → DimensionElevenTwelveDensity.P := ![
  m1 22 1 * u ^ 9,
  m2Full * u ^ 8,
  m2One 22 * u ^ 8,
  m3Full * u ^ 7,
  m3 22 1 * u ^ 7,
  m3 22 2 * u ^ 7,
  ReconstructionExamples.f4 * u ^ 6]

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem generators10_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 10)
    (B : β → Matrix (Fin 10 ⊕ Fin 10) (Fin 10 ⊕ Fin 10) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 7) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators10 i)) := by
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hB b)
  have h0 := m1_mixed_in_positive_ray Q c B hB η hη 22 1 (by norm_num) (by omega)
  have h1 := m2Full_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h2 := m2One_mixed_in_positive_ray Q c (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h2
  have h3 := m3Full_mixed_in_positive_ray Q c B hB η hη (by omega)
  have h4 := m3_mixed_in_positive_ray Q c 1 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h4
  have h5 := m3_mixed_in_positive_ray Q c 2 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h5
  have h6 := f4_mixed_in_positive_ray Q c B hB η hη (by omega)
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h2 h4 h5
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m1 22 1 * u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2Full * u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2One 22 * u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h2
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3Full * u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h3
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3 22 1 * u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h4
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3 22 2 * u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h5

  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (ReconstructionExamples.f4 * u ^ 6))
    rw [eval_mul_u]
    simpa only [hn] using h6

end
end QuaternionicSymmetry.QuaternionicTenPointwise
