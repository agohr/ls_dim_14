import QuaternionicSymmetry.PrintedLowerSimpleMoments
import QuaternionicSymmetry.QuaternionicZeroBlockPadding

/-! The six nonscalar terms of the printed dimension-seven certificate
are actual positive-ray forms for Hermitian matrix coefficients. -/
namespace QuaternionicSymmetry.QuaternionicSevenPointwise
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

def generators7 : Fin 6 → DimensionElevenTwelveDensity.P := ![
  m1 16 16 * u ^ 6,
  m2Full * u ^ 5,
  m2One 16 * u ^ 5,
  m3Full * u ^ 4,
  m3 16 1 * u ^ 4,
  m3 16 2 * u ^ 4]

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem generators7_in_positive_ray
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 7)
    (B : β → Matrix (Fin 7 ⊕ Fin 7) (Fin 7 ⊕ Fin 7) ℂ)
    (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 6) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators7 i)) := by
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hB b)
  have h0 := m1_mixed_in_positive_ray Q c B hB η hη 16 16 (by norm_num) (by omega)
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
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h2 h4 h5
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m1 16 16 * u ^ 6))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2Full * u ^ 5))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m2One 16 * u ^ 5))
    rw [eval_mul_u]
    simpa only [hn] using h2
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3Full * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h3
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3 16 1 * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h4
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η) (m3 16 2 * u ^ 4))
    rw [eval_mul_u]
    simpa only [hn] using h5

end
end QuaternionicSymmetry.QuaternionicSevenPointwise
