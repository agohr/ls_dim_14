import QuaternionicSymmetry.PrintedGaussianProjectionPositivity
import QuaternionicSymmetry.PrintedQuarticDensityPositivity
import QuaternionicSymmetry.QuaternionicZeroBlockPadding
import QuaternionicSymmetry.ElevenTwelveLinearAssembly

/-! The twelve printed certificate generators have the required pointwise
signs for actual Hermitian anti-self-dual coefficients and hyperholomorphic
2-forms. The zero H block is derived by padding. This does not identify the
coefficients with manifold curvature or interpret the index globally. -/
namespace QuaternionicSymmetry.QuaternionicC12Pointwise

open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
  PrintedProjectionCubicPositivity PrintedGaussianProjectionPositivity
  PrintedQuarticDensityPositivity QuaternionicZeroBlockPadding
  ElevenTwelveLinearAssembly

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 150000

private theorem eval_mul_u {R : Type*} [CommRing R] [Algebra ℚ R]
    (v : Fin 6 → R) (p : DimensionElevenTwelveDensity.P) (j : ℕ) :
    aeval v (p * DimensionElevenTwelveDensity.u ^ j) = aeval v p * v 0 ^ j := by
  simp only [map_mul, map_pow, DimensionElevenTwelveDensity.u, aeval_X]

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem generators11_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 11)
    (B : β → Matrix (Fin 11 ⊕ Fin 11) (Fin 11 ⊕ Fin 11) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 12) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators11 i)) := by
  have hH : ∀ b, (B b).IsHermitian := fun b => (hB b).1
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hH b)
  have h0 := m1_mixed_in_positive_ray Q c B hH η hη (by omega)
  have h1 := m2One_mixed_in_positive_ray Q c (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h1
  have h2 := m2Full_mixed_in_positive_ray Q c B hH η hη (by omega)
  have h3 := m3_mixed_in_positive_ray Q c 2 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h3
  have h4 := m3_mixed_in_positive_ray Q c 3 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h4
  have h5 := m3_mixed_in_positive_ray Q c 4 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h5
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := QuarticOrbitalEleven.spectra_admissible
  have h6 := orbital11_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalEleven.a₁ ha1 B hB η hη (by omega)
  have h7 := orbital11_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalEleven.a₂ ha2 B hB η hη (by omega)
  have h8 := orbital11_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalEleven.a₃ ha3 B hB η hη (by omega)
  have h9 := orbital11_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalEleven.a₄ ha4 B hB η hη (by omega)
  have h10 := orbital11_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalEleven.a₅ ha5 B hB η hη (by omega)
  have h11 := f5_mixed_in_positive_ray Q c B hH η hη (by omega)
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h1 h3 h4 h5
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (ElevenTwelveProjectionCertificates.m1Full * DimensionElevenTwelveDensity.u ^ 10))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m2One 24) * DimensionElevenTwelveDensity.u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (ElevenTwelveProjectionCertificates.m2Full * DimensionElevenTwelveDensity.u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h2
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 24 2) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h3
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 24 3) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h4
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 24 4) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h5
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital11 QuarticOrbitalEleven.a₁) * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h6
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital11 QuarticOrbitalEleven.a₂) * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h7
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital11 QuarticOrbitalEleven.a₃) * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h8
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital11 QuarticOrbitalEleven.a₄) * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h9
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital11 QuarticOrbitalEleven.a₅) * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h10
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (DimensionElevenTwelveDensity.f5 * DimensionElevenTwelveDensity.u ^ 6))
    rw [eval_mul_u]
    simpa only [hn] using h11

theorem generators12_in_positive_ray
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = 12)
    (B : β → Matrix (Fin 12 ⊕ Fin 12) (Fin 12 ⊕ Fin 12) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (i : Fin 12) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (aeval (densityValues Q c B η) (generators12 i)) := by
  have hH : ∀ b, (B b).IsHermitian := fun b => (hB b).1
  have hP : ∀ b, (padTwo (B b)).IsHermitian := fun b => padTwo_isHermitian _ (hH b)
  have h0 := m1_mixed_in_positive_ray Q c B hH η hη (by omega)
  have h1 := m2One_mixed_in_positive_ray Q c (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h1
  have h2 := m2Full_mixed_in_positive_ray Q c B hH η hη (by omega)
  have h3 := m3_mixed_in_positive_ray Q c 1 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h3
  have h4 := m3_mixed_in_positive_ray Q c 2 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h4
  have h5 := m3_mixed_in_positive_ray Q c 3 (by decide) (by decide)
    (fun b => padTwo (B b)) hP η hη (by omega)
  rw [densityValues_padTwo] at h5
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := QuarticOrbitalTwelve.spectra_admissible
  have h6 := orbital12_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalTwelve.b₁ ha1 B hB η hη (by omega)
  have h7 := orbital12_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalTwelve.b₂ ha2 B hB η hη (by omega)
  have h8 := orbital12_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalTwelve.b₃ ha3 B hB η hη (by omega)
  have h9 := orbital12_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalTwelve.b₄ ha4 B hB η hη (by omega)
  have h10 := orbital12_density_mixed_in_positive_ray hsource Q c
    QuarticOrbitalTwelve.b₅ ha5 B hB η hη (by omega)
  have h11 := f5_mixed_in_positive_ray Q c B hH η hη (by omega)
  norm_num only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at h1 h3 h4 h5
  fin_cases i
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (ElevenTwelveProjectionCertificates.m1Full * DimensionElevenTwelveDensity.u ^ 11))
    rw [eval_mul_u]
    simpa only [hn] using h0
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m2One 26) * DimensionElevenTwelveDensity.u ^ 10))
    rw [eval_mul_u]
    simpa only [hn] using h1
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (ElevenTwelveProjectionCertificates.m2Full * DimensionElevenTwelveDensity.u ^ 10))
    rw [eval_mul_u]
    simpa only [hn] using h2
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 26 1) * DimensionElevenTwelveDensity.u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h3
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 26 2) * DimensionElevenTwelveDensity.u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h4
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((ElevenTwelveProjectionCertificates.m3 26 3) * DimensionElevenTwelveDensity.u ^ 9))
    rw [eval_mul_u]
    simpa only [hn] using h5
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital12 QuarticOrbitalTwelve.b₁) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h6
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital12 QuarticOrbitalTwelve.b₂) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h7
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital12 QuarticOrbitalTwelve.b₃) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h8
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital12 QuarticOrbitalTwelve.b₄) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h9
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      ((QuarticOrbitalDensityBridge.orbital12 QuarticOrbitalTwelve.b₅) * DimensionElevenTwelveDensity.u ^ 8))
    rw [eval_mul_u]
    simpa only [hn] using h10
  · change PositiveRay.Contains _ (aeval (densityValues Q c B η)
      (DimensionElevenTwelveDensity.f5 * DimensionElevenTwelveDensity.u ^ 7))
    rw [eval_mul_u]
    simpa only [hn] using h11

end
end QuaternionicSymmetry.QuaternionicC12Pointwise
