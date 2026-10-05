import QuaternionicSymmetry.GaussianOrbitalFrameMixture

/-! The fixed-probe PSD/Haar/Gaussian identity as an equality of real
polynomials, and hence after substitution into any commutative real algebra. -/

namespace QuaternionicSymmetry.GaussianOrbitalPolynomialMixture

open Matrix MeasureTheory CompactSymplecticHaar QuaternionicMatrixModel
  GaussianOrbitalFrameMixture
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

variable {n : ℕ} {β : Type*} [Fintype β]

/-- The universal compact-coordinate linear contraction for a fixed probe. -/
def universalProbeCoefficient (q : ProbeIndex n) :
    MvPolynomial (CoordinateIndex n β) (MvPolynomial β ℝ) :=
  ∑ b, MvPolynomial.C (MvPolynomial.X b) * MvPolynomial.X (q,b)

/-- The coefficientwise Haar average of the fixed-probe covariance power. -/
def haarCovariancePolynomial
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) : MvPolynomial β ℝ :=
  CompactPolynomialAverage.average (probability (standardJ n))
    (frameCoordinates P B)
      ((∑ q, (universalProbeCoefficient q) ^ 2) ^ k)

/-- The intrinsic Gaussian orbital polynomial has coefficients obtained by
integrating finite Schur coordinates. -/
def gaussianOrbitalPolynomial
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) : MvPolynomial β ℝ :=
  ∑ lam : OrbitalRealCone.Shape k,
    MvPolynomial.C
      ((∫ t : ProbeIndex n → ℝ,
        OrbitalRealCone.matrixCoordinates (probeSum P t) k
          ∂GaussianWick.standardMeasure) lam) *
      MatrixTracePolynomial.schurPolynomial B lam.1

theorem map_universalProbeCoefficient (x : β → ℝ) (q : ProbeIndex n) :
    MvPolynomial.map (MvPolynomial.aeval x).toRingHom
      (universalProbeCoefficient (β := β) q) = mixingCoefficient x q := by
  simp [universalProbeCoefficient, mixingCoefficient]

theorem eval_haarCovariancePolynomial
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (x : β → ℝ) :
    (haarCovariancePolynomial P B k).eval x =
      CompactPolynomialAverage.average (probability (standardJ n))
        (frameCoordinates P B)
          ((∑ q, (mixingCoefficient x q) ^ 2) ^ k) := by
  rw [← MvPolynomial.aeval_eq_eval]
  unfold haarCovariancePolynomial
  rw [CompactPolynomialAverage.average_map]
  simp only [map_pow, map_sum, map_universalProbeCoefficient]

theorem eval_haarCovariancePolynomial_integral
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hGram : ∀ (g : CompactSymplecticHaar.Group n) (x : β → ℝ),
      CovariancePolynomial.quadratic (frameCovariance A B g) x =
        ∑ q, probeContraction P B x g q ^ 2)
    (k : ℕ) (x : β → ℝ) :
    (haarCovariancePolynomial P B k).eval x =
      ∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k
        ∂probability (standardJ n) := by
  rw [eval_haarCovariancePolynomial]
  let p : MvPolynomial (CoordinateIndex n β) ℝ :=
    (∑ q, (mixingCoefficient x q) ^ 2) ^ k
  have h := CompactPolynomialAverage.integral_evaluation
    (probability (standardJ n)) (frameCoordinates P B)
    (continuous_frameCoordinates P B) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) p
  simp only [LinearMap.id_apply, Algebra.algebraMap_self_apply] at h
  rw [← h]
  congr 1
  funext g
  simp only [p, map_pow, map_sum, mixingCoefficient_eval]
  rw [hGram g x]

theorem integrable_probe_coordinates
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) :
    Integrable (fun t : ProbeIndex n → ℝ =>
      OrbitalRealCone.matrixCoordinates (probeSum P t) k)
      GaussianWick.standardMeasure := by
  apply OrbitalRealCone.integrable_matrixCoordinates_of_schurValues
  intro lam
  have h := GaussianPolynomialIntegration.polynomial_integrable
    (MatrixTracePolynomial.schurPolynomial P lam.1)
  simpa only [MatrixTracePolynomial.eval_schurPolynomial,
    MatrixTracePolynomial.matrixCombination, probeSum] using h

theorem eval_gaussianOrbitalPolynomial_integral
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (x : β → ℝ) :
    (gaussianOrbitalPolynomial P B k).eval x =
      ∫ t : ProbeIndex n → ℝ,
        (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
          (probeSum P t) B k).eval x
        ∂GaussianWick.standardMeasure := by
  let μ : Measure (ProbeIndex n → ℝ) := GaussianWick.standardMeasure
  have hfi := integrable_probe_coordinates P k
  calc
    (gaussianOrbitalPolynomial P B k).eval x =
        ∑ lam : OrbitalRealCone.Shape k,
          (∫ t : ProbeIndex n → ℝ,
            OrbitalRealCone.matrixCoordinates (probeSum P t) k lam ∂μ) *
              (MatrixTracePolynomial.schurPolynomial B lam.1).eval x := by
      simp only [gaussianOrbitalPolynomial, map_sum, map_mul, MvPolynomial.eval_C]
      apply Finset.sum_congr rfl
      intro lam _
      rw [OrbitalRealCone.integral_matrixCoordinates_apply _ hfi]
      rfl
    _ = ∑ lam : OrbitalRealCone.Shape k,
          ∫ t : ProbeIndex n → ℝ,
            OrbitalRealCone.matrixCoordinates (probeSum P t) k lam *
              (MatrixTracePolynomial.schurPolynomial B lam.1).eval x ∂μ := by
      apply Finset.sum_congr rfl
      intro lam _
      rw [integral_mul_const]
    _ = ∫ t : ProbeIndex n → ℝ,
          ∑ lam : OrbitalRealCone.Shape k,
            OrbitalRealCone.matrixCoordinates (probeSum P t) k lam *
              (MatrixTracePolynomial.schurPolynomial B lam.1).eval x ∂μ := by
      rw [integral_finset_sum]
      intro lam _
      exact (hfi.eval lam).mul_const _
    _ = _ := by
      congr 1
      funext t
      rw [OrbitalRealCone.finiteOrbitalPolynomial_eq_coordinates]
      simp

/-- The checked scalar Haar/Gaussian mixture determines an exact equality
of universal real polynomials. -/
theorem fixed_probe_polynomial_mixture
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (A : Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (P : ProbeIndex (m+6) → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q))
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b))
    (hGram : ∀ (g : CompactSymplecticHaar.Group (m+6)) (x : β → ℝ),
      CovariancePolynomial.quadratic (frameCovariance A B g) x =
        ∑ q, probeContraction P B x g q ^ 2) :
    haarCovariancePolynomial P B k =
      MvPolynomial.C (((2 ^ k * k.factorial : ℕ) : ℝ)) *
        gaussianOrbitalPolynomial P B k := by
  apply MvPolynomial.funext
  intro x
  rw [eval_haarCovariancePolynomial_integral A P B hGram k x,
    MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_gaussianOrbitalPolynomial_integral]
  exact fixed_frame_gaussian_orbital_mixture
    hsource m k hm hk A P hP B hB hGram x

/-- The same exact identity after substitution in any commutative real
algebra, including nilpotent even exterior forms. -/
theorem fixed_probe_polynomial_mixture_aeval
    {S : Type*} [CommRing S] [Algebra ℝ S]
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (A : Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (P : ProbeIndex (m+6) → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q))
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b))
    (hGram : ∀ (g : CompactSymplecticHaar.Group (m+6)) (x : β → ℝ),
      CovariancePolynomial.quadratic (frameCovariance A B g) x =
        ∑ q, probeContraction P B x g q ^ 2)
    (η : β → S) :
    MvPolynomial.aeval η (haarCovariancePolynomial P B k) =
      ((2 ^ k * k.factorial : ℕ) : S) *
        MvPolynomial.aeval η (gaussianOrbitalPolynomial P B k) := by
  have h := congrArg (MvPolynomial.aeval η)
    (fixed_probe_polynomial_mixture hsource m k hm hk A P hP B hB hGram)
  simpa only [map_mul, MvPolynomial.aeval_C, map_natCast] using h

/-- PSD input yields a universal polynomial mixture and a closed-cone
Gaussian coordinate average with one fixed spectral-class probe family. -/
theorem psd_polynomial_mixture_mem_closed_cone
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (A : Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hA : A.PosSemidef)
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b)) :
    ∃ P : ProbeIndex (m+6) → Matrix (Fin (m+6) ⊕ Fin (m+6))
        (Fin (m+6) ⊕ Fin (m+6)) ℂ,
      (∀ q, HermitianAntiSelfDual (P q)) ∧
      haarCovariancePolynomial P B k =
        MvPolynomial.C (((2 ^ k * k.factorial : ℕ) : ℝ)) *
          gaussianOrbitalPolynomial P B k ∧
      (∫ t : ProbeIndex (m+6) → ℝ,
        OrbitalRealCone.matrixCoordinates (probeSum P t) k
          ∂GaussianWick.standardMeasure) ∈
        OrbitalRealCone.cone (m+6) k := by
  obtain ⟨P, hP, hGram⟩ := exists_fixed_frame_probes
    (S := ℝ) A B hA hB
  exact ⟨P, hP,
    fixed_probe_polynomial_mixture hsource m k hm hk A P hP B hB hGram,
    gaussian_probe_coordinates_mem_closed_cone P hP k⟩

end
end QuaternionicSymmetry.GaussianOrbitalPolynomialMixture
