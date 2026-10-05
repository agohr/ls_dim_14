import QuaternionicSymmetry.GaussianOrbitalPolynomialMixture
import QuaternionicSymmetry.MatrixTraceReality

/-! The PSD mixture in the manuscript convention Y = -X². The sign is
transported through weighted Schur homogeneity before any substitution into
a possibly nilpotent coefficient algebra. -/

namespace QuaternionicSymmetry.GaussianOrbitalSignedMixture

open MatrixTracePolynomial OrbitalRealCone GaussianOrbitalFrameMixture
  GaussianOrbitalPolynomialMixture MeasureTheory

open scoped ComplexOrder MatrixOrder

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℝ S] [Algebra ℚ S]
  [IsScalarTower ℚ ℝ S]

/-- Evaluation of the finite Schur coordinate presentation. -/
def evaluateCoordinates {k : ℕ} (w : Coordinates k) (p : Fin 6 → S) : S :=
  ∑ lam : Shape k, algebraMap ℝ S (w lam) *
    MvPolynomial.aeval p (FiniteTypeCSchurSix.schur lam.1)

omit [IsScalarTower ℚ ℝ S] in
theorem evaluateCoordinates_weightedScaling {k : ℕ} (hk : k ≤ 6)
    (w : Coordinates k) (p : Fin 6 → S) (c : S) :
    evaluateCoordinates w (fun i => c ^ (i.val + 1) * p i) =
      c ^ k * evaluateCoordinates w p := by
  unfold evaluateCoordinates
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam _
  rw [FiniteSchurWeightedScaling.schur_weightedScaling c p k hk lam.1
    (List.mem_toFinset.mp lam.2)]
  ring

variable {n : ℕ} {β : Type*} [Fintype β]

/-- The Gaussian mixture polynomial has exactly the integrated intrinsic
Schur coordinates after any coefficient-algebra substitution. -/
theorem aeval_gaussianOrbitalPolynomial
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (η : β → S) :
    MvPolynomial.aeval η (gaussianOrbitalPolynomial P B k) =
      evaluateCoordinates
        (∫ t : ProbeIndex n → ℝ, matrixCoordinates (probeSum P t) k
          ∂GaussianWick.standardMeasure)
        (fun i => MvPolynomial.aeval η (tracePowerPolynomial B (i.val + 1))) := by
  unfold gaussianOrbitalPolynomial evaluateCoordinates
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  exact MvPolynomial.comp_aeval_apply
    (fun i : Fin 6 => tracePowerPolynomial B (i.val + 1))
    ((MvPolynomial.aeval η).restrictScalars ℚ) (FiniteTypeCSchurSix.schur lam.1)

/-- The signed power-sum substitution gives precisely the curvature sign
of the averaged Gaussian polynomial. -/
theorem evaluateCoordinates_signedTracePower
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (hk : k ≤ 6) (η : β → S) :
    evaluateCoordinates
        (∫ t : ProbeIndex n → ℝ, matrixCoordinates (probeSum P t) k
          ∂GaussianWick.standardMeasure)
        (fun i => signedTracePower (complexifiedMatrix B η) (i.val + 1)) =
      (-1 : S) ^ k * MvPolynomial.aeval η (gaussianOrbitalPolynomial P B k) := by
  rw [aeval_gaussianOrbitalPolynomial]
  have h := evaluateCoordinates_weightedScaling hk
    (∫ t : ProbeIndex n → ℝ, matrixCoordinates (probeSum P t) k
      ∂GaussianWick.standardMeasure)
    (fun i => MvPolynomial.aeval η (tracePowerPolynomial B (i.val + 1))) (-1 : S)
  simpa only [signedTracePower, aeval_tracePowerPolynomial] using h

/-- Exact fixed-probe PSD mixture with the manuscript's signed power sums.
Hermitian coefficients identify these variables with the literal half traces
inside the complexified algebra by `MatrixTraceReality`. -/
theorem fixed_probe_signed_mixture
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (A : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (P : ProbeIndex (m+6) →
      Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hP : ∀ q, QuaternionicMatrixModel.HermitianAntiSelfDual (P q))
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b))
    (hGram : ∀ (g : CompactSymplecticHaar.Group (m+6)) (x : β → ℝ),
      CovariancePolynomial.quadratic (frameCovariance A B g) x =
        ∑ q, probeContraction P B x g q ^ 2)
    (η : β → S) :
    (-1 : S) ^ k * MvPolynomial.aeval η (haarCovariancePolynomial P B k) =
      ((2 ^ k * k.factorial : ℕ) : S) *
        evaluateCoordinates
          (∫ t : ProbeIndex (m+6) → ℝ, matrixCoordinates (probeSum P t) k
            ∂GaussianWick.standardMeasure)
          (fun i => signedTracePower (complexifiedMatrix B η) (i.val + 1)) := by
  rw [evaluateCoordinates_signedTracePower P B k hk η,
    fixed_probe_polynomial_mixture_aeval hsource m k hm hk A P hP B hB hGram η]
  ring

/-- A numerical PSD test supplies the fixed probes and the signed orbital
mixture, uniformly for every substitution in the real coefficient algebra. -/
theorem psd_signed_mixture
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (A : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hA : A.PosSemidef)
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (B b)) :
    ∃ P : ProbeIndex (m+6) →
        Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ,
      (∀ q, QuaternionicMatrixModel.HermitianAntiSelfDual (P q)) ∧
      (∫ t : ProbeIndex (m+6) → ℝ, matrixCoordinates (probeSum P t) k
        ∂GaussianWick.standardMeasure) ∈ cone (m+6) k ∧
      ∀ η : β → S,
        (-1 : S) ^ k * MvPolynomial.aeval η (haarCovariancePolynomial P B k) =
          ((2 ^ k * k.factorial : ℕ) : S) *
            evaluateCoordinates
              (∫ t : ProbeIndex (m+6) → ℝ, matrixCoordinates (probeSum P t) k
                ∂GaussianWick.standardMeasure)
              (fun i => signedTracePower (complexifiedMatrix B η) (i.val + 1)) := by
  obtain ⟨P, hP, hGram⟩ := exists_fixed_frame_probes (S := ℝ) A B hA hB
  exact ⟨P, hP, gaussian_probe_coordinates_mem_closed_cone P hP k,
    fun η => fixed_probe_signed_mixture hsource m k hm hk A P hP B hB hGram η⟩

end
end QuaternionicSymmetry.GaussianOrbitalSignedMixture
