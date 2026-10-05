import QuaternionicSymmetry.FixedSymplecticTraceGram
import QuaternionicSymmetry.GaussianOrbitalNormalization
import QuaternionicSymmetry.OrbitalRealSquaredSpectrum
import QuaternionicSymmetry.OrbitalRealCone

/-! A numerical PSD matrix supplies fixed symplectic trace probes for all
frames. Their Gaussian moments are exactly the frame covariance powers with
the source's factorial normalization. -/

namespace QuaternionicSymmetry.GaussianOrbitalFrameMixture

open Matrix QuaternionicMatrixModel SymplecticTraceProjection
  CompactSymplecticHaar QuaternionicHaarOrbital GaussianPolynomialExpectation
  MeasureTheory
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

variable {n : ℕ} {β S : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]

abbrev ProbeIndex (n : ℕ) :=
  (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × Fin 2

abbrev CoordinateIndex (n : ℕ) (β : Type*) := ProbeIndex n × β

def frameCoordinates
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : Group n) : CoordinateIndex n β → ℝ :=
  fun qb => traceCoordinates (standardJ n) (P qb.1) B g qb.2

omit [Fintype β] in
theorem continuous_frameCoordinates
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    Continuous (frameCoordinates P B) := by
  apply continuous_pi
  intro qb
  exact (continuous_apply qb.2).comp
    (continuous_traceCoordinates (standardJ n) (P qb.1) B)

def mixingCoefficient (x : β → ℝ) (q : ProbeIndex n) :
    MvPolynomial (CoordinateIndex n β) ℝ :=
  ∑ b, MvPolynomial.C (x b) * MvPolynomial.X (q,b)

def mixingPolynomial (x : β → ℝ) (k : ℕ) :
    MvPolynomial (ProbeIndex n) (MvPolynomial (CoordinateIndex n β) ℝ) :=
  linearPolynomial (mixingCoefficient x) ^ (2 * k)

/-- The same curvature family expressed at a compact symplectic frame. -/
def frameFamily (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : Group n) (b : β) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  conjugate (standardJ n) g (B b)

omit [Fintype β] in
theorem frameFamily_antiSelfDual
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b)) (g : Group n) (b : β) :
    HermitianAntiSelfDual (frameFamily B g b) :=
  HermitianAntiSelfDual_conjugate (B b) (hB b) g

def frameCovariance (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : Group n) : Matrix β β ℝ :=
  MatrixMoments.covarianceMatrix A (frameFamily B g)

def probeContraction
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (η : β → S) (g : Group n) (q : ProbeIndex n) : S :=
  ∑ b, algebraMap ℝ S (traceCoordinates (standardJ n) (P q) B g b) * η b

theorem mixingCoefficient_eval
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (x : β → ℝ) (g : Group n) (q : ProbeIndex n) :
    (mixingCoefficient x q).eval (frameCoordinates P B g) =
      probeContraction P B x g q := by
  simp only [mixingCoefficient, frameCoordinates, probeContraction,
    map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro b _
  simpa using mul_comm (x b)
    (traceCoordinates (standardJ n) (P q) B g b)

theorem mixingPolynomial_eval
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (x : β → ℝ) (g : Group n) (t : ProbeIndex n → ℝ) (k : ℕ) :
    ((mixingPolynomial x k).eval
      (fun q => MvPolynomial.C (t q))).eval (frameCoordinates P B g) =
        (GaussianFunctional.combination (probeContraction P B x g) t) ^ (2 * k) := by
  simp [mixingPolynomial, linearPolynomial, GaussianFunctional.combination,
    mixingCoefficient_eval, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]

/-- A real linear combination of the fixed probes. -/
def probeSum
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (t : ProbeIndex n → ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  ∑ q, (t q : ℂ) • P q

theorem probeSum_antiSelfDual
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q)) (t : ProbeIndex n → ℝ) :
    HermitianAntiSelfDual (probeSum P t) := by
  change probeSum P t ∈ QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule n
  unfold probeSum
  apply Submodule.sum_mem
  intro q _
  change (t q : ℝ) • P q ∈
    QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule n
  exact Submodule.smul_mem _ _ (hP q)

omit [Fintype β] in
/-- The Gaussian linear combination of probe contractions is exactly one
scalar orbital contraction for the fixed matrix `probeSum P t`. -/
theorem traceCoordinates_probeSum
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (t : ProbeIndex n → ℝ) (g : Group n) (b : β) :
    traceCoordinates (standardJ n) (probeSum P t) B g b =
      ∑ q, t q * traceCoordinates (standardJ n) (P q) B g b := by
  simp only [traceCoordinates_eq_trace, probeSum, Finset.sum_mul,
    Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp [Complex.mul_re]

theorem gaussianCombination_eq_orbitalContraction
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (η : β → S) (g : Group n) (t : ProbeIndex n → ℝ) :
    GaussianFunctional.combination (probeContraction P B η g) t =
      ∑ b, algebraMap ℝ S
        (traceCoordinates (standardJ n) (probeSum P t) B g b) * η b := by
  simp only [GaussianFunctional.combination, probeContraction,
    traceCoordinates_probeSum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Algebra.smul_def, map_mul, mul_assoc]

/-- Fixed probes work at every symplectic frame, without choosing a new
Gram factorization after `g` is known. -/
theorem exists_fixed_frame_probes
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, HermitianAntiSelfDual (B b)) :
    ∃ P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      (∀ q, HermitianAntiSelfDual (P q)) ∧
      ∀ (g : Group n) (η : β → S),
        CovariancePolynomial.quadratic (frameCovariance A B g) η =
          ∑ q, probeContraction P B η g q ^ 2 := by
  obtain ⟨P, hP, hsq⟩ :=
    FixedSymplecticTraceGram.psd_fixed_symplectic_covariance_squares_all_families
      (β := β) (S := S) A hA
  refine ⟨P, hP, ?_⟩
  intro g η
  have h := hsq (frameFamily B g) (frameFamily_antiSelfDual B hB g) η
  change CovariancePolynomial.quadratic (frameCovariance A B g) η = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [traceCoordinates_eq_trace, frameFamily,
    CompactSymplecticHaar.conjugate, mul_assoc]

theorem normalized_gaussian_frame_moment
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hGram : ∀ (g : Group n) (η : β → S),
      CovariancePolynomial.quadratic (frameCovariance A B g) η =
        ∑ q, probeContraction P B η g q ^ 2)
    (g : Group n) (η : β → S) (k : ℕ) :
    ((2 ^ k * k.factorial : ℕ) : S) *
      expectation (linearPolynomial (probeContraction P B η g) ^ (2 * k)) =
        ((2 * k).factorial : S) *
          CovariancePolynomial.quadratic (frameCovariance A B g) η ^ k := by
  rw [hGram g η]
  exact GaussianOrbitalNormalization.universal_factorial_wick
    (probeContraction P B η g) k

/-- Every fixed real Gaussian coefficient vector produces one genuine scalar
symplectic orbital moment. The spectral data are used only to prove this
identity; the polynomial on the right is intrinsic in `probeSum P t`. -/
theorem probeSum_orbital_moment
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (P : ProbeIndex (m+6) → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q))
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b))
    (t : ProbeIndex (m+6) → ℝ) (x : β → ℝ) :
    (∫ g, (∑ b, traceCoordinates (standardJ (m+6)) (probeSum P t) B g b * x b) ^
        (2*k) ∂probability (standardJ (m+6))) =
      ((2*k).factorial : ℝ) *
        (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial (probeSum P t) B k).eval x := by
  obtain ⟨eigen, u, hu⟩ :=
    OrbitalSymplecticSpectral.exists_symplectic_diagonalization
      (probeSum_antiSelfDual P hP t)
  have hdiag (s : β → ℝ) :
      ∃ (eigen : Fin (m+6) → ℝ) (v : CompactSymplecticHaar.Group (m+6)),
        MatrixTracePolynomial.matrixCombination B s =
          conjugate (standardJ (m+6)) v
            (OrbitalDiagonalSpectra.hermitianDiagonal eigen) :=
    OrbitalSymplecticSpectral.exists_symplectic_diagonalization
      (OrbitalPointwisePolynomialSign.matrixCombination_HermitianAntiSelfDual B hB s)
  exact OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial_integral
    hsource m k hm hk (probeSum P t) B eigen u hu hdiag x

theorem mixed_compact_moment_eq_orbital
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (P : ProbeIndex (m+6) → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q))
    (B : β → Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : ∀ b, HermitianAntiSelfDual (B b))
    (t : ProbeIndex (m+6) → ℝ) (x : β → ℝ) :
    (∫ g, ((mixingPolynomial x k).eval
      (fun q => MvPolynomial.C (t q))).eval (frameCoordinates P B g)
        ∂probability (standardJ (m+6))) =
      ((2*k).factorial : ℝ) *
        (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial (probeSum P t) B k).eval x := by
  have h := probeSum_orbital_moment hsource m k hm hk P hP B hB t x
  convert h using 1
  congr 1
  funext g
  rw [mixingPolynomial_eval, gaussianCombination_eq_orbitalContraction]
  simp

/-- Actual Haar and Gaussian integration of the fixed-probe frame
construction. This is the exact Wick/orbital normalization before dividing
by the positive double factorial. -/
theorem fixed_frame_gaussian_orbital_integral
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
    (x : β → ℝ) :
    (Nat.doubleFactorial (2 * k - 1) : ℝ) *
      (∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k
        ∂probability (standardJ (m+6))) =
      ((2*k).factorial : ℝ) *
        (∫ t : ProbeIndex (m+6) → ℝ,
          (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
            (probeSum P t) B k).eval x
          ∂GaussianWick.standardMeasure) := by
  let p := mixingPolynomial (n := m+6) x k
  let μ := probability (standardJ (m+6))
  let coord := frameCoordinates P B
  have hF := GaussianCompactInterchange.integral_gaussian_then_compact
    μ coord (continuous_frameCoordinates P B) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) p
  have hR := GaussianCompactInterchange.integral_compact_then_gaussian
    μ coord (continuous_frameCoordinates P B) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) p
  have hswap := hF.symm.trans hR
  have hgauss (g : CompactSymplecticHaar.Group (m+6)) :
      (∫ t : ProbeIndex (m+6) → ℝ,
        ((p.eval (fun q => MvPolynomial.C (t q))).eval (coord g))
          ∂GaussianWick.standardMeasure) =
        (Nat.doubleFactorial (2 * k - 1) : ℝ) *
          CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k := by
    simp only [p, coord, mixingPolynomial_eval]
    have h := GaussianWick.integral_combination_even
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (probeContraction P B x g) k
    simp only [LinearMap.id_apply] at h
    rw [h, ← hGram g x]
  have hhaar (t : ProbeIndex (m+6) → ℝ) :
      (∫ g, ((p.eval (fun q => MvPolynomial.C (t q))).eval (coord g)) ∂μ) =
        ((2*k).factorial : ℝ) *
          (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
            (probeSum P t) B k).eval x :=
    mixed_compact_moment_eq_orbital hsource m k hm hk P hP B hB t x
  simp only [LinearMap.id_apply, LinearMap.comp_apply,
    GaussianCompactInterchange.compactEvalLinear_apply,
    MvPolynomial.algebraMap_eq, Algebra.algebraMap_self_apply] at hswap
  rw [show (∫ g, (∫ t : ProbeIndex (m+6) → ℝ,
      ((p.eval (fun q => MvPolynomial.C (t q))).eval (coord g))
        ∂GaussianWick.standardMeasure) ∂μ) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) *
        (∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k ∂μ) by
      simp_rw [hgauss]
      rw [integral_const_mul]] at hswap
  rw [show (∫ t : ProbeIndex (m+6) → ℝ,
      (∫ g, ((p.eval (fun q => MvPolynomial.C (t q))).eval (coord g)) ∂μ)
        ∂GaussianWick.standardMeasure) =
      ((2*k).factorial : ℝ) *
        (∫ t : ProbeIndex (m+6) → ℝ,
          (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
            (probeSum P t) B k).eval x ∂GaussianWick.standardMeasure) by
      simp_rw [hhaar]
      rw [integral_const_mul]] at hswap
  exact hswap

/-- The final numerical PSD-to-orbital Gaussian mixture has exactly the
`2^k k!` coefficient. The probe family is fixed before Haar or Gaussian
integration. -/
theorem fixed_frame_gaussian_orbital_mixture
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
    (x : β → ℝ) :
    (∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k
      ∂probability (standardJ (m+6))) =
      ((2 ^ k * k.factorial : ℕ) : ℝ) *
        (∫ t : ProbeIndex (m+6) → ℝ,
          (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
            (probeSum P t) B k).eval x
          ∂GaussianWick.standardMeasure) := by
  have h := fixed_frame_gaussian_orbital_integral
    hsource m k hm hk A P hP B hB hGram x
  have hdf : (Nat.doubleFactorial (2 * k - 1) : ℝ) ≠ 0 := by positivity
  have hfact : ((2*k).factorial : ℝ) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) *
        ((2 ^ k * k.factorial : ℕ) : ℝ) := by
    norm_cast
    rw [GaussianOrbitalNormalization.factorial_eq_orbital_wick_factor]
    ring
  rw [hfact] at h
  exact (mul_left_cancel₀ hdf (by simpa only [mul_assoc] using h))

/-- The PSD input itself yields one fixed symplectic probe family and the
normalized Haar/Gaussian orbital mixture for every numerical coefficient
vector. No frame-dependent Gram or spectral selection is made. -/
theorem psd_gaussian_orbital_mixture
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
      ∀ x : β → ℝ,
        (∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k
          ∂probability (standardJ (m+6))) =
          ((2 ^ k * k.factorial : ℕ) : ℝ) *
            (∫ t : ProbeIndex (m+6) → ℝ,
              (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
                (probeSum P t) B k).eval x
              ∂GaussianWick.standardMeasure) := by
  obtain ⟨P, hP, hGram⟩ := exists_fixed_frame_probes
    (S := ℝ) A B hA hB
  exact ⟨P, hP, fun x =>
    fixed_frame_gaussian_orbital_mixture hsource m k hm hk A P hP B hB hGram x⟩

/-- The Gaussian average of intrinsic finite orbital coordinates is in the
closed cone generated by all nonnegative real squared spectra. The integrand
uses `probeSum P t`, so no measurable eigenvalue choice is required. -/
theorem gaussian_probe_coordinates_mem_closed_cone
    (P : ProbeIndex n → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hP : ∀ q, HermitianAntiSelfDual (P q)) (k : ℕ) :
    (∫ t : ProbeIndex n → ℝ,
      OrbitalRealCone.matrixCoordinates (probeSum P t) k
        ∂GaussianWick.standardMeasure) ∈ OrbitalRealCone.cone n k := by
  letI : IsProbabilityMeasure
      (GaussianWick.standardMeasure : Measure (ProbeIndex n → ℝ)) := by
    change IsProbabilityMeasure
      (Measure.pi (fun _ : ProbeIndex n => ProbabilityTheory.gaussianReal 0 1))
    infer_instance
  have hfi : Integrable (fun t : ProbeIndex n → ℝ =>
      OrbitalRealCone.matrixCoordinates (probeSum P t) k)
      GaussianWick.standardMeasure := by
    apply OrbitalRealCone.integrable_matrixCoordinates_of_schurValues
    intro lam
    have h := GaussianPolynomialIntegration.polynomial_integrable
      (MatrixTracePolynomial.schurPolynomial P lam.1)
    simpa only [MatrixTracePolynomial.eval_schurPolynomial,
      MatrixTracePolynomial.matrixCombination, probeSum] using h
  apply OrbitalRealCone.integral_matrixCoordinates_mem_cone
    (fun t => probeSum P t)
  · exact Filter.Eventually.of_forall (fun t => probeSum_antiSelfDual P hP t)
  · exact hfi

/-- The normalized PSD mixture and its closed scalar-orbital cone membership
use the same fixed probe family. -/
theorem psd_gaussian_mixture_mem_closed_cone
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
      (∀ x : β → ℝ,
        (∫ g, CovariancePolynomial.quadratic (frameCovariance A B g) x ^ k
          ∂probability (standardJ (m+6))) =
          ((2 ^ k * k.factorial : ℕ) : ℝ) *
            (∫ t : ProbeIndex (m+6) → ℝ,
              (OrbitalMatrixPolynomialBridge.finiteOrbitalPolynomial
                (probeSum P t) B k).eval x
              ∂GaussianWick.standardMeasure)) ∧
      (∫ t : ProbeIndex (m+6) → ℝ,
        OrbitalRealCone.matrixCoordinates (probeSum P t) k
          ∂GaussianWick.standardMeasure) ∈
        OrbitalRealCone.cone (m+6) k := by
  obtain ⟨P, hP, hmix⟩ :=
    psd_gaussian_orbital_mixture hsource m k hm hk A hA B hB
  exact ⟨P, hP, hmix, gaussian_probe_coordinates_mem_closed_cone P hP k⟩

end
end QuaternionicSymmetry.GaussianOrbitalFrameMixture
