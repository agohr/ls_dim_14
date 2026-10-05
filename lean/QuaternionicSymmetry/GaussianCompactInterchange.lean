import QuaternionicSymmetry.GaussianOrbitalNormalization
import QuaternionicSymmetry.GaussianFunctionalPolynomial
import QuaternionicSymmetry.CompactPolynomialAverage
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Coefficientwise linearity and interchange of finite Gaussian and compact
averages. The coefficient algebra may contain nilpotents. -/

namespace QuaternionicSymmetry.GaussianCompactInterchange

open GaussianPolynomialExpectation CompactPolynomialAverage

noncomputable section

variable {ι S T : Type*} [Fintype ι] [CommRing S] [Algebra ℝ S]
    [CommRing T] [Algebra ℝ T]

/-- Apply a real-linear map separately to every polynomial coefficient. -/
def mapCoeffs (L : S →ₗ[ℝ] T) : MvPolynomial ι S →ₗ[ℝ] MvPolynomial ι T :=
  Finsupp.mapRange.linearMap L

omit [Fintype ι] in
@[simp] theorem mapCoeffs_monomial (L : S →ₗ[ℝ] T)
    (d : ι →₀ ℕ) (a : S) :
    mapCoeffs L (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (L a) := by
  change (Finsupp.mapRange.linearMap L) (Finsupp.single d a) = Finsupp.single d (L a)
  simpa only [Finsupp.mapRange.linearMap_apply] using
    (Finsupp.mapRange_single (f := L) (hf := L.map_zero) (a := d) (b := a))

/-- Gaussian expectation commutes with every real-linear coefficient map. -/
theorem expectation_mapCoeffs (L : S →ₗ[ℝ] T)
    (p : MvPolynomial ι S) :
    L (expectation p) = expectation (mapCoeffs L p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      simp only [expectation_monomial, mapCoeffs_monomial]
      rw [show L (a * algebraMap ℝ S (monomialMoment d)) =
        L a * algebraMap ℝ T (monomialMoment d) by
          rw [mul_comm a, ← Algebra.smul_def, map_smul,
            Algebra.smul_def, mul_comm]]
  | add p q hp hq => simp only [map_add, hp, hq]

variable {Ω β : Type*} [MeasurableSpace Ω] [Fintype β]

/-- Evaluation of the compact polynomial variables at real coordinates,
viewed as a real-linear coefficient map. -/
def compactEvalLinear (x : β → ℝ) : MvPolynomial β S →ₗ[ℝ] S :=
  (MvPolynomial.aeval (fun b => algebraMap ℝ S (x b)) :
    MvPolynomial β S →ₐ[S] S).toLinearMap.restrictScalars ℝ

omit [Fintype β] in
@[simp] theorem compactEvalLinear_apply (x : β → ℝ) (p : MvPolynomial β S) :
    compactEvalLinear x p = p.eval (fun b => algebraMap ℝ S (x b)) := by
  rfl

/-- Evaluation of the Gaussian variables as a real-linear coefficient map. -/
def gaussianEvalLinear (t : ι → ℝ) : MvPolynomial ι S →ₗ[ℝ] S :=
  (MvPolynomial.aeval (fun i => algebraMap ℝ S (t i)) :
    MvPolynomial ι S →ₐ[S] S).toLinearMap.restrictScalars ℝ

omit [Fintype ι] in
@[simp] theorem gaussianEvalLinear_apply (t : ι → ℝ) (p : MvPolynomial ι S) :
    gaussianEvalLinear t p = p.eval (fun i => algebraMap ℝ S (t i)) := by
  rfl

omit [Fintype β] in
/-- Compact polynomial averaging also commutes with every real-linear
coefficient map. -/
theorem average_mapCoeffs (μ : MeasureTheory.Measure Ω) (f : Ω → β → ℝ)
    (L : S →ₗ[ℝ] T) (p : MvPolynomial β S) :
    L (average μ f p) = average μ f (mapCoeffs L p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      simp only [average_monomial, mapCoeffs_monomial]
      rw [show L (a * algebraMap ℝ S (CompactPolynomialAverage.monomialMoment μ f d)) =
        L a * algebraMap ℝ T (CompactPolynomialAverage.monomialMoment μ f d) by
          rw [mul_comm a, ← Algebra.smul_def, map_smul,
            Algebra.smul_def, mul_comm]]
  | add p q hp hq => simp only [map_add, hp, hq]

omit [Algebra ℝ S] in
/-- The canonical bivariate polynomial flip exchanges pure bidegree
monomials. -/
theorem commAlgEquiv_monomial_monomial (d : ι →₀ ℕ) (e : β →₀ ℕ) (a : S) :
    MvPolynomial.commAlgEquiv S ι β
      (MvPolynomial.monomial d (MvPolynomial.monomial e a)) =
    MvPolynomial.monomial e (MvPolynomial.monomial d a) := by
  simp [MvPolynomial.monomial_eq, MvPolynomial.commAlgEquiv_C,
    MvPolynomial.commAlgEquiv_X, mul_assoc, mul_comm]

/-- Averaging in the `β` variables is independent of whether Gaussian
variables are represented as coefficients or as the outer variables. -/
theorem mapCoeffs_average_flip (μ : MeasureTheory.Measure Ω) (f : Ω → β → ℝ)
    (p : MvPolynomial ι (MvPolynomial β S)) :
    mapCoeffs ((average μ f : MvPolynomial β S →ₗ[S] S).restrictScalars ℝ) p =
      (average μ f : MvPolynomial β (MvPolynomial ι S) →ₗ[MvPolynomial ι S]
        MvPolynomial ι S) (MvPolynomial.commAlgEquiv S ι β p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      induction a using MvPolynomial.induction_on' with
      | monomial e c =>
          rw [commAlgEquiv_monomial_monomial, mapCoeffs_monomial,
            average_monomial]
          change MvPolynomial.monomial d (average μ f (MvPolynomial.monomial e c)) = _
          rw [average_monomial]
          calc
            MvPolynomial.monomial d
                (c * algebraMap ℝ S (CompactPolynomialAverage.monomialMoment μ f e)) =
                MvPolynomial.C (algebraMap ℝ S
                  (CompactPolynomialAverage.monomialMoment μ f e)) *
                  MvPolynomial.monomial d c := by
              rw [MvPolynomial.C_mul_monomial]
              congr 1
              ring
            _ = _ := mul_comm _ _
      | add a b ha hb =>
          simp only [map_add, ha, hb]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Evaluating Gaussian variables before or after the bivariate flip gives
the same compact polynomial. -/
theorem mapCoeffs_gaussianEval_flip (t : ι → ℝ)
    (p : MvPolynomial ι (MvPolynomial β S)) :
    mapCoeffs (gaussianEvalLinear t : MvPolynomial ι S →ₗ[ℝ] S)
        (MvPolynomial.commAlgEquiv S ι β p) =
      p.eval (fun i => algebraMap ℝ (MvPolynomial β S) (t i)) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      induction a using MvPolynomial.induction_on' with
      | monomial e c =>
          rw [commAlgEquiv_monomial_monomial, mapCoeffs_monomial]
          simp only [gaussianEvalLinear_apply, MvPolynomial.eval_monomial]
          simp only [← map_pow]
          have hprod :
              (d.prod fun i k => algebraMap ℝ (MvPolynomial β S) (t i ^ k)) =
                MvPolynomial.C (d.prod fun i k => algebraMap ℝ S (t i ^ k)) := by
            simp [Finsupp.prod]
          rw [hprod, mul_comm (MvPolynomial.monomial e c)
            (MvPolynomial.C (d.prod fun i k => algebraMap ℝ S (t i ^ k))),
            MvPolynomial.C_mul_monomial]
          congr 1
          ring
      | add a b ha hb => simp only [map_add, ha, hb]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The actual compact coefficient average and finite Gaussian expectation
commute on all bivariate polynomials. -/
theorem average_expectation_comm (μ : MeasureTheory.Measure Ω)
    (f : Ω → β → ℝ) (p : MvPolynomial ι (MvPolynomial β S)) :
    (average μ f : MvPolynomial β S →ₗ[S] S) (expectation p) =
      (expectation : MvPolynomial ι S →ₗ[S] S)
        ((average μ f : MvPolynomial β (MvPolynomial ι S) →ₗ[MvPolynomial ι S]
          MvPolynomial ι S) (MvPolynomial.commAlgEquiv S ι β p)) := by
  calc
    (average μ f : MvPolynomial β S →ₗ[S] S) (expectation p) =
        expectation (mapCoeffs
          ((average μ f : MvPolynomial β S →ₗ[S] S).restrictScalars ℝ) p) :=
      (expectation_mapCoeffs
        ((average μ f : MvPolynomial β S →ₗ[S] S).restrictScalars ℝ) p)
    _ = _ := congrArg expectation (mapCoeffs_average_flip μ f p)

/-- The coefficientwise mixture is an actual iterated Gaussian and compact
integral after every real-linear scalar evaluation. -/
theorem integral_gaussian_then_compact
    [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (f : Ω → β → ℝ) (hf : Continuous f)
    (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι (MvPolynomial β S)) :
    L ((average μ f : MvPolynomial β S →ₗ[S] S) (expectation p)) =
      ∫ ω, (∫ t : ι → ℝ,
        (L.comp (compactEvalLinear (f ω)))
          (p.eval (fun i => algebraMap ℝ (MvPolynomial β S) (t i)))
          ∂GaussianFunctionalPolynomial.standardMeasure) ∂μ := by
  calc
    L ((average μ f : MvPolynomial β S →ₗ[S] S) (expectation p)) =
        ∫ ω, L ((expectation p).eval
          (fun b => algebraMap ℝ S (f ω b))) ∂μ :=
      (CompactPolynomialAverage.integral_evaluation μ f hf L (expectation p)).symm
    _ = _ := by
      congr 1
      funext ω
      have h := GaussianFunctionalPolynomial.integral_polynomial
        (L.comp (compactEvalLinear (f ω))) p
      simpa only [compactEvalLinear_apply] using h.symm

/-- The same scalar mixture with the order of actual integrations reversed.
Together with `integral_gaussian_then_compact`, this proves Fubini for these
finite polynomial integrands without imposing a topology on `S`. -/
theorem integral_compact_then_gaussian
    [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (f : Ω → β → ℝ) (hf : Continuous f)
    (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial ι (MvPolynomial β S)) :
    L ((average μ f : MvPolynomial β S →ₗ[S] S) (expectation p)) =
      ∫ t : ι → ℝ, (∫ ω,
        L ((p.eval (fun i => algebraMap ℝ (MvPolynomial β S) (t i))).eval
          (fun b => algebraMap ℝ S (f ω b))) ∂μ)
        ∂GaussianFunctionalPolynomial.standardMeasure := by
  rw [average_expectation_comm μ f p]
  rw [← GaussianFunctionalPolynomial.integral_polynomial L
    ((average μ f : MvPolynomial β (MvPolynomial ι S) →ₗ[MvPolynomial ι S]
      MvPolynomial ι S) (MvPolynomial.commAlgEquiv S ι β p))]
  congr 1
  funext t
  have hmap := average_mapCoeffs μ f (gaussianEvalLinear t :
    MvPolynomial ι S →ₗ[ℝ] S) (MvPolynomial.commAlgEquiv S ι β p)
  rw [← gaussianEvalLinear_apply, hmap, mapCoeffs_gaussianEval_flip]
  exact (CompactPolynomialAverage.integral_evaluation μ f hf L
    (p.eval (fun i => algebraMap ℝ (MvPolynomial β S) (t i)))).symm

/-- The signed linear Gaussian contraction has precisely the Wick factor
after compact averaging. This remains valid for nilpotent coefficients. -/
theorem averaged_even_wick (μ : MeasureTheory.Measure Ω)
    (f : Ω → β → ℝ) (θ : ι → MvPolynomial β S) (k : ℕ) :
    (expectation : MvPolynomial ι S →ₗ[S] S)
        ((average μ f : MvPolynomial β (MvPolynomial ι S) →ₗ[MvPolynomial ι S]
          MvPolynomial ι S)
          (MvPolynomial.commAlgEquiv S ι β
            (linearPolynomial θ ^ (2 * k)))) =
      (Nat.doubleFactorial (2 * k - 1) : S) *
        (average μ f : MvPolynomial β S →ₗ[S] S)
          ((∑ i, θ i ^ 2) ^ k) := by
  classical
  rw [← average_expectation_comm μ f]
  rw [GaussianUniversalWick.even_moment]
  simpa only [MvPolynomial.smul_eq_C_mul, smul_eq_mul] using
    (average μ f : MvPolynomial β S →ₗ[S] S).map_smul
      (Nat.doubleFactorial (2 * k - 1) : S) ((∑ i, θ i ^ 2) ^ k)

/-- Exact factorial normalization of the compact/Gaussian mixture, including
degree zero. -/
theorem averaged_factorial_wick (μ : MeasureTheory.Measure Ω)
    (f : Ω → β → ℝ) (θ : ι → MvPolynomial β S) (k : ℕ) :
    ((2 ^ k * k.factorial : ℕ) : S) *
      (expectation : MvPolynomial ι S →ₗ[S] S)
        ((average μ f : MvPolynomial β (MvPolynomial ι S) →ₗ[MvPolynomial ι S]
          MvPolynomial ι S)
          (MvPolynomial.commAlgEquiv S ι β
            (linearPolynomial θ ^ (2 * k)))) =
      ((2 * k).factorial : S) *
        (average μ f : MvPolynomial β S →ₗ[S] S)
          ((∑ i, θ i ^ 2) ^ k) := by
  rw [averaged_even_wick]
  rw [← mul_assoc, ← Nat.cast_mul]
  congr 1
  exact congrArg (fun m : ℕ => (m : S))
    (GaussianOrbitalNormalization.factorial_eq_orbital_wick_factor k).symm

end
end QuaternionicSymmetry.GaussianCompactInterchange
