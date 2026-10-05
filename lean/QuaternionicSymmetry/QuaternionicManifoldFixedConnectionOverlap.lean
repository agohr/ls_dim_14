import QuaternionicSymmetry.LocalConnectionConstantConjugation
import QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison

/-! The actual adapted tangent connection overlap in one fixed
quaternionic model. -/

namespace QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap

open scoped Manifold Quaternion ContDiff
open QuaternionicManifoldFixedNormalizer
open ManifoldQuaternionicConnection
open LocalConnectionConstantConjugation
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private def modelOperator (p : M) : E →L[ℝ] E :=
  (modelGauge S (Q.reduction.Q (achart E p))).toContinuousLinearMap

private def modelInverse (p : M) : E →L[ℝ] E :=
  ((modelGauge S (Q.reduction.Q (achart E p))).symm).toContinuousLinearMap

def fixedForm (p : M) : LocalConnection.Form (E := E) (A := E →L[ℝ] E) :=
  transportedForm (modelInverse S Q p) (modelOperator S Q p) (D.form p)

def fixedGauge (p q : M) : E → E →L[ℝ] E :=
  transportedGauge (modelInverse S Q q) (modelOperator S Q p)
    (adaptedGauge Q p q)

def fixedGaugeInv (p q : M) : E → E →L[ℝ] E :=
  transportedGauge (modelInverse S Q p) (modelOperator S Q q)
    (adaptedGaugeInv Q p q)

omit [Nontrivial E] in
theorem fixedForm_apply (p : M) (y u : E) :
    fixedForm S Q D p y u =
      QuaternionicManifoldProjectiveStandardConnection.fixedTangentConjugation
        S Q p (D.form p y u) := by
  rfl

theorem fixedForm_symplectic_commutes (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (a : Fin 3 → ℝ) :
    QuaternionicLieAlgebraProjection.symplecticProjection S
        (fixedForm S Q D p y u) *
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a =
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a *
        QuaternionicLieAlgebraProjection.symplecticProjection S
          (fixedForm S Q D p y u) := by
  let T := Q.reduction.Q (achart E p)
  have hcomm (b : Fin 3 → ℝ) :
      QuaternionicLieAlgebraProjection.symplecticProjection T
        (D.form p y u) *
          VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T b =
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T b *
          QuaternionicLieAlgebraProjection.symplecticProjection T
            (D.form p y u) :=
    ManifoldQuaternionicConnectionSplitting.symplecticConnection_commutes Q D p y u hy b
  rw [fixedForm_apply]
  change QuaternionicLieAlgebraProjection.symplecticProjection S
      (QuaternionicIsometryNormalizer.conjugation (modelGauge S T).symm
        (D.form p y u)) *
        VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a =
    VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S a *
      QuaternionicLieAlgebraProjection.symplecticProjection S
        (QuaternionicIsometryNormalizer.conjugation (modelGauge S T).symm
          (D.form p y u))
  rw [
    QuaternionicManifoldModelProjection.symplecticProjection_modelGauge S T
      (D.form p y u) hcomm]
  exact QuaternionicManifoldModelProjection.modelGauge_symm_conjugation_commutes
    S T _ hcomm a

omit [Nontrivial E] in
theorem fixedGauge_eq_transition (p q : M) (y : E) :
    fixedGauge S Q p q y =
      QuaternionicManifoldSmoothProductLifts.fixedTransitionCLM S Q
        (achart E p) (achart E q) ((extChartAt 𝓘(ℝ, E) p).symm y) := by
  rfl

omit [Nontrivial E] in
theorem fixedGauge_inverse (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    fixedGaugeInv S Q p q y * fixedGauge S Q p q y = 1 ∧
      fixedGauge S Q p q y * fixedGaugeInv S Q p q y = 1 := by
  let P := modelOperator S Q p
  let Pi := modelInverse S Q p
  let R := modelOperator S Q q
  let Ri := modelInverse S Q q
  have hP : P * Pi = 1 ∧ Pi * P = 1 := by
    constructor <;> apply ContinuousLinearMap.ext <;> intro v <;>
      simp [P, Pi, modelOperator, modelInverse]
  have hR : R * Ri = 1 ∧ Ri * R = 1 := by
    constructor <;> apply ContinuousLinearMap.ext <;> intro v <;>
      simp [R, Ri, modelOperator, modelInverse]
  obtain ⟨hg₁, hg₂⟩ := adaptedGauge_inverse Q p q y hy
  change (Pi * adaptedGaugeInv Q p q y * R) *
      (Ri * adaptedGauge Q p q y * P) = 1 ∧
    (Ri * adaptedGauge Q p q y * P) *
      (Pi * adaptedGaugeInv Q p q y * R) = 1
  constructor
  · simp only [mul_assoc, ← mul_assoc R Ri, hR.1, one_mul,
      ← mul_assoc (adaptedGaugeInv Q p q y) (adaptedGauge Q p q y), hg₁,
      one_mul, hP.2]
  · simp only [mul_assoc, ← mul_assoc P Pi, hP.1, one_mul,
      ← mul_assoc (adaptedGauge Q p q y) (adaptedGaugeInv Q p q y), hg₂,
      one_mul, hR.2]

omit [Nontrivial E] in
theorem fixedForm_overlap (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    fixedForm S Q D p y =
      LocalConnectionGauge.transform
        (transportedForm (modelInverse S Q q) (modelOperator S Q q)
          (LocalConnectionCoordinatePullback.pullback (D.form q)
            (chartTransition (I := 𝓘(ℝ, E)) p q)))
        (fixedGauge S Q p q) (fixedGaugeInv S Q p q) y := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := congrArg (fun F : E →L[ℝ] (E →L[ℝ] E) => F u)
    (D.overlap p q y hy)
  change D.form p y u = LocalConnectionGauge.transform
    (LocalConnectionCoordinatePullback.pullback (D.form q)
      (chartTransition (I := 𝓘(ℝ, E)) p q))
    (adaptedGauge Q p q) (adaptedGaugeInv Q p q) y u at hD
  change modelInverse S Q p * D.form p y u * modelOperator S Q p = _
  rw [hD]
  have hQ : modelOperator S Q q * modelInverse S Q q = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [modelOperator, modelInverse]
  simpa only [fixedGauge, fixedGaugeInv] using
    (transform_constant_conjugation
      (LocalConnectionCoordinatePullback.pullback (D.form q)
        (chartTransition (I := 𝓘(ℝ, E)) p q))
      (adaptedGauge Q p q) (adaptedGaugeInv Q p q)
      (modelOperator S Q p) (modelInverse S Q p)
      (modelOperator S Q q) (modelInverse S Q q)
      hQ y u
      ((adaptedGauge_contDiffAt Q p q y hy
        (show (2 : WithTop ℕ∞) ≤ ∞ from (WithTop.coe_le_coe).mpr le_top)).differentiableAt
        (by norm_num)))

omit [Nontrivial E] in
theorem fixedForm_overlap_pullback (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ, E)) p q) :
    fixedForm S Q D p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback (fixedForm S Q D q)
          (chartTransition (I := 𝓘(ℝ, E)) p q))
        (fixedGauge S Q p q) (fixedGaugeInv S Q p q) y := by
  rw [fixedForm_overlap S Q D p q y hy,
    transportedForm_pullback]
  rfl

end
end QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap
