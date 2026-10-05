import QuaternionicSymmetry.ManifoldQuaternionicIsometryVerticalComplex

/-! Quaternionic complex-structure intertwining on actual base tangent
spaces under a metric-quaternionic isometry. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryBaseComplex

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryTotalHorizontal
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldTwistorLocalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem localTrueCoefficientAction_center
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    localTrueCoefficientAction Q f p p a = coefficientAction Q f p a := by
  unfold localTrueCoefficientAction
  rw [Q.reduction.rankThreeCoordChange_self (achart E p) p
    (mem_chart_source E p),
    Q.reduction.rankThreeCoordChange_self (achart E (f • p)) (f • p)
      (mem_chart_source E (f • p))]

theorem chartBaseComplex_center
    (p : M) (a : coefficientSphere) :
    chartBaseComplex Q p (extChartAt 𝓘(ℝ,E) p p) a =
      localTangentSynth Q (achart E p) p a.1 := by
  unfold chartBaseComplex localTangentSynth baseComplex
  rw [(extChartAt 𝓘(ℝ,E) p).left_inv (mem_extChartAt_source p)]

/-- The actual base differential intertwines the complex structure
determined by each twistor point with that at its lifted image. -/
theorem isometry_mfderiv_intertwines_chartBaseComplex
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) (v : E) :
    let a := coefficientSphereHomeomorph.symm z.2
    let b := coefficientSphereHomeomorph.symm (sphereTotalMap Q f z).2
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1
      (chartBaseComplex Q z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1) a v) =
    chartBaseComplex Q (sphereTotalMap Q f z).1
      (extChartAt 𝓘(ℝ,E) (sphereTotalMap Q f z).1
        (sphereTotalMap Q f z).1) b
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) z.1 v) := by
  dsimp only
  rw [sphereTotalMap_base Q f z,
    chartBaseComplex_center Q z.1,
    chartBaseComplex_center Q (f • z.1),
    ← localRawDerivative_center_eq_mfderiv Q f z.1,
    sphereTotalMap_coefficient Q f z]
  change localRawDerivative Q f z.1 z.1
      (localTangentSynth Q (achart E z.1) z.1
        (coefficientSphereHomeomorph.symm z.2).1 v) =
    localTangentSynth Q (achart E (f • z.1)) (f • z.1)
      (coefficientAction Q f z.1
        (coefficientSphereHomeomorph.symm z.2).1)
      (localRawDerivative Q f z.1 z.1 v)
  rw [← localTrueCoefficientAction_center Q f z.1]
  exact localRawDerivative_intertwines Q f z.1 z.1
    (mem_chart_source E z.1) (mem_chart_source E (f • z.1)) _ v

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryBaseComplex
