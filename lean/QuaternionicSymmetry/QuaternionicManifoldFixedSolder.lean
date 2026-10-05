import QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap
import QuaternionicSymmetry.ManifoldTwistorLocalComplexSmoothness

/-! The actual solder form in one fixed quaternionic model, with smoothness
and covariance including the derivative of the base chart transition. -/
namespace QuaternionicSymmetry.QuaternionicManifoldFixedSolder
open QuaternionicManifoldFixedNormalizer QuaternionicManifoldFixedConnectionOverlap
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def fixedSolder (p : M) (y : E) : E →L[ℝ] E :=
  (modelGauge S (Q.reduction.Q (achart E p))).symm.toContinuousLinearMap.comp
    (solder Q p y)

omit [Nontrivial E] in
theorem fixedSolder_smooth (p : M) :
    ContDiffOn ℝ ∞ (fixedSolder S Q p) (extChartAt 𝓘(ℝ,E) p).target := by
  have hs : ContDiffOn ℝ ∞ (solder Q p) (extChartAt 𝓘(ℝ,E) p).target :=
    (ManifoldTwistorGlobalAlmostComplex.frameTo_chart_smooth Q p).congr
      (fun y hy => solder_eq_toFrame Q p y hy)
  exact contDiffOn_const.clm_comp hs

omit [Nontrivial E] in
theorem fixedSolder_chartTransition (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    (fixedSolder S Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)).comp
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y) =
      (fixedGauge S Q p q y).comp (fixedSolder S Q p y) := by
  apply ContinuousLinearMap.ext
  intro u
  have hs := congrArg (fun T : E →L[ℝ] E => T u)
    (solder_chartTransition Q p q y hy)
  change (modelGauge S (Q.reduction.Q (achart E q))).symm
      (solder Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)) =
    (modelGauge S (Q.reduction.Q (achart E q))).symm
      (adaptedGauge Q p q y ((modelGauge S (Q.reduction.Q (achart E p)))
        ((modelGauge S (Q.reduction.Q (achart E p))).symm (solder Q p y u))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (modelGauge S (Q.reduction.Q (achart E q))).symm hs

end
end QuaternionicSymmetry.QuaternionicManifoldFixedSolder
