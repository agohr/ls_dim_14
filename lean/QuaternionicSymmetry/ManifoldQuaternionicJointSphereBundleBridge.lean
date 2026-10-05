import QuaternionicSymmetry.ManifoldQuaternionicJointSphereLift

/-! Value-level bridge between the genuine sphere-bundle chart and the
original quaternionic unit-sphere chart. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointSphereBundleBridge
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingAdaptedDerivative
open ManifoldQuaternionicJointSphereCoordinate
open ManifoldQuaternionicJointSphereLift
open ManifoldQuaternionicTwistorLocalAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- An arbitrary point-level lift of the actual twistor map has the
jointly continuous frozen-frame coefficient on the two-chart overlap. -/
theorem sphereChartCoefficient_of_movingLift
    (f₀ f : QuaternionicIsometries Q) (x₀ : M)
    (z w : SphereBundleTotal Q)
    (hx : z.1 ∈ (chartAt E x₀).source)
    (hy : f • z.1 ∈ (chartAt E (f₀ • x₀)).source)
    (hw : w.1 ∈ (sphereCore Q).baseSet (achart E (f₀ • x₀)))
    (hbase : w.1 = f • z.1)
    (horig : toOriginalSphere Q w =
      twistorMap Q f (toOriginalSphere Q z)) :
    sphereChartCoefficient Q (achart E (f₀ • x₀)) w =
      movingCoefficientRotation Q f₀ x₀
        (sphereChartCoefficient Q (achart E x₀) z) (f,z.1) := by
  rw [sphereChartCoefficient_eq_localCoordinate Q (achart E (f₀ • x₀)) w hw,
    sphereChartCoefficient_eq_localCoordinate Q (achart E x₀) z hx]
  change Q.quaternionicRankThreeCore.coordChange
    (Q.quaternionicRankThreeCore.indexAt w.1)
      (achart E (f₀ • x₀)) w.1
      (toOriginalSphere Q w).1.2 = _
  rw [hbase, horig]
  rw [movingCoefficientRotation_eq_true_on_overlap Q f₀ f x₀ z.1 hx hy]
  exact twistorMap_movingLocalCoordinate Q f₀ f x₀ (toOriginalSphere Q z) hx hy

/-- The actual sphere-bundle lift, not just an abstract point-level lift,
has this two-fixed-chart formula. -/
theorem sphereChartCoefficient_movingLift
    (f₀ f : QuaternionicIsometries Q) (x₀ : M)
    (z : SphereBundleTotal Q)
    (hx : z.1 ∈ (chartAt E x₀).source)
    (hy : f • z.1 ∈ (chartAt E (f₀ • x₀)).source) :
    sphereChartCoefficient Q (achart E (f₀ • x₀))
      (sphereTotalMap Q f z) =
      movingCoefficientRotation Q f₀ x₀
        (sphereChartCoefficient Q (achart E x₀) z) (f,z.1) :=
  sphereChartCoefficient_of_movingLift Q f₀ f x₀ z (sphereTotalMap Q f z)
    hx hy
    (by simpa only [sphereTotalMap_base] using hy)
    (sphereTotalMap_base Q f z)
    (toOriginal_sphereTotalMap Q f z)

end
end QuaternionicSymmetry.ManifoldQuaternionicJointSphereBundleBridge
