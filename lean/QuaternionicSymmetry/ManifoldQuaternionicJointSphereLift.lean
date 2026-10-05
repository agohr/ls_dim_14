import QuaternionicSymmetry.ManifoldQuaternionicJointSphereCoordinate

/-! The genuine twistor sphere lift in two frozen bundle charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointSphereLift

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingAdaptedDerivative
open ManifoldQuaternionicJointSphereCoordinate
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

theorem twistorMap_movingLocalCoordinate
    (f₀ f : QuaternionicIsometries Q) (x₀ : M)
    (z : TwistorSphere Q)
    (hx : projection Q z ∈ (chartAt E x₀).source)
    (hy : f • projection Q z ∈ (chartAt E (f₀ • x₀)).source) :
    (localCoordinate Q (achart E (f₀ • x₀)) (twistorMap Q f z)
      (by simpa only [projection_twistorMap] using hy)).1 =
    movingTrueCoefficientAction Q f₀ x₀
      (localCoordinate Q (achart E x₀) z hx).1 (f,projection Q z) := by
  let x := projection Q z
  let i := achart E x₀
  let j := achart E (f₀ • x₀)
  let a := localCoordinate Q i z hx
  have hz : pointOfLocal Q i x hx a = z :=
    pointOfLocal_localCoordinate Q i z hx
  have hcoord := twistorMap_localCoordinate Q f i j x hx hy a
  change Q.quaternionicRankThreeCore.coordChange
      (Q.quaternionicRankThreeCore.indexAt (f • x)) j (f • x)
      (twistorMap Q f (pointOfLocal Q i x hx a)).1.2 =
    movingTrueCoefficientAction Q f₀ x₀ a.1 (f,x) at hcoord
  rw [hz] at hcoord
  exact hcoord

end
end QuaternionicSymmetry.ManifoldQuaternionicJointSphereLift
