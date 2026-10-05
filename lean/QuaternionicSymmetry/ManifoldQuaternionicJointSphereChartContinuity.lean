import QuaternionicSymmetry.ManifoldQuaternionicJointMovingCoefficientContinuity
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! Joint continuity of the actual twistor lift's local sphere coefficient. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointSphereChartContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingAdaptedDerivative
open ManifoldQuaternionicJointMovingCoefficientContinuity
open ManifoldQuaternionicJointSphereBundleBridge
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicTwistorLocalAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuousAt_sphereChartCoefficient
    (i : atlas E M) (z₀ : SphereBundleTotal Q)
    (hi : z₀.1 ∈ (sphereCore Q).baseSet i) :
    ContinuousAt (sphereChartCoefficient Q i) z₀ := by
  have hz : z₀ ∈ ((sphereCore Q).localTriv i).source :=
    ((sphereCore Q).mem_localTriv_source i z₀).2 hi
  have htriv : ContinuousAt ((sphereCore Q).localTriv i) z₀ :=
    ((sphereCore Q).localTriv i).continuousOn.continuousAt
      (((sphereCore Q).localTriv i).open_source.mem_nhds hz)
  exact (continuous_subtype_val.comp
    ((coefficientSphereHomeomorph.symm.continuous).comp continuous_snd)).continuousAt.comp
      (f := (sphereCore Q).localTriv i) (x := z₀) htriv

/-- At every actual isometry and twistor point, the output coefficient in
one fixed target sphere chart varies jointly continuously. -/
theorem continuousAt_jointSphereChartCoefficient
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q) :
    ContinuousAt (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereChartCoefficient Q (achart E (f₀ • z₀.1))
        (sphereTotalMap Q p.1 p.2)) (f₀,z₀) := by
  let i := achart E z₀.1
  let j := achart E (f₀ • z₀.1)
  let a₀ := sphereChartCoefficient Q i z₀
  have hi : z₀.1 ∈ (sphereCore Q).baseSet i :=
    (sphereCore Q).mem_baseSet_at z₀.1
  have hcoord : ContinuousAt (sphereChartCoefficient Q i) z₀ :=
    continuousAt_sphereChartCoefficient Q i z₀ hi
  have hbase : ContinuousAt (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      p.2.1) (f₀,z₀) :=
    ((sphereCore Q).continuous_proj.comp continuous_snd).continuousAt
  have hinput : ContinuousAt
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        ((p.1,p.2.1),sphereChartCoefficient Q i p.2)) (f₀,z₀) := by
    exact (continuousAt_fst.prodMk hbase).prodMk
      (hcoord.comp (f := Prod.snd) (x := (f₀,z₀)) continuousAt_snd)
  have hrot := (continuousAt_movingCoefficientRotation_joint Q hR3 f₀ z₀.1 a₀).comp
    (f := fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      ((p.1,p.2.1),sphereChartCoefficient Q i p.2))
    (x := (f₀,z₀)) hinput
  have hsource : ∀ᶠ p : QuaternionicIsometries Q × SphereBundleTotal Q in nhds (f₀,z₀),
      p.2.1 ∈ (chartAt E z₀.1).source := by
    exact ((chartAt E z₀.1).open_source.preimage
      ((sphereCore Q).continuous_proj.comp continuous_snd)).mem_nhds
        (mem_chart_source E z₀.1)
  have htarget : ∀ᶠ p : QuaternionicIsometries Q × SphereBundleTotal Q in nhds (f₀,z₀),
      p.1 • p.2.1 ∈ (chartAt E (f₀ • z₀.1)).source := by
    have haction : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        p.1 • p.2.1) :=
      (continuous_action Q).comp
        (continuous_fst.prodMk ((sphereCore Q).continuous_proj.comp continuous_snd))
    exact ((chartAt E (f₀ • z₀.1)).open_source.preimage haction).mem_nhds
      (mem_chart_source E (f₀ • z₀.1))
  apply hrot.congr_of_eventuallyEq
  filter_upwards [hsource, htarget] with p hs ht
  exact sphereChartCoefficient_movingLift Q f₀ p.1 z₀.1 p.2 hs ht

end
end QuaternionicSymmetry.ManifoldQuaternionicJointSphereChartContinuity
