import QuaternionicSymmetry.ManifoldQuaternionicJointSphereChartContinuity

/-! Joint continuity of the derivative-induced action on the actual
quaternionic twistor sphere bundle. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointSphereChartContinuity
open ManifoldQuaternionicTwistorLocalAction
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldRiemannianIsometryLieInput
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open Topology
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuousAt_jointSphereTotalMap
    (hR3 : IsometryLieSource.{0,0})
    (f₀ : QuaternionicIsometries Q) (z₀ : SphereBundleTotal Q) :
    ContinuousAt (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2) (f₀,z₀) := by
  let j := achart E (f₀ • z₀.1)
  let w₀ := sphereTotalMap Q f₀ z₀
  have hcoeff := continuousAt_jointSphereChartCoefficient Q hR3 f₀ z₀
  have hemb : IsEmbedding (fun u : geometricSphere =>
      (coefficientSphereHomeomorph.symm u).1) :=
    IsEmbedding.subtypeVal.comp coefficientSphereHomeomorph.symm.isEmbedding
  have hsecond : ContinuousAt
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        ((sphereCore Q).localTriv j (sphereTotalMap Q p.1 p.2)).2)
      (f₀,z₀) := by
    apply hemb.isInducing.continuousAt_iff.mpr
    change ContinuousAt (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereChartCoefficient Q j (sphereTotalMap Q p.1 p.2)) (f₀,z₀)
    exact hcoeff
  have hinput : Continuous
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        (p.1,p.2.1)) :=
    continuous_fst.prodMk ((sphereCore Q).continuous_proj.comp continuous_snd)
  have hbase : ContinuousAt
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        p.1 • p.2.1) (f₀,z₀) :=
    ((continuous_action Q).comp hinput).continuousAt
  have hlocal : ContinuousAt
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        (sphereCore Q).localTriv j (sphereTotalMap Q p.1 p.2)) (f₀,z₀) := by
    convert hbase.prodMk hsecond using 1
  have hw : w₀ ∈ ((sphereCore Q).localTriv j).source := by
    apply ((sphereCore Q).mem_localTriv_source j w₀).2
    simpa only [w₀, sphereTotalMap_base] using
      (sphereCore Q).mem_baseSet_at (f₀ • z₀.1)
  have hsymm : ContinuousAt ((sphereCore Q).localTriv j).invFun
      ((sphereCore Q).localTriv j w₀) :=
    ((sphereCore Q).localTriv j).continuousOn_invFun.continuousAt
      (((sphereCore Q).localTriv j).open_target.mem_nhds
        (((sphereCore Q).localTriv j).map_source hw))
  have hcomp := hsymm.comp
    (f := fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      (sphereCore Q).localTriv j (sphereTotalMap Q p.1 p.2))
    (x := (f₀,z₀)) hlocal
  apply hcomp.congr_of_eventuallyEq
  have htarget : ∀ᶠ p : QuaternionicIsometries Q × SphereBundleTotal Q
      in nhds (f₀,z₀), p.1 • p.2.1 ∈ (sphereCore Q).baseSet j :=
    ((sphereCore Q).isOpen_baseSet j |>.preimage
      ((continuous_action Q).comp hinput)).mem_nhds
        ((sphereCore Q).mem_baseSet_at (f₀ • z₀.1))
  filter_upwards [htarget] with p hp
  have hmem : sphereTotalMap Q p.1 p.2 ∈
      ((sphereCore Q).localTriv j).source :=
    ((sphereCore Q).mem_localTriv_source j _).2
      (by simpa only [sphereTotalMap_base] using hp)
  exact (((sphereCore Q).localTriv j).left_inv hmem).symm

theorem continuous_jointSphereTotalMap (hR3 : IsometryLieSource.{0,0}) :
    Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2) :=
  continuous_iff_continuousAt.mpr (fun p => continuousAt_jointSphereTotalMap Q hR3 p.1 p.2)

end
end QuaternionicSymmetry.ManifoldQuaternionicJointSphereContinuity
