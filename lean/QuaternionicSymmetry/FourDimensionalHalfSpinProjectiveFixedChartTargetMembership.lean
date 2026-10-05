import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTensorDescent

/-! The literal spinor bundle-core transition at an actual total-space point
is exactly the target local-trivialization coordinate. Consequently target
affine-chart membership is inherited from the actual point. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTargetMembership

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinActualTransitionSmooth
  ManifoldQuaternionicReduction
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem spinorCoordChange_localTriv (p q : M)
    (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hq : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) q).source) :
    spinorCoordChange Q (achart ℍ p) (achart ℍ q)
      (z.1, ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2) =
      ((projectiveSpinorCore Q).localTriv (achart ℍ q) z).2 := by
  let Z := projectiveSpinorCore Q
  have hp' : z.1 ∈ Z.baseSet (achart ℍ p) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp
  have hq' : z.1 ∈ Z.baseSet (achart ℍ q) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hq
  rw [Z.localTriv_apply, Z.localTriv_apply]
  change Z.coordChange (achart ℍ p) (achart ℍ q) z.1
      (Z.coordChange (Z.indexAt z.1) (achart ℍ p) z.1 z.2) =
    Z.coordChange (Z.indexAt z.1) (achart ℍ q) z.1 z.2
  exact Z.coordChange_comp (Z.indexAt z.1) (achart ℍ p)
    (achart ℍ q) z.1 ⟨⟨Z.mem_baseSet_at _, hp'⟩, hq'⟩ z.2

theorem spinorCoordChange_target_mem (p q : M) (i j : Fin 2)
    (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hq : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) q).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i)
    (hj : ((projectiveSpinorCore Q).localTriv (achart ℍ q) z).2 ∈
      affineDomain 1 j) :
    spinorCoordChange Q (achart ℍ p) (achart ℍ q)
      ((extChartAt 𝓘(ℝ, ℍ) p).symm
        (fixedProjectiveChart Q p i z).1,
        indexedSourcePoint i (fixedProjectiveChart Q p i z).2) ∈
      affineDomain 1 j := by
  have hbase : (extChartAt 𝓘(ℝ, ℍ) p).symm
      (fixedProjectiveChart Q p i z).1 = z.1 := by
    change (extChartAt 𝓘(ℝ, ℍ) p).symm
      ((extChartAt 𝓘(ℝ, ℍ) p) z.1) = z.1
    exact (extChartAt 𝓘(ℝ, ℍ) p).left_inv hp
  have hfiber : indexedSourcePoint i (fixedProjectiveChart Q p i z).2 =
      ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 := by
    change indexedSourcePoint i
      (((projectiveChart 1 i)
        (((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2)) 0) = _
    exact indexedSourcePoint_chart_left i _ hi
  rw [hbase, hfiber, spinorCoordChange_localTriv Q p q z hp hq]
  exact hj

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTargetMembership
