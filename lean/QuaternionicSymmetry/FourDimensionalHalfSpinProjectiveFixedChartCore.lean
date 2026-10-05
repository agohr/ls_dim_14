import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAtlasTensorDescent
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveManifold

/-! Genuine fixed base/CP¹ affine-coordinate maps for the independently
constructed projective-spinor bundle. Their composite transition is the
literal core map, not a newly chosen model transition. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartCore

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinProjectiveAllCoreTensorOverlap
  ComplexProjectiveTopology
  FourDimensionalHalfSpinActualTransitionSmooth
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def fixedProjectiveChart (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) : ℍ × ℂ :=
  ((extChartAt 𝓘(ℝ, ℍ) p) z.1,
    ((projectiveChart 1 i)
      (((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2)) 0)

def fixedProjectiveChartInv (p : M) (i : Fin 2)
    (yz : ℍ × ℂ) : SpinorBundleTotal Q :=
  ((projectiveSpinorCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.symm
    ((extChartAt 𝓘(ℝ, ℍ) p).symm yz.1, indexedSourcePoint i yz.2)

theorem fixedProjectiveChart_transition (p q : M) (i j : Fin 2)
    (y : ℍ) (hy : y ∈ ManifoldQuaternionicConnection.chartOverlap
      (I := 𝓘(ℝ, ℍ)) p q) (z : ℂ) :
    fixedProjectiveChart Q q j (fixedProjectiveChartInv Q p i (y,z)) =
      indexedCoreTransition Q i j p q (y,z) := by
  let Z := projectiveSpinorCore Q
  let x := (extChartAt 𝓘(ℝ, ℍ) p).symm y
  have hp0 : x ∈ (extChartAt 𝓘(ℝ, ℍ) p).source :=
    (extChartAt 𝓘(ℝ, ℍ) p).map_target hy.1
  have hp : x ∈ Z.baseSet (achart ℍ p) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp0
  have hq : x ∈ Z.baseSet (achart ℍ q) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hy.2
  let s := indexedSourcePoint i z
  have hcoord :
      ((Z.localTriv (achart ℍ q))
        ((Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph.symm (x,s))) =
      (x, spinorCoordChange Q (achart ℍ p) (achart ℍ q) (x,s)) := by
    change ((Z.localTriv (achart ℍ q)).toOpenPartialHomeomorph
      ((Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph.symm (x,s))) =
      (x, Z.coordChange (achart ℍ p) (achart ℍ q) x s)
    simp only [Z.localTriv_symm_apply]
    change (x, Z.coordChange (Z.indexAt x) (achart ℍ q) x
      (Z.coordChange (achart ℍ p) (Z.indexAt x) x s)) = _
    congr 1
    exact Z.coordChange_comp (achart ℍ p) (Z.indexAt x) (achart ℍ q) x
      ⟨⟨hp, Z.mem_baseSet_at _⟩, hq⟩ s
  have hbase :
      (fixedProjectiveChartInv Q p i (y,z)).1 = x := by
    change ((Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph.symm
      (x,s)).1 = x
    simp only [Z.localTriv_symm_apply]
  change ((extChartAt 𝓘(ℝ, ℍ) q)
      (fixedProjectiveChartInv Q p i (y,z)).1,
      ((projectiveChart 1 j)
        ((Z.localTriv (achart ℍ q))
          (fixedProjectiveChartInv Q p i (y,z))).2) 0) = _
  rw [hbase]
  have hbase' : (extChartAt 𝓘(ℝ, ℍ) q) x =
      ManifoldQuaternionicConnection.chartTransition
        (I := 𝓘(ℝ, ℍ)) p q y := rfl
  rw [hbase']
  change (ManifoldQuaternionicConnection.chartTransition
      (I := 𝓘(ℝ, ℍ)) p q y,
      ((projectiveChart 1 j)
        ((Z.localTriv (achart ℍ q))
          ((Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph.symm
            (x,s))).2) 0) = _
  rw [hcoord]
  fin_cases i <;> fin_cases j <;>
    rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartCore
