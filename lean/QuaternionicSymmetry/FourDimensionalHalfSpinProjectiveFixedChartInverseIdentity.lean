import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartCore
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative

/-! The explicit inverse of each actual fixed projective affine chart is a
right inverse on its true base-chart target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseIdentity

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectivePreferredSecondPoint
  ComplexProjectiveTopology
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

theorem indexedSourcePoint_chart (i : Fin 2) (z : ℂ) :
    ((projectiveChart 1 i) (indexedSourcePoint i z)) 0 = z := by
  fin_cases i
  · change ((projectiveChart 1 0)
      (FourDimensionalHalfSpinProjectiveMobiusAction.affineSpinorPoint z)) 0 = z
    rw [affineSpinorPoint_eq_projectiveChart]
    rw [(projectiveChart 1 0).right_inv]
    · rfl
    · rw [projectiveChart_target]
      trivial
  · change ((projectiveChart 1 1)
      ((projectiveChart 1 1).symm ![z])) 0 = z
    rw [(projectiveChart 1 1).right_inv]
    · rfl
    · rw [projectiveChart_target]
      trivial

theorem fixedProjectiveChartInv_right (p : M) (i : Fin 2)
    (y : ℍ) (hy : y ∈ (extChartAt 𝓘(ℝ, ℍ) p).target) (z : ℂ) :
    fixedProjectiveChart Q p i
      (fixedProjectiveChartInv Q p i (y,z)) = (y,z) := by
  let Z := projectiveSpinorCore Q
  let L := (Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph
  let x := (extChartAt 𝓘(ℝ, ℍ) p).symm y
  let s := indexedSourcePoint i z
  have hp0 : x ∈ (extChartAt 𝓘(ℝ, ℍ) p).source :=
    (extChartAt 𝓘(ℝ, ℍ) p).map_target hy
  have hp : x ∈ Z.baseSet (achart ℍ p) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp0
  have htarget : (x,s) ∈ L.target :=
    (Z.mem_localTriv_target (achart ℍ p) (x,s)).mpr hp
  have hbase : (L.symm (x,s)).1 = x :=
    (Z.localTriv (achart ℍ p)).proj_symm_apply htarget
  have hright := L.right_inv htarget
  change ((extChartAt 𝓘(ℝ, ℍ) p) (L.symm (x,s)).1,
    ((projectiveChart 1 i) (L (L.symm (x,s))).2) 0) = (y,z)
  rw [hbase, hright, (extChartAt 𝓘(ℝ, ℍ) p).right_inv hy]
  exact Prod.ext rfl (indexedSourcePoint_chart i z)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseIdentity
