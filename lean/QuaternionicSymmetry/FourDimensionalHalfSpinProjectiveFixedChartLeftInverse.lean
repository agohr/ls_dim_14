import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseIdentity

/-! A fixed projective chart and its explicit inverse agree on their genuine
base and affine-fiber source, not merely at a preferred chart center. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLeftInverse

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjective
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

theorem indexedSourcePoint_chart_left (i : Fin 2)
    (s : ProjectiveSpinor) (hs : s ∈ affineDomain 1 i) :
    indexedSourcePoint i (((projectiveChart 1 i) s) 0) = s := by
  fin_cases i
  · change FourDimensionalHalfSpinProjectiveMobiusAction.affineSpinorPoint
        (((projectiveChart 1 0) s) 0) = s
    rw [affineSpinorPoint_eq_projectiveChart]
    have hc : ![((projectiveChart 1 0) s) 0] =
        (projectiveChart 1 0) s := by
      funext j
      fin_cases j
      rfl
    rw [hc]
    exact (projectiveChart 1 0).left_inv (by simpa [projectiveChart_source] using hs)
  · change (projectiveChart 1 1).symm
        ![((projectiveChart 1 1) s) 0] = s
    have hc : ![((projectiveChart 1 1) s) 0] =
        (projectiveChart 1 1) s := by
      funext j
      fin_cases j
      rfl
    rw [hc]
    exact (projectiveChart 1 1).left_inv (by simpa [projectiveChart_source] using hs)

theorem fixedProjectiveChartInv_left (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i) :
    fixedProjectiveChartInv Q p i (fixedProjectiveChart Q p i z) = z := by
  let Z := projectiveSpinorCore Q
  let L := (Z.localTriv (achart ℍ p)).toOpenPartialHomeomorph
  have hp' : z.1 ∈ Z.baseSet (achart ℍ p) := by
    simpa only [Z, projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp
  have hsource : z ∈ L.source :=
    (Z.mem_localTriv_source (achart ℍ p) z).mpr hp'
  have hbase : (extChartAt 𝓘(ℝ, ℍ) p).symm
      ((extChartAt 𝓘(ℝ, ℍ) p) z.1) = z.1 :=
    (extChartAt 𝓘(ℝ, ℍ) p).left_inv hp
  have hfiber := indexedSourcePoint_chart_left i (L z).2 hi
  change L.symm
    ((extChartAt 𝓘(ℝ, ℍ) p).symm
      ((extChartAt 𝓘(ℝ, ℍ) p) z.1),
      indexedSourcePoint i (((projectiveChart 1 i) (L z).2) 0)) = z
  rw [hbase, hfiber]
  have hproj : (L z).1 = z.1 := by
    change ((Z.localTriv (achart ℍ p)) z).1 = z.1
    rw [Z.localTriv_apply]
  rw [← hproj]
  exact L.left_inv hsource

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
