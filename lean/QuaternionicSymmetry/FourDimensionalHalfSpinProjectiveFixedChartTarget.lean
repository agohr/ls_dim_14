import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartLocalTensorSmooth
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth

/-! The true target of each fixed affine projective chart is the real-linear
scalar image of its independent pole-centered atlas target. It is open, and
the explicit chart inverse maps it into the exact fixed-chart source. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTarget

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartAsAtlas
  FourDimensionalHalfSpinProjectiveFixedChartAtlasSource
  FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartPole
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

def fixedChartTarget (p : M) (i : Fin 2) : Set (ℍ × ℂ) :=
  {c | projectiveTangentModelEquiv.symm c ∈
    (extChartAt productModel (chartPole Q p i)).target}

theorem fixedChartTarget_isOpen (p : M) (i : Fin 2) :
    IsOpen (fixedChartTarget Q p i) :=
  (isOpen_extChartAt_target (I := productModel) (x := chartPole Q p i)).preimage
    projectiveTangentModelEquiv.symm.continuous

theorem fixedChart_mem_target (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    fixedProjectiveChart Q p i z ∈ fixedChartTarget Q p i := by
  change projectiveTangentModelEquiv.symm (fixedProjectiveChart Q p i z) ∈
    (extChartAt productModel (chartPole Q p i)).target
  rw [fixedChart_eq_poleAtlas Q p i z]
  simp only [projectiveTangentModelEquiv.symm_apply_apply]
  exact (extChartAt productModel (chartPole Q p i)).map_source
    ((fixedChartSource_eq_poleAtlas_source Q p i) ▸ hz)

theorem fixedChartInv_mem_source (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    fixedProjectiveChartInv Q p i c ∈ fixedChartSource Q p i := by
  rw [fixedChartSource_eq_poleAtlas_source Q p i]
  rw [fixedChartInv_eq_poleAtlas Q p i c]
  exact (extChartAt productModel (chartPole Q p i)).map_target hc

theorem fixedChartInv_right_target (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    fixedProjectiveChart Q p i (fixedProjectiveChartInv Q p i c) = c := by
  rw [fixedChart_eq_poleAtlas Q p i,
    fixedChartInv_eq_poleAtlas Q p i]
  rw [(extChartAt productModel (chartPole Q p i)).right_inv hc]
  exact projectiveTangentModelEquiv.apply_symm_apply c

theorem fixedChartTarget_base (p : M) (i : Fin 2)
    (c : ℍ × ℂ) (hc : c ∈ fixedChartTarget Q p i) :
    c.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).target := by
  let z := fixedProjectiveChartInv Q p i c
  have hz : z ∈ fixedChartSource Q p i := fixedChartInv_mem_source Q p i c hc
  have hbase : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
    have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mp hz.1
    rw [← (projectiveSpinorCore Q).baseSet_at] at hp'
    simpa only [projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
  have heq := fixedChartInv_right_target Q p i c hc
  have hcoord : (fixedProjectiveChart Q p i z).1 =
      (extChartAt 𝓘(ℝ, ℍ) p) z.1 := rfl
  rw [← heq, hcoord]
  exact (extChartAt 𝓘(ℝ, ℍ) p).map_source hbase

theorem fixedChartInv_smoothOn (p : M) (i : Fin 2) :
    ContMDiffOn 𝓘(ℝ, ℍ × ℂ) productModel ∞
      (fixedProjectiveChartInv Q p i) (fixedChartTarget Q p i) := by
  intro c hc
  exact (fixedProjectiveChartInv_smoothAt Q p i c hc).contMDiffWithinAt

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTarget
