import QuaternionicSymmetry.ManifoldQuaternionicLocalSphereActionSmooth
import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! Preferred geometric-sphere bundle trivializations are smooth charts for
the genuine smooth twistor sphere total space. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicSphereChartSmooth

open ManifoldTwistorSphereCore
open ManifoldTwistorSphereManifold
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
open ManifoldQuaternionicMetric
open Filter
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

/-- At its preferred base chart, the genuine bundle trivialization is a
smooth map from the twistor total space to the base–sphere product. -/
theorem preferredLocalTriv_smoothAt (z : SphereBundleTotal Q) :
    ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (fun w : SphereBundleTotal Q =>
        (sphereCore Q).localTriv ((sphereCore Q).indexAt z.1) w) z := by
  let Z := sphereCore Q
  let i := Z.indexAt z.1
  have hz : z ∈ (Z.localTriv i).source :=
    (Z.mem_localTriv_source i z).2 (Z.mem_baseSet_at z.1)
  rw [contMDiffAt_iff]
  refine ⟨(Z.localTriv i).continuousOn.continuousAt
    ((Z.localTriv i).open_source.mem_nhds hz), ?_⟩
  apply contDiffWithinAt_id.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin
      (I := J (E := E)) z] with y hy
    change writtenInExtChartAt (J (E := E)) (J (E := E)) z
      (chartAt (M × geometricSphere) z) y = y
    exact writtenInExtChartAt_chartAt_comp z hy
  · exact writtenInExtChartAt_chartAt_comp z
      ((extChartAt (J (E := E)) z).map_source
        (mem_extChartAt_source z))

/-- The inverse preferred trivialization is smooth at the coordinate of its
center. -/
theorem preferredLocalTriv_symm_smoothAt (z : SphereBundleTotal Q) :
    ContMDiffAt (J (E := E)) (J (E := E)) ∞
      (chartAt (M × geometricSphere) z).symm
      (chartAt (M × geometricSphere) z z) := by
  let Z := sphereCore Q
  have hz : z ∈ (Z.localTriv (Z.indexAt z.1)).source :=
    (Z.mem_localTriv_source (Z.indexAt z.1) z).2 (Z.mem_baseSet_at z.1)
  have ht : (Z.localTriv (Z.indexAt z.1) z) ∈
      (chartAt (M × geometricSphere) z).target :=
    (chartAt (M × geometricSphere) z).map_source hz
  rw [contMDiffAt_iff]
  refine ⟨(chartAt (M × geometricSphere) z).continuousOn_symm.continuousAt
    ((chartAt (M × geometricSphere) z).open_target.mem_nhds ht), ?_⟩
  have hcoord :
      (extChartAt (J (E := E)) (chartAt (M × geometricSphere) z z))
        (chartAt (M × geometricSphere) z z) =
      (extChartAt (J (E := E)) z) z := by
    simp only [extChartAt, chartAt_comp, prodChartedSpace_chartAt, mfld_simps]
  have htarget : (extChartAt (J (E := E)) z).target ∈
      nhdsWithin
        ((extChartAt (J (E := E)) (chartAt (M × geometricSphere) z z))
          (chartAt (M × geometricSphere) z z))
        (Set.range (J (E := E))) := by
    rw [hcoord]
    exact extChartAt_target_mem_nhdsWithin z
  apply contDiffWithinAt_id.congr_of_eventuallyEq
  · filter_upwards [htarget] with y hy
    exact writtenInExtChartAt_chartAt_symm_comp z hy
  · have hy : (extChartAt (J (E := E)) z z) ∈
        (extChartAt (J (E := E)) z).target :=
      (extChartAt (J (E := E)) z).map_source (mem_extChartAt_source z)
    rw [hcoord]
    exact writtenInExtChartAt_chartAt_symm_comp z hy

end
end QuaternionicSymmetry.ManifoldQuaternionicSphereChartSmooth
