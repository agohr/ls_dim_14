import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePartialChart
import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! A charted space on the independently topologized native negative-Hodge
sphere, using the actual native two-form local trivializations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereCharted

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance

def nativeSphereChartAt (p : NativeSphereBundleTotal Q) :
    OpenPartialHomeomorph (NativeSphereBundleTotal Q) (M × geometricSphere) :=
  nativeSpherePartialChart Q hdim (Q.frames.adaptedCore.indexAt p.1.1)
    ⟨p,Q.frames.adaptedCore.mem_baseSet_at _⟩

theorem nativeSphereChartAt_source (p : NativeSphereBundleTotal Q) :
    p ∈ (nativeSphereChartAt Q hdim p).source := by
  rw [nativeSphereChartAt, nativeSpherePartialChart_source]
  exact Q.frames.adaptedCore.mem_baseSet_at _

instance nativeSphereChartedSpace :
    ChartedSpace (M × geometricSphere) (NativeSphereBundleTotal Q) where
  atlas := Set.range (nativeSphereChartAt Q hdim)
  chartAt := nativeSphereChartAt Q hdim
  mem_chart_source := nativeSphereChartAt_source Q hdim
  chart_mem_atlas := fun p => ⟨p,rfl⟩

instance nativeSphereModelChartedSpace :
    ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (NativeSphereBundleTotal Q) := by
  letI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
    ⟨by simp [EuclideanThree]⟩
  letI := nativeSphereChartedSpace Q hdim
  exact ChartedSpace.comp (ModelProd E (EuclideanSpace ℝ (Fin 2)))
    (M × geometricSphere) (NativeSphereBundleTotal Q)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereCharted
