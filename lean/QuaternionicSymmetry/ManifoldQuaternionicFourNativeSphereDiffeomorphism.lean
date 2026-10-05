import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePreferredChart
import QuaternionicSymmetry.ManifoldChartCompatibleSmooth

/-! The independently smooth native negative-Hodge sphere and the genuine
associated quaternionic twistor sphere have the same smooth charts under the
fiberwise two-form identification. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphism

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereBundleSmoothCoordinate
open ManifoldQuaternionicFourNativeSpherePreferredChart
open ManifoldQuaternionicFourNativeSphereCharted
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldQuaternionicFourNativeSphereSmoothAtlas
open ManifoldChartCompatibleSmooth
open ManifoldTwistorSphereCore
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

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

theorem preferred_model_chart_compatible (z w : SphereBundleTotal Q)
    (hw : w ∈ (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2))) z).source) :
    letI := nativeSphereModelChartedSpace Q hdim
    (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (associatedToNativeHomeomorph Q hdim z))
      (associatedToNativeHomeomorph Q hdim w) =
        (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2))) z) w := by
  letI := nativeSphereChartedSpace Q hdim
  letI := nativeSphereModelChartedSpace Q hdim
  have hw' : w ∈ (chartAt (M × geometricSphere) z).source := by
    simpa only [chartAt_comp, OpenPartialHomeomorph.trans_source] using hw.1
  have hz' := preferred_chart_compatible Q hdim z z (mem_chart_source _ z)
  have hw'' := preferred_chart_compatible Q hdim z w hw'
  simp only [chartAt_comp, OpenPartialHomeomorph.trans_apply]
  rw [hz', hw'']

/-- The global fiberwise two-form identification is smooth from the actual
associated twistor sphere to the independently smooth native Hodge sphere. -/
theorem associatedToNative_contMDiff :
    letI := nativeSphereModelChartedSpace Q hdim
    ContMDiff (productModel (E := E)) (productModel (E := E)) ∞
      (associatedToNativeHomeomorph Q hdim) := by
  letI := nativeSphereModelChartedSpace Q hdim
  letI : IsManifold (productModel (E := E)) ∞
      (NativeSphereBundleTotal Q) := nativeSphere_isManifold Q hdim
  apply homeomorph_contMDiff_of_chart_compatible
    (I := productModel (E := E))
  intro z w hw
  exact preferred_model_chart_compatible Q hdim z w hw

theorem preferred_product_chart_source_iff (z w : SphereBundleTotal Q) :
    letI := nativeSphereChartedSpace Q hdim
    w ∈ (chartAt (M × geometricSphere) z).source ↔
      associatedToNativeHomeomorph Q hdim w ∈
        (chartAt (M × geometricSphere)
          (associatedToNativeHomeomorph Q hdim z)).source := by
  letI := nativeSphereChartedSpace Q hdim
  rw [FiberBundle.chartedSpace'_chartAt]
  change w.1 ∈ (sphereCore Q).baseSet ((sphereCore Q).indexAt z.1) ↔
    (associatedToNativeHomeomorph Q hdim w) ∈
      (nativeSphereChartAt Q hdim (associatedToNativeHomeomorph Q hdim z)).source
  rw [nativeSphereChartAt, nativeSpherePartialChart_source]
  rfl

theorem preferred_model_chart_source_iff (z w : SphereBundleTotal Q) :
    letI := nativeSphereModelChartedSpace Q hdim
    w ∈ (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2))) z).source ↔
      associatedToNativeHomeomorph Q hdim w ∈
        (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2)))
          (associatedToNativeHomeomorph Q hdim z)).source := by
  letI := nativeSphereChartedSpace Q hdim
  letI := nativeSphereModelChartedSpace Q hdim
  simp only [chartAt_comp, OpenPartialHomeomorph.trans_source,
    Set.mem_inter_iff, Set.mem_preimage]
  have hbase := preferred_product_chart_source_iff Q hdim z w
  have hcenter := preferred_chart_compatible Q hdim z z (mem_chart_source _ z)
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · exact hbase.mp hw.1
    · have hcoord := preferred_chart_compatible Q hdim z w hw.1
      simpa only [hcenter, hcoord] using hw.2
  · intro hw
    refine ⟨?_, ?_⟩
    · exact hbase.mpr hw.1
    · have hw' := hbase.mpr hw.1
      have hcoord := preferred_chart_compatible Q hdim z w hw'
      simpa only [hcenter, hcoord] using hw.2

/-- The inverse of the global form identification is smooth as well. -/
theorem associatedToNative_symm_contMDiff :
    letI := nativeSphereModelChartedSpace Q hdim
    ContMDiff (productModel (E := E)) (productModel (E := E)) ∞
      (associatedToNativeHomeomorph Q hdim).symm := by
  letI := nativeSphereModelChartedSpace Q hdim
  letI : IsManifold (productModel (E := E)) ∞
      (NativeSphereBundleTotal Q) := nativeSphere_isManifold Q hdim
  apply homeomorph_contMDiff_of_chart_compatible
    (I := productModel (E := E))
  intro y v hv
  let z := (associatedToNativeHomeomorph Q hdim).symm y
  let w := (associatedToNativeHomeomorph Q hdim).symm v
  have hz : associatedToNativeHomeomorph Q hdim z = y :=
    (associatedToNativeHomeomorph Q hdim).right_inv y
  have hw : associatedToNativeHomeomorph Q hdim w = v :=
    (associatedToNativeHomeomorph Q hdim).right_inv v
  have hsource : w ∈
      (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2))) z).source :=
    (preferred_model_chart_source_iff Q hdim z w).mpr (by simpa [hz,hw] using hv)
  have h := preferred_model_chart_compatible Q hdim z w hsource
  simpa only [z, w, hz, hw] using h.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereDiffeomorphism
