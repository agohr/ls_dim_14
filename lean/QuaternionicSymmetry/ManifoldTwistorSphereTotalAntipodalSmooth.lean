import QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalContinuous
import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! Smoothness of the genuine total-space sphere antipode in the
independently constructed twistor sphere atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalSmooth

open scoped Manifold ContDiff
open ManifoldTwistorSphereBundle ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere
  ManifoldQuaternionicTwistorAntipodalWeight
  ManifoldTwistorSphereAntipodalDerivative
  ManifoldTwistorSphereTotalAntipodalChart
  ManifoldTwistorSphereTotalAntipodalContinuous
  ManifoldTwistorSphereManifold

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

def productAntipodal (p : M × geometricSphere) : M × geometricSphere :=
  (p.1, geometricAntipodal p.2)

theorem productAntipodal_smooth :
    ContMDiff (productModel (E := E)) (productModel (E := E)) ∞
      (productAntipodal (M := M)) := by
  exact contMDiff_fst.prodMk
    (geometricAntipodal_smooth.comp contMDiff_snd)

theorem chart_sphereAntipodal (p q : SphereBundleTotal Q)
    (hq : q ∈ (chartAt (M × geometricSphere) p).source) :
    (chartAt (M × geometricSphere) (sphereAntipodal Q p))
      (sphereAntipodal Q q) =
        productAntipodal ((chartAt (M × geometricSphere) p) q) := by
  rw [FiberBundle.chartedSpace'_chartAt,
    FiberBundle.chartedSpace'_chartAt]
  let Z := sphereCore Q
  have hi : q.1 ∈ Z.baseSet (Z.indexAt p.1) := by
    simpa only [FiberBundle.chartedSpace'_chartAt] using hq
  apply Prod.ext
  · rfl
  · exact congrArg Prod.snd
      (sphereAntipodal_localTriv Q (Z.indexAt p.1) q hi)

theorem sphereAntipodal_contMDiff :
    ContMDiff (productModel (E := E)) (productModel (E := E)) ∞
      (sphereAntipodal Q) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(sphereAntipodal_continuous Q).continuousAt, ?_⟩
  have hprod := (productAntipodal_smooth (E := E) (M := M))
    ((chartAt (M × geometricSphere) p) p)
  rw [contMDiffAt_iff] at hprod
  apply hprod.2.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := productModel) p]
      with v hv
    let z := (extChartAt productModel p).symm v
    have hzfull : z ∈
        (chartAt (ModelProd E (EuclideanSpace ℝ (Fin 2))) p).source := by
      simpa only [z, extChartAt_source] using
        (extChartAt productModel p).map_target hv
    have hz : z ∈ (chartAt (M × geometricSphere) p).source := by
      simpa only [chartAt_comp, OpenPartialHomeomorph.trans_source] using hzfull.1
    have hchart := chart_sphereAntipodal Q p z hz
    have harg : (chartAt (M × geometricSphere) p) z =
        (extChartAt productModel ((chartAt (M × geometricSphere) p) p)).symm v := by
      have hv' : v ∈ ((chartAt (M × geometricSphere) p).toPartialEquiv ≫
          extChartAt productModel ((chartAt (M × geometricSphere) p) p)).target := by
        simpa only [extChartAt_comp] using hv
      rw [PartialEquiv.trans_target] at hv'
      simpa only [z, extChartAt_comp, PartialEquiv.coe_trans_symm,
        Function.comp_apply] using
        (chartAt (M × geometricSphere) p).right_inv hv'.2
    have hcenter := chart_sphereAntipodal Q p p (mem_chart_source _ p)
    change (extChartAt productModel
        ((chartAt (M × geometricSphere) (sphereAntipodal Q p))
          (sphereAntipodal Q p)))
        ((chartAt (M × geometricSphere) (sphereAntipodal Q p))
          (sphereAntipodal Q z)) =
      (extChartAt productModel
        (productAntipodal ((chartAt (M × geometricSphere) p) p)))
        (productAntipodal ((extChartAt productModel
          ((chartAt (M × geometricSphere) p) p)).symm v))
    rw [← harg, ← hchart, ← hcenter]
  · have hchart := chart_sphereAntipodal Q p p (mem_chart_source _ p)
    let u := (chartAt (M × geometricSphere) p) p
    have hp : p ∈ (extChartAt (productModel (E := E)) p).source := by
      simp only [extChartAt_source, mem_chart_source]
    have hu : u ∈ (extChartAt (productModel (E := E)) u).source := by
      simp only [extChartAt_source, mem_chart_source]
    change (extChartAt productModel (sphereAntipodal Q p))
        (sphereAntipodal Q ((extChartAt productModel p).symm
          ((extChartAt productModel p) p))) =
      (extChartAt productModel (productAntipodal u))
        (productAntipodal ((extChartAt productModel u).symm
          ((extChartAt productModel u) u)))
    rw [(extChartAt productModel p).left_inv hp,
      (extChartAt productModel u).left_inv hu]
    rw [extChartAt_comp]
    change (extChartAt productModel
        ((chartAt (M × geometricSphere) (sphereAntipodal Q p))
          (sphereAntipodal Q p)))
        ((chartAt (M × geometricSphere) (sphereAntipodal Q p))
          (sphereAntipodal Q p)) =
      (extChartAt productModel (productAntipodal u))
        (productAntipodal u)
    rw [hchart]

end
end QuaternionicSymmetry.ManifoldTwistorSphereTotalAntipodalSmooth
