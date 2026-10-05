import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveSmoothCoordinate

/-! Smoothness of the global fiberwise Hopf map between the two independently
smooth associated total spaces. The chart expression is the genuine product
of the identity base map and the explicit CP¹-to-round-sphere diffeomorphism. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleSmooth

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveBundleHomeomorphism
  FourDimensionalHalfSpinProjectiveForwardContinuous
  FourDimensionalHalfSpinProjectiveSmoothCoordinate
  FourDimensionalHalfSpinProjective
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev sourceModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev targetModel := 𝓘(ℝ, ℍ).prod (𝓡 2)

theorem spinorToSphere_contMDiff :
    ContMDiff sourceModel targetModel ∞ (spinorToSphere Q) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(spinorSphereHomeomorph Q).continuous.continuousAt, ?_⟩
  have hprod := (productHopf_contMDiff (M := M))
    ((chartAt (M × ProjectiveSpinor) p) p)
  rw [contMDiffAt_iff] at hprod
  apply hprod.2.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := sourceModel) p]
      with v hv
    let z := (extChartAt sourceModel p).symm v
    have hzfull : z ∈ (chartAt (ModelProd ℍ (Fin 1 → ℂ)) p).source := by
      simpa only [z, extChartAt_source] using
        (extChartAt sourceModel p).map_target hv
    have hz : z ∈ (chartAt (M × ProjectiveSpinor) p).source := by
      simpa only [chartAt_comp, OpenPartialHomeomorph.trans_source] using hzfull.1
    have hchart := product_chart_hopf Q p z hz
    have harg : (chartAt (M × ProjectiveSpinor) p) z =
        (extChartAt sourceModel ((chartAt (M × ProjectiveSpinor) p) p)).symm v := by
      have hv' : v ∈ ((chartAt (M × ProjectiveSpinor) p).toPartialEquiv ≫
          extChartAt sourceModel ((chartAt (M × ProjectiveSpinor) p) p)).target := by
        simpa only [extChartAt_comp] using hv
      rw [PartialEquiv.trans_target] at hv'
      simpa only [z, extChartAt_comp, PartialEquiv.coe_trans_symm,
        Function.comp_apply] using
        (chartAt (M × ProjectiveSpinor) p).right_inv hv'.2
    have hcenter := product_chart_hopf Q p p (mem_chart_source _ p)
    change (extChartAt targetModel
        ((chartAt (M × geometricSphere) (spinorToSphere Q p)) (spinorToSphere Q p)))
        ((chartAt (M × geometricSphere) (spinorToSphere Q p))
        (spinorToSphere Q z)) =
      (extChartAt targetModel
        (productHopf ((chartAt (M × ProjectiveSpinor) p) p)))
        (productHopf ((extChartAt sourceModel
          ((chartAt (M × ProjectiveSpinor) p) p)).symm v))
    rw [← harg, ← hchart, ← hcenter]
  · have hchart := product_chart_hopf Q p p (mem_chart_source _ p)
    let u := (chartAt (M × ProjectiveSpinor) p) p
    have hp : p ∈ (extChartAt sourceModel p).source := by
      simp only [extChartAt_source, mem_chart_source]
    have hu : u ∈ (extChartAt sourceModel u).source := by
      simp only [extChartAt_source, mem_chart_source]
    change (extChartAt targetModel (spinorToSphere Q p))
        (spinorToSphere Q ((extChartAt sourceModel p).symm
          ((extChartAt sourceModel p) p))) =
      (extChartAt targetModel (productHopf u))
        (productHopf ((extChartAt sourceModel u).symm
          ((extChartAt sourceModel u) u)))
    rw [(extChartAt sourceModel p).left_inv hp,
      (extChartAt sourceModel u).left_inv hu]
    rw [extChartAt_comp]
    change (extChartAt targetModel
        ((chartAt (M × geometricSphere) (spinorToSphere Q p)) (spinorToSphere Q p)))
        ((chartAt (M × geometricSphere) (spinorToSphere Q p)) (spinorToSphere Q p)) =
      (extChartAt targetModel (productHopf u)) (productHopf u)
    rw [hchart]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleSmooth
