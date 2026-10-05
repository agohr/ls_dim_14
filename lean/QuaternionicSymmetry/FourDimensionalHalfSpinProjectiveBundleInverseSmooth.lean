import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleSmooth

/-! Smoothness of the inverse of the fiberwise Hopf homeomorphism, using
the independent smooth atlases on both associated bundles. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleInverseSmooth

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveBundleEquiv
  FourDimensionalHalfSpinProjectiveBundleHomeomorphism
  FourDimensionalHalfSpinProjectiveInverseContinuous
  FourDimensionalHalfSpinProjectiveSmoothCoordinate
  FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfDiffeomorph
  FourDimensionalHalfSpinHopfDiffeomorphPackage
  ManifoldTwistorSphereCore
  ManifoldTwistorCoefficientSphere

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev sourceModel := 𝓘(ℝ, ℍ).prod (𝓡 2)
private abbrev targetModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

def productHopfInverse (p : M × geometricSphere) : M × ProjectiveSpinor :=
  (p.1, projectiveHopfGeometricHomeomorph.symm p.2)

theorem productHopfInverse_contMDiff :
    ContMDiff sourceModel targetModel ∞ (productHopfInverse (M := M)) := by
  have hfst : ContMDiff sourceModel 𝓘(ℝ, ℍ) ∞
      (fun p : M × geometricSphere => p.1) := contMDiff_fst
  have hsnd : ContMDiff sourceModel (𝓘(ℝ, Fin 1 → ℂ)) ∞
      (fun p : M × geometricSphere => projectiveHopfGeometricHomeomorph.symm p.2) :=
    projectiveHopfGeometricDiffeomorph.contMDiff_invFun.comp contMDiff_snd
  exact hfst.prodMk hsnd

theorem product_chart_inverse_hopf (p q : SphereBundleTotal Q)
    (hq : q ∈ (chartAt (M × geometricSphere) p).source) :
    (chartAt (M × ProjectiveSpinor) (sphereToSpinor Q p))
      (sphereToSpinor Q q) =
      productHopfInverse ((chartAt (M × geometricSphere) p) q) := by
  rw [FiberBundle.chartedSpace'_chartAt,
    FiberBundle.chartedSpace'_chartAt]
  let Zs := sphereCore Q
  let Zp := projectiveSpinorCore Q
  have hi : q.1 ∈ Zs.baseSet (Zs.indexAt p.1) := by
    simpa only [FiberBundle.chartedSpace'_chartAt] using hq
  apply Prod.ext
  · rfl
  · simpa only [productHopfInverse, Zs, Zp] using
      (localTriv_inverse_hopf Q (Zs.indexAt p.1) q hi)

theorem sphereToSpinor_contMDiff :
    ContMDiff sourceModel targetModel ∞ (sphereToSpinor Q) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(spinorSphereHomeomorph Q).symm.continuous.continuousAt, ?_⟩
  have hprod := (productHopfInverse_contMDiff (M := M))
    ((chartAt (M × geometricSphere) p) p)
  rw [contMDiffAt_iff] at hprod
  apply hprod.2.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := sourceModel) p]
      with v hv
    let z := (extChartAt sourceModel p).symm v
    have hzfull : z ∈ (chartAt (ModelProd ℍ (EuclideanSpace ℝ (Fin 2))) p).source := by
      simpa only [z, extChartAt_source] using
        (extChartAt sourceModel p).map_target hv
    have hz : z ∈ (chartAt (M × geometricSphere) p).source := by
      simpa only [chartAt_comp, OpenPartialHomeomorph.trans_source] using hzfull.1
    have hchart := product_chart_inverse_hopf Q p z hz
    have harg : (chartAt (M × geometricSphere) p) z =
        (extChartAt sourceModel ((chartAt (M × geometricSphere) p) p)).symm v := by
      have hv' : v ∈ ((chartAt (M × geometricSphere) p).toPartialEquiv ≫
          extChartAt sourceModel ((chartAt (M × geometricSphere) p) p)).target := by
        simpa only [extChartAt_comp] using hv
      rw [PartialEquiv.trans_target] at hv'
      simpa only [z, extChartAt_comp, PartialEquiv.coe_trans_symm,
        Function.comp_apply] using
        (chartAt (M × geometricSphere) p).right_inv hv'.2
    have hcenter := product_chart_inverse_hopf Q p p (mem_chart_source _ p)
    change (extChartAt targetModel
        ((chartAt (M × ProjectiveSpinor) (sphereToSpinor Q p)) (sphereToSpinor Q p)))
        ((chartAt (M × ProjectiveSpinor) (sphereToSpinor Q p))
          (sphereToSpinor Q z)) =
      (extChartAt targetModel
        (productHopfInverse ((chartAt (M × geometricSphere) p) p)))
        (productHopfInverse ((extChartAt sourceModel
          ((chartAt (M × geometricSphere) p) p)).symm v))
    rw [← harg, ← hchart, ← hcenter]
  · have hchart := product_chart_inverse_hopf Q p p (mem_chart_source _ p)
    let u := (chartAt (M × geometricSphere) p) p
    have hp : p ∈ (extChartAt sourceModel p).source := by
      simp only [extChartAt_source, mem_chart_source]
    have hu : u ∈ (extChartAt sourceModel u).source := by
      simp only [extChartAt_source, mem_chart_source]
    change (extChartAt targetModel (sphereToSpinor Q p))
        (sphereToSpinor Q ((extChartAt sourceModel p).symm
          ((extChartAt sourceModel p) p))) =
      (extChartAt targetModel (productHopfInverse u))
        (productHopfInverse ((extChartAt sourceModel u).symm
          ((extChartAt sourceModel u) u)))
    rw [(extChartAt sourceModel p).left_inv hp,
      (extChartAt sourceModel u).left_inv hu]
    rw [extChartAt_comp]
    change (extChartAt targetModel
        ((chartAt (M × ProjectiveSpinor) (sphereToSpinor Q p)) (sphereToSpinor Q p)))
        ((chartAt (M × ProjectiveSpinor) (sphereToSpinor Q p)) (sphereToSpinor Q p)) =
      (extChartAt targetModel (productHopfInverse u)) (productHopfInverse u)
    rw [hchart]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveBundleInverseSmooth
