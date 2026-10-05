import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The vertical block of a product tangent coordinate transition. -/
namespace QuaternionicSymmetry.ProdTangentCoordChange
open scoped Manifold ContDiff
noncomputable section

variable {V E G M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem coordChange_prod_inr (g₀ g : G) (x₀ x : M) (v : E)
    (hg : g ∈ (chartAt V g₀).source)
    (hx : x ∈ (chartAt E x₀).source) :
    (tangentBundleCore (𝓘(ℝ,V).prod 𝓘(ℝ,E)) (G × M)).coordChange
      (achart (ModelProd V E) (g₀,x₀))
      (achart (ModelProd V E) (g,x)) (g,x) (0,v) =
      (0, (tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E x₀) (achart E x) x v) := by
  have hgsource : (extChartAt 𝓘(ℝ,V) g₀) g ∈
      ((extChartAt 𝓘(ℝ,V) g₀).symm ≫ extChartAt 𝓘(ℝ,V) g).source := by
    simp [ext_coord_change_source, hg]
  have hxsource : (extChartAt 𝓘(ℝ,E) x₀) x ∈
      ((extChartAt 𝓘(ℝ,E) x₀).symm ≫ extChartAt 𝓘(ℝ,E) x).source := by
    simp [ext_coord_change_source, hx]
  have hdG : DifferentiableAt ℝ
      (fun t : V => (extChartAt 𝓘(ℝ,V) g)
        ((extChartAt 𝓘(ℝ,V) g₀).symm t))
      ((extChartAt 𝓘(ℝ,V) g₀) g) := by
    have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ,V))
      (n := ∞) g g₀ hgsource
    simpa only [modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using h.differentiableWithinAt (by simp)
  have hdM : DifferentiableAt ℝ
      (fun t : E => (extChartAt 𝓘(ℝ,E) x)
        ((extChartAt 𝓘(ℝ,E) x₀).symm t))
      ((extChartAt 𝓘(ℝ,E) x₀) x) := by
    have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℝ,E))
      (n := ∞) x x₀ hxsource
    simpa only [modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using h.differentiableWithinAt (by simp)
  simp only [tangentBundleCore_coordChange_achart, extChartAt_prod,
    PartialEquiv.prod_coe_symm, PartialEquiv.prod_coe,
    ModelWithCorners.range_prod, Function.comp_def]
  simp only [modelWithCornersSelf_coe, Set.range_id, Set.univ_prod_univ,
    fderivWithin_univ]
  have hprod := (hdG.hasFDerivAt.prodMap
    (p := ((extChartAt 𝓘(ℝ,V) g₀) g, (extChartAt 𝓘(ℝ,E) x₀) x))
    hdM.hasFDerivAt).fderiv
  have happ := congrArg
    (fun T : (V × E) →L[ℝ] (V × E) => T (0,v)) hprod
  simpa [Prod.map_apply] using happ

end
end QuaternionicSymmetry.ProdTangentCoordChange
