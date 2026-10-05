import QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartInvolution
import QuaternionicSymmetry.GeneralSmoothInvolutionDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTotalHorizontal

/-! The actual strong-chart reflection derivative at a nearby reflected
point is the inverse of its derivative at the original point, derived by
differentiating the checked local involution. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse

open Filter Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongQuaternionicHermitianTangent
open CompactSymplecticProjectorStrongQuaternionicPointIsometry
open CompactSymplecticProjectorStrongSymmetryChartInvolution
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryChartFields
open GeneralSmoothInvolutionDerivative
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem actual_pointSymmetry_chart_derivative_inverse_eventually
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
    let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
    let F := localIsometryChartMap Q f x
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,EModel q) x x),
      (fderiv ℝ F (F y)).comp (fderiv ℝ F y) =
        ContinuousLinearMap.id ℝ (EModel q) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  letI : Nontrivial (EModel q) := inferInstance
  let Q := strongQuaternionicHermitianTangent hLee hDesc hImm n d e q g a hq hn
  let f := pointSymmetryQuaternionicIsometry hLee hDesc hImm n d e q g a hq hn x
  let y₀ := extChartAt 𝓘(ℝ,EModel q) x x
  let F := localIsometryChartMap Q f x
  have hfix : f • x = x := by
    change pointSymmetry n x x = x
    exact pointSymmetry_fixed n x
  have hcenter : F y₀ = y₀ := by
    change localIsometryChartMap Q f x (extChartAt 𝓘(ℝ,EModel q) x x) = y₀
    rw [ManifoldQuaternionicIsometryTotalHorizontal.localIsometryChartMap_center Q f x,
      hfix]
  have hF : ContDiffAt ℝ 1 F y₀ :=
    (localIsometryChartMap_contDiffAt_center Q f x).of_le (by norm_num)
  exact derivative_comp_of_eventual_involution F y₀ hF hcenter
    (actual_pointSymmetry_chart_involutive_eventually
      hLee hDesc hImm n d e q g a hq hn x)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongSymmetryChartDerivativeInverse
