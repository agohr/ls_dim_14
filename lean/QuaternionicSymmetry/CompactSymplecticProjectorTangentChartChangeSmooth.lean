import QuaternionicSymmetry.CompactSymplecticProjectorLocalQuaternionicPlaneChart

/-! Smooth dependence of the actual quotient tangent-chart transition
operator on the overlap of two preferred charts. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTangentChartChangeSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem tangentCoordChange_smoothOn
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (tangentCoordChange 𝓘(ℝ, RModel q) x y)
      ((chartAt (RModel q) x).source ∩ (chartAt (RModel q) y).source) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : IsManifold 𝓘(ℝ, RModel q) 1 (ProjectiveCarrier n) :=
    a.quotientManifold.of_le (by simp)
  letI : IsManifold 𝓘(ℝ, RModel q) (∞ + 1) (ProjectiveCarrier n) := by
    simpa using a.quotientManifold
  letI : (tangentBundleCore 𝓘(ℝ, RModel q) (ProjectiveCarrier n)).IsContMDiff
      𝓘(ℝ, RModel q) ∞ := tangentBundleCore.isContMDiff
  exact (tangentBundleCore 𝓘(ℝ, RModel q) (ProjectiveCarrier n)).contMDiffOn_coordChange
    𝓘(ℝ, RModel q) (achart (RModel q) x) (achart (RModel q) y)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTangentChartChangeSmooth
