import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartCenter

/-! Every index of the actual strong quotient atlas is precisely the
preferred strong chart at its selected center. This identifies indexed
tangent-core transitions with the point-centered formulas already proved. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartIndex

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeChartCenter
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementCenter
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem strongIndex_eq_preferredChart
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∀ i : atlas (EModel q) (ProjectiveCarrier n),
      i.1 = chartAt (EModel q)
        (strongChartCenter hLee hDesc hImm n d e q g a hq hn i) := by
  letI := euclideanQuotientCharts n d e q g a
  intro i
  have hi := ManifoldChartRefinementCenter.chart_eq_restr
    (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
    (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
    (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn) i
  exact hi

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeChartIndex
