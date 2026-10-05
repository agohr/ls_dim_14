import QuaternionicSymmetry.GeneralImmersionHessianLinearConstraint
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricJet

/-! Ambient real-linear equations valid on all actual projector values
also hold on the chartwise projector Hessian in the strong quotient atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianLinearConstraint

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open CompactSymplecticProjectorOrbitQuotient
open GeneralImmersionHessianLinearConstraint
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_chartHessian_linear_constraint
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x : ProjectiveCarrier n, L (quotientOrbitProjector n x) = 0) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (u v : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      L (fderiv ℝ (fderiv ℝ F) y u v) = 0 := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u v
  let F := quotientOrbitProjector n ∘
    (extChartAt 𝓘(ℝ,EModel q) p).symm
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : ContDiffAt ℝ 2 F y := by
    exact (((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt).of_le
        (by decide)
  exact hessian_linear_constraint F L y u v hF (fun z => hL _)

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianLinearConstraint
