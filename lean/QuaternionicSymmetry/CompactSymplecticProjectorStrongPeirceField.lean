import QuaternionicSymmetry.ProjectorPeirceContinuousSmooth
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceDerivative
import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaPeirce

/-! The genuine Peirce projection is a C¹ operator-valued field in every
strong quotient chart, with explicit derivative from the actual projector
immersion. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPeirceField

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorPeirceDerivative
open ProjectorPeirceContinuousProjection
open ProjectorPeirceContinuousSmooth
open ProjectorPeirceTangentProjection
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_peirceField_differentiableAt
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target),
      DifferentiableAt ℝ
        (fun z => tangentPartCLM n
          (quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm z))) y := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedSpace ℝ (Mat n →L[ℝ] Mat n) := inferInstance
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : DifferentiableAt ℝ
      (quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm) y :=
    ((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt
      |>.differentiableAt (by simp)
  exact (tangentPartCLM_differentiableAt n _).comp y hF

theorem actual_peirceField_derivative_apply
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ∀ (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (u : EModel q) (A : Mat n),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let π := fun z => tangentPartCLM n (F z)
      let X := fderiv ℝ F y u
      (fderiv ℝ π y u) A =
        X * A + A * X - 2 • (X * A * F y + F y * A * X) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro p y hy u A
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedSpace ℝ (Mat n →L[ℝ] Mat n) := inferInstance
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let π := fun z => tangentPartCLM n (F z)
  have hπ : DifferentiableAt ℝ π y :=
    actual_peirceField_differentiableAt hLee hDesc hImm n d e q g a hq hn p y hy
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : DifferentiableAt ℝ F y :=
    ((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt
      |>.differentiableAt (by simp)
  have hPart : DifferentiableAt ℝ (fun B : Mat n => tangentPart B A) (F y) := by
    simpa only [tangentPartCLM_apply] using
      (tangentPartCLM_differentiableAt n (F y)).clm_apply
        (differentiableAt_const A)
  have hCLM := fderiv_clm_apply hπ (differentiableAt_const A)
  change fderiv ℝ (fun z => tangentPart (F z) A) y = _ at hCLM
  have hCLMu := congrArg (fun L : EModel q →L[ℝ] Mat n => L u) hCLM
  simp at hCLMu
  have hcomp := fderiv_comp y hPart hF
  change fderiv ℝ (fun z => tangentPart (F z) A) y = _ at hcomp
  have hu := congrArg (fun L : EModel q →L[ℝ] Mat n => L u) hcomp
  simp only [ContinuousLinearMap.comp_apply] at hu
  rw [fderiv_tangentPart n (F y) A (fderiv ℝ F y u)] at hu
  change ((fderiv ℝ π y) u) A =
    (fderiv ℝ F y u) * A + A * (fderiv ℝ F y u) -
      2 • ((fderiv ℝ F y u) * A * F y + F y * A * (fderiv ℝ F y u))
  rw [← hCLMu]
  exact hu

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPeirceField
