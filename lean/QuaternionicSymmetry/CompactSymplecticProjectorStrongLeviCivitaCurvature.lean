import QuaternionicSymmetry.GeneralImmersionProjectionCurvatureLocal
import QuaternionicSymmetry.CompactSymplecticProjectorStrongPeirceField
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartPeirceFixed
import QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaPeirce
import QuaternionicSymmetry.LocalConnection

/-! The curvature of the actual ordinary Levi-Civita connection of the
projector metric is the commutator of derivatives of the genuine Peirce
projection field. No model-curvature conclusion is supplied as a premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaCurvature

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongLeviCivitaPeirce
open CompactSymplecticProjectorStrongChartPeirceFixed
open CompactSymplecticProjectorStrongPeirceField
open GeneralImmersionProjectionCurvatureLocal
open ProjectorPeirceContinuousProjection
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_leviCivita_curvature_eq_peirce_derivative_commutator
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
    ∀ (D : CoordinateLeviCivitaConnection
        (smoothProjectorMetric_strongGauge hLee hDesc hImm n d e q g a hq hn))
      (p : ProjectiveCarrier n) (y : EModel q)
      (hy : y ∈ (extChartAt 𝓘(ℝ,EModel q) p).target)
      (u v w : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let proj := fun z => tangentPartCLM n (F z)
      (fderiv ℝ F y)
        (LocalConnection.curvature (D.form p) y u v w) =
          (fderiv ℝ proj y u) ((fderiv ℝ proj y v) (fderiv ℝ F y w)) -
            (fderiv ℝ proj y v) ((fderiv ℝ proj y u) (fderiv ℝ F y w)) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v w
  letI : NormedSpace ℝ (Mat n) := inferInstance
  letI : NormedSpace ℝ (Mat n →L[ℝ] Mat n) := inferInstance
  letI : NormedAlgebra ℝ (EModel q →L[ℝ] EModel q) := inferInstance
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let proj := fun z => tangentPartCLM n (F z)
  let Γ := D.form p
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hf : ContDiffAt ℝ 3 F y :=
    (((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt).of_le
        (by decide)
  have hπ : DifferentiableAt ℝ proj y :=
    actual_peirceField_differentiableAt hLee hDesc hImm n d e q g a hq hn p y hy
  have hΓ : DifferentiableAt ℝ Γ y :=
    ((D.smooth_form p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hy))
      |>.differentiableAt (by simp)
  have hGauss : ∀ᶠ z in 𝓝 y, ∀ s t : EModel q,
      fderiv ℝ F z (Γ z s t) = proj z (fderiv ℝ (fderiv ℝ F) z s t) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz s t
    exact actual_leviCivita_eq_peirce_projected_hessian
      hLee hDesc hImm n d e q g a hq hn D p z hz s t
  have hfix : ∀ᶠ z in 𝓝 y, ∀ t : EModel q,
      proj z (fderiv ℝ F z t) = fderiv ℝ F z t := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz t
    exact actual_chartDerivative_peirce_fixed
      hLee hDesc hImm n d e q g a hq hn p z hz t
  have hcurv := projection_curvature_formula_local F proj Γ y u v w
    hf hπ hΓ hGauss hfix
  change (fderiv ℝ F y)
      (LocalConnection.curvature Γ y u v w) = _
  simp only [LocalConnection.curvature_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, map_sub, map_add]
  simp only [map_sub, map_add] at hcurv
  abel_nf at hcurv ⊢
  exact hcurv

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaCurvature
