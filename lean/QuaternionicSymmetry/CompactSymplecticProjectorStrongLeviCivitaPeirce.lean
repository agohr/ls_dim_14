import QuaternionicSymmetry.CompactSymplecticProjectorStrongHessianPeirceRange
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartPeirceFixed
import QuaternionicSymmetry.CompactSymplecticProjectorStrongChartMetricJet
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceOrthogonal
import QuaternionicSymmetry.GeneralImmersionLeviCivitaProjectionContinuous
import QuaternionicSymmetry.GeneralImmersionHessianSymmetry
import QuaternionicSymmetry.ProjectorPeirceContinuousProjection
import QuaternionicSymmetry.CompactSymplecticProjectorLeviCivita

/-! The ordinary Levi-Civita Christoffel term of the genuine strong
projector metric is exactly the Peirce tangent component of the actual
ambient projector Hessian. This identifies the Riemannian connection
with the concrete immersed-orbit geometry, not just a bracket model. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaPeirce

open Matrix Manifold Bundle GeneralLeviCivitaSource
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeMetric
open CompactSymplecticProjectorStrongChartMetricPullback
open CompactSymplecticProjectorStrongChartMetricJet
open CompactSymplecticProjectorStrongChartPeirceFixed
open CompactSymplecticProjectorStrongHessianPeirceRange
open CompactSymplecticProjectorPeirceOrthogonal
open CompactSymplecticProjectorAmbientMetric
open GeneralImmersionLeviCivitaProjectionContinuous
open GeneralImmersionHessianSymmetry
open ProjectorPeirceContinuousProjection
open ProjectorPeirceTangentProjection
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff Topology
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem actual_leviCivita_eq_peirce_projected_hessian
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
      (u v : EModel q),
      let F := quotientOrbitProjector n ∘
        (extChartAt 𝓘(ℝ,EModel q) p).symm
      let P := F y
      (fderiv ℝ F y) (D.form p y u v) =
        tangentPart P (fderiv ℝ (fderiv ℝ F) y u v) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  intro D p y hy u v
  let F := quotientOrbitProjector n ∘ (extChartAt 𝓘(ℝ,EModel q) p).symm
  let P : Mat n := F y
  let fD : EModel q →L[ℝ] Mat n := fderiv ℝ F y
  let H : EModel q →L[ℝ] EModel q →L[ℝ] Mat n := fderiv ℝ (fderiv ℝ F) y
  let Γ : EModel q → EModel q → EModel q := fun s t => D.form p y s t
  have hPself : Pᴴ = P := by
    change (quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm y))ᴴ =
      quotientOrbitProjector n ((extChartAt 𝓘(ℝ,EModel q) p).symm y)
    induction ((extChartAt 𝓘(ℝ,EModel q) p).symm y) using Quotient.inductionOn' with
    | _ z => exact orbitProjector_selfAdjoint n z
  have hpos : ∀ Z : Mat n, frobeniusCLM n Z Z = 0 → Z = 0 := by
    intro Z hZ
    exact (frobeniusPairing_self_eq_zero_iff n Z).mp (by simpa using hZ)
  have hproj : ∀ s t : EModel q, ∃ w : EModel q,
      tangentPartCLM n P (H s t) = fD w := by
    intro s t
    obtain ⟨w, hw⟩ := actual_chartHessian_peircePart_in_derivative_range
      hLee hDesc hImm n d e q g a hq hn p y hy s t
    exact ⟨w, hw.symm⟩
  have hfix : ∀ w : EModel q, tangentPartCLM n P (fD w) = fD w := by
    intro w
    exact actual_chartDerivative_peirce_fixed
      hLee hDesc hImm n d e q g a hq hn p y hy w
  have hadjoint : ∀ Z W : Mat n,
      frobeniusCLM n (tangentPartCLM n P Z) W =
      frobeniusCLM n Z (tangentPartCLM n P W) := by
    intro Z W
    exact tangentPart_frobenius_selfAdjoint n P Z W hPself
  have hΓ : ∀ s t : EModel q, Γ s t = Γ t s := by
    intro s t
    exact D.torsion p y s t hy
  have hσ : ContMDiffAt 𝓘(ℝ,EModel q) 𝓘(ℝ,EModel q) ∞
      (extChartAt 𝓘(ℝ,EModel q) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hF : ContDiffAt ℝ 2 F y :=
    (((smooth_quotientOrbitProjector_strongGauge
      hLee hDesc hImm n d e q g a hq hn).contMDiffAt.comp y hσ).contDiffAt).of_le
        (by decide)
  have hH : ∀ s t : EModel q, H s t = H t s := by
    intro s t
    exact hessian_symmetric F y s t hF
  have hmetric : ∀ s t w : EModel q,
      frobeniusCLM n (H s t) (fD w) + frobeniusCLM n (fD t) (H s w) =
        frobeniusCLM n (fD (Γ s t)) (fD w) +
          frobeniusCLM n (fD t) (fD (Γ s w)) := by
    intro s t w
    have hm := D.metric p y s t w hy
    rw [actual_chartMetric_first_jet_eq_projector_hessian
      hLee hDesc hImm n d e q g a hq hn p y hy s t w,
      actual_chartMetric_eq_frobenius_chart_derivatives
        hLee hDesc hImm n d e q g a hq hn p y hy (Γ s t) w,
      actual_chartMetric_eq_frobenius_chart_derivatives
        hLee hDesc hImm n d e q g a hq hn p y hy t (Γ s w)] at hm
    exact hm
  have hsymm : ∀ Z W : Mat n, frobeniusCLM n Z W = frobeniusCLM n W Z :=
    frobeniusCLM_symm n
  simpa only [Γ, fD, H, P, F, tangentPartCLM_apply] using
    projected_christoffel_eq_second_derivative_on_hessian
    fD (tangentPartCLM n P) (frobeniusCLM n) Γ
    (fun s t => H s t) hpos hproj hfix hadjoint hΓ hH hmetric hsymm u v

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongLeviCivitaPeirce
