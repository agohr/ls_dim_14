import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeFrame

/-! The one selected quotient section gives a smooth action-derived change of
frame and its inverse on the same fixed strong Euclidean chart. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeFrame

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorLocalQuaternionicFrameSmooth
open CompactSymplecticProjectorLocalDerivativeInverseSmooth
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorActualSmoothSectionFrame
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeSmoothTransport
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

def euclideanGaugeDerivative
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → CompactSymplecticHaar.Group (n + 1))
    (x y : ProjectiveCarrier n) : EModel q →L[ℝ] EModel q :=
  (euclideanModelEquiv q).toContinuousLinearMap.comp
    ((gaugeDerivativeCoordinates n d e q g a σ x y).comp
      (euclideanModelEquiv q).symm.toContinuousLinearMap)

def euclideanGaugeDerivativeInverse
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (σ : ProjectiveCarrier n → CompactSymplecticHaar.Group (n + 1))
    (x y : ProjectiveCarrier n) : EModel q →L[ℝ] EModel q :=
  (euclideanModelEquiv q).toContinuousLinearMap.comp
    ((ContinuousLinearMap.inverse (gaugeDerivativeCoordinates n d e q g a σ x y)).comp
      (euclideanModelEquiv q).symm.toContinuousLinearMap)

theorem selected_derivative_and_inverse_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (euclideanGaugeDerivative n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) ∧
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (euclideanGaugeDerivativeInverse n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
  let W := strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  rcases hSpec with ⟨_, _, _, _, hD, hInv, _, _⟩
  have hD' : ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (gaugeDerivativeCoordinates n d e q g a σ x) W :=
    hD.mono Set.inter_subset_right
  have hInv' : ContMDiffOn 𝓘(ℝ, RModel q)
      𝓘(ℝ, RModel q →L[ℝ] RModel q) ∞
      (fun y => ContinuousLinearMap.inverse
        (gaugeDerivativeCoordinates n d e q g a σ x y)) W :=
    hInv.mono Set.inter_subset_right
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  have hL : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, RModel q →L[ℝ] EModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).toContinuousLinearMap) W := contMDiffOn_const
  have hR : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, EModel q →L[ℝ] RModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (euclideanModelEquiv q).symm.toContinuousLinearMap) W := contMDiffOn_const
  constructor
  · exact (hL.clm_comp (contMDiffOn_strongGauge_of_original hLee hDesc hImm
      n d e q g a hq hn _ W hD')).clm_comp hR
  · exact (hL.clm_comp (contMDiffOn_strongGauge_of_original hLee hDesc hImm
      n d e q g a hq hn _ W hInv')).clm_comp hR

/-- The two selected smooth fields are inverse changes of coordinates on
the very same strong chart; invertibility is inherited from the actual
derivative of the transitive action, not an extra frame assumption. -/
theorem selected_derivative_inverse_pair
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    let σ := strongGaugeSection hLee hDesc hImm n d e q g a hq hn x
    (euclideanGaugeDerivative n d e q g a σ x y).comp
      (euclideanGaugeDerivativeInverse n d e q g a σ x y) =
        ContinuousLinearMap.id ℝ (EModel q) ∧
    (euclideanGaugeDerivativeInverse n d e q g a σ x y).comp
      (euclideanGaugeDerivative n d e q g a σ x y) =
        ContinuousLinearMap.id ℝ (EModel q) := by
  letI := g.charts
  letI := g.manifold
  letI := a.quotientCharts
  letI := a.quotientManifold
  have hSpec := Classical.choose_spec ((Classical.choose_spec
    (actualQuotientPlane_has_local_smooth_section_frame hLee hDesc hImm
      n d e q g a hq hn x)).2.2)
  rcases hSpec with ⟨_, _, _, hInv, _, _, _, _⟩
  obtain ⟨T, hT⟩ := hInv y hy.2
  change (T : RModel q →L[ℝ] RModel q) =
    gaugeDerivativeCoordinates n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y at hT
  constructor <;> ext v <;>
    simp only [euclideanGaugeDerivative, euclideanGaugeDerivativeInverse,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] <;>
    rw [← hT, ContinuousLinearMap.inverse_equiv] <;>
    simp

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeFrame
