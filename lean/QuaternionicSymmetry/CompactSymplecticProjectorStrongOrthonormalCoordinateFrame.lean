import QuaternionicSymmetry.CompactSymplecticProjectorTranslatedOrthonormalFrame
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeDerivativeFrame

/-! In one fixed strong quotient chart, the selected action derivative
transports the actual base orthonormal frame smoothly. Its inverse is
smooth on the same open set. The metric/Q-gluing laws are separate. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongOrthonormalCoordinateFrame

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorBaseOrthonormalCoordinates
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorStrongGaugeSection
open CompactSymplecticProjectorStrongGaugeDerivativeFrame
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open GeneralSmoothLocalSectionSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def baseOrthonormalEuclideanCoordinates
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    EModel q ≃L[ℝ] EModel q :=
  (baseOrthonormalFrame hDesc hImm n d e q g a hq).trans
    (euclideanModelEquiv q)

def localOrthonormalFromFrame
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) : EModel q →L[ℝ] EModel q :=
  (euclideanGaugeDerivative n d e q g a
    (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y).comp
      (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).toContinuousLinearMap

def localOrthonormalToFrame
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) : EModel q →L[ℝ] EModel q :=
  (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).symm.toContinuousLinearMap.comp
    (euclideanGaugeDerivativeInverse n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y)

theorem localOrthonormalFrames_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := g.charts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) ∧
    ContMDiffOn 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) := by
  letI := g.charts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  obtain ⟨hD, hInv⟩ := selected_derivative_and_inverse_smooth
    hLee hDesc hImm n d e q g a hq hn x
  have hF : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).toContinuousLinearMap)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
    contMDiffOn_const
  have hT : ContMDiffOn 𝓘(ℝ, EModel q)
      𝓘(ℝ, EModel q →L[ℝ] EModel q) ∞
      (fun _ : ProjectiveCarrier n =>
        (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).symm.toContinuousLinearMap)
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :=
    contMDiffOn_const
  constructor
  · exact hD.clm_comp hF
  · exact hT.clm_comp hInv

theorem localOrthonormalFrames_inverse
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n)
    (hy : y ∈ strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn x) :
    (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y).comp
      (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y) =
        ContinuousLinearMap.id ℝ (EModel q) ∧
    (localOrthonormalFromFrame hLee hDesc hImm n d e q g a hq hn x y).comp
      (localOrthonormalToFrame hLee hDesc hImm n d e q g a hq hn x y) =
        ContinuousLinearMap.id ℝ (EModel q) := by
  obtain ⟨hDI, hID⟩ := selected_derivative_inverse_pair
    hLee hDesc hImm n d e q g a hq hn x y hy
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    change (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).symm
      ((euclideanGaugeDerivativeInverse n d e q g a
        (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y)
        ((euclideanGaugeDerivative n d e q g a
          (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y)
          ((baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq) v))) = v
    have h := congrArg (fun L : EModel q →L[ℝ] EModel q =>
      L ((baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq) v)) hID
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [h]
    exact (baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).symm_apply_apply v
  · apply ContinuousLinearMap.ext
    intro v
    change (euclideanGaugeDerivative n d e q g a
      (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y)
        ((baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq)
          ((baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).symm
            ((euclideanGaugeDerivativeInverse n d e q g a
              (strongGaugeSection hLee hDesc hImm n d e q g a hq hn x) x y) v))) = v
    rw [(baseOrthonormalEuclideanCoordinates hDesc hImm n d e q g a hq).apply_symm_apply]
    have h := congrArg (fun L : EModel q →L[ℝ] EModel q => L v) hDI
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongOrthonormalCoordinateFrame
