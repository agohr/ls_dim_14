import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanModel
import QuaternionicSymmetry.CompactSymplecticProjectorEuclideanChartBridge
import QuaternionicSymmetry.CompactSymplecticProjectorStrongGaugeAtlas
import QuaternionicSymmetry.ManifoldChartRefinementDiffeomorph

/-! A genuine identity diffeomorphism from the original real-coordinate
quotient atlas to the strong Euclidean self-model atlas. Each intermediate
charted-space dictionary is fixed explicitly. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorEuclideanCharts
open CompactSymplecticProjectorEuclideanChartBridge
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldChartRefinementDiffeomorph
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)


def oldToStrongDiffeomorph
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    @Diffeomorph ℝ _ (RModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _
      𝓘(ℝ, RModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ a.quotientCharts
      (ProjectiveCarrier n) _
      (strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn) ∞ := by
  letI := a.quotientCharts
  let oldCharts := a.quotientCharts
  let selfCharts := euclideanQuotientCharts n d e q g a
  let strongCharts := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let D₁ : @Diffeomorph ℝ _ (RModel q) _ _ (EModel q) _ _
      (RModel q) _ (RModel q) _
      𝓘(ℝ, RModel q) (euclideanModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ oldCharts ∞ :=
    euclideanModelDiffeomorph n d e q g a
  letI := euclideanQuotientCharts n d e q g a
  let D₂ : @Diffeomorph ℝ _ (EModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _
      (euclideanModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ selfCharts ∞ :=
    euclideanChartDiffeomorph n d e q g a
  let D₃ : @Diffeomorph ℝ _ (EModel q) _ _ (EModel q) _ _
      (EModel q) _ (EModel q) _
      𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ selfCharts
      (ProjectiveCarrier n) _ strongCharts ∞ := by
    exact restrictedChartsDiffeomorph
      (I := 𝓘(ℝ, EModel q))
      (strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
      (strongGaugeNeighborhood_isOpen hLee hDesc hImm n d e q g a hq hn)
      (mem_strongGaugeNeighborhood hLee hDesc hImm n d e q g a hq hn)
  let D₂₃ : @Diffeomorph ℝ _ (EModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _
      (euclideanModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ strongCharts ∞ :=
    @Diffeomorph.trans ℝ _ (EModel q) _ _ (EModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _ (EModel q) _
      (euclideanModel q) 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ selfCharts
      (ProjectiveCarrier n) _ strongCharts ∞ D₂ D₃
  have h : @Diffeomorph ℝ _ (RModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _
      𝓘(ℝ, RModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ strongCharts ∞ :=
    @Diffeomorph.trans ℝ _ (RModel q) _ _ (EModel q) _ _ (EModel q) _ _
      (RModel q) _ (RModel q) _ (EModel q) _
      𝓘(ℝ, RModel q) (euclideanModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ strongCharts ∞ D₁ D₂₃
  exact h

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
