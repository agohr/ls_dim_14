import QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetry

/-! Actual point reflections are smooth involutive diffeomorphisms in the
strong Euclidean quotient atlas, transferred through the checked identity
diffeomorphism with every old/new chart dictionary fixed explicitly. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetry

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

def strongPointSymmetryDiffeomorph
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    @Diffeomorph ℝ _ (EModel q) _ _ (EModel q) _ _
      (EModel q) _ (EModel q) _
      𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _
      (strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn)
      (ProjectiveCarrier n) _
      (strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn) ∞ := by
  let oldCharts := a.quotientCharts
  let strongCharts := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let D := oldToStrongDiffeomorph hLee hDesc hImm n d e q g a hq hn
  let S : @Diffeomorph ℝ _ (RModel q) _ _ (RModel q) _ _
      (RModel q) _ (RModel q) _
      𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ oldCharts ∞ :=
    pointSymmetry_diffeomorph n d e q g a x
  let T : @Diffeomorph ℝ _ (EModel q) _ _ (RModel q) _ _
      (EModel q) _ (RModel q) _
      𝓘(ℝ, EModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) _ strongCharts
      (ProjectiveCarrier n) _ oldCharts ∞ := D.symm
  let U : @Diffeomorph ℝ _ (RModel q) _ _ (EModel q) _ _
      (RModel q) _ (EModel q) _
      𝓘(ℝ, RModel q) 𝓘(ℝ, EModel q)
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ strongCharts ∞ := D
  let TS : @Diffeomorph ℝ _ (EModel q) _ _ (RModel q) _ _
      (EModel q) _ (RModel q) _
      𝓘(ℝ, EModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) _ strongCharts
      (ProjectiveCarrier n) _ oldCharts ∞ :=
    @Diffeomorph.trans ℝ _ (EModel q) _ _ (RModel q) _ _ (RModel q) _ _
      (EModel q) _ (RModel q) _ (RModel q) _
      𝓘(ℝ, EModel q) 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) _ strongCharts
      (ProjectiveCarrier n) _ oldCharts
      (ProjectiveCarrier n) _ oldCharts ∞ T S
  exact @Diffeomorph.trans ℝ _ (EModel q) _ _ (RModel q) _ _ (EModel q) _ _
    (EModel q) _ (RModel q) _ (EModel q) _
    𝓘(ℝ, EModel q) 𝓘(ℝ, RModel q) 𝓘(ℝ, EModel q)
    (ProjectiveCarrier n) _ strongCharts
    (ProjectiveCarrier n) _ oldCharts
    (ProjectiveCarrier n) _ strongCharts ∞ TS U

theorem strongPointSymmetry_apply
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x y : ProjectiveCarrier n) :
    strongPointSymmetryDiffeomorph hLee hDesc hImm n d e q g a hq hn x y =
      pointSymmetry n x y := by
  rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetry
