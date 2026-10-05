import QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
import QuaternionicSymmetry.CompactSymplecticProjectorTranslationDiffeomorph

/-! Every actual Sp(n+1) left translation is a genuine diffeomorphism of
the strong Euclidean quotient atlas, with old and strong chart dictionaries
kept separate in the transport. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDiffeomorph

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorTranslationDiffeomorph
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

def strongLeftCosetDiffeomorph
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) :
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
    leftCosetDiffeomorph n d e q g a u
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

theorem strongLeftCosetDiffeomorph_apply
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) (x : ProjectiveCarrier n) :
    strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u x =
      leftCosetAction n u x := rfl

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDiffeomorph
