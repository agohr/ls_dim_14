import QuaternionicSymmetry.CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
import QuaternionicSymmetry.CompactSymplecticHomogeneousAtlasSource

/-! Joint smoothness of the literal Sp action and its inverse-parameter
family on the strong Euclidean quotient atlas, transported through the
already checked old-to-strong identity diffeomorphism. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongJointActionSmooth

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section
set_option maxHeartbeats 1000000

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem strongJointAction_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := g.charts
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, EModel q)) 𝓘(ℝ, EModel q) ∞
      (fun p : G n × ProjectiveCarrier n => leftCosetAction n p.1 p.2) := by
  letI := g.charts
  letI := a.quotientCharts
  letI := a.quotientManifold
  let D := oldToStrongDiffeomorph hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hpair : ContMDiff
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, EModel q))
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
      (fun p : G n × ProjectiveCarrier n => (p.1, D.symm p.2)) :=
    contMDiff_fst.prodMk (D.symm.contMDiff.comp contMDiff_snd)
  have h := D.contMDiff.comp (a.actionSmooth.comp hpair)
  apply h.congr
  intro p
  rfl

theorem strongInverseJointAction_smooth
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) :
    letI := g.charts
    letI := a.quotientCharts
    letI := a.quotientManifold
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
    ContMDiff (𝓘(ℝ, RModel d).prod 𝓘(ℝ, EModel q)) 𝓘(ℝ, EModel q) ∞
      (fun p : G n × ProjectiveCarrier n => leftCosetAction n p.1⁻¹ p.2) := by
  letI := g.charts
  letI := g.manifold
  letI := g.lieGroup
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  letI := strongEuclideanQuotientCharts_isManifold hLee hDesc hImm n d e q g a hq hn
  have hinv : ContMDiff
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, EModel q))
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, EModel q)) ∞
      (fun p : G n × ProjectiveCarrier n => (p.1⁻¹, p.2)) :=
    ((contMDiff_inv 𝓘(ℝ, RModel d) ∞).comp contMDiff_fst).prodMk contMDiff_snd
  exact (strongJointAction_smooth hLee hDesc hImm n d e q g a hq hn).comp hinv

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongJointActionSmooth
