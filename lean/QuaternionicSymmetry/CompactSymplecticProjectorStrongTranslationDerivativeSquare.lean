import QuaternionicSymmetry.CompactSymplecticProjectorOldToStrongTangent
import QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDiffeomorph
import QuaternionicSymmetry.ManifoldDiffeomorphConjugateDerivative

/-! The old and strong derivatives of every genuine symplectic translation
form the exact coordinate square through the Euclidean model equivalence. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDerivativeSquare

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorOldToStrongTangent
open CompactSymplecticProjectorStrongTranslationDiffeomorph
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorEuclideanModel
open CompactSymplecticProjectorTranslationDiffeomorph
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldDiffeomorphConjugateDerivative
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff

noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem translation_derivative_coordinate_square
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (u : G n) (y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∀ v : RModel q,
      (euclideanModelEquiv q)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n u) y v) =
      mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
        (leftCosetAction n u) y ((euclideanModelEquiv q) v) := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let D := oldToStrongDiffeomorph hLee hDesc hImm n d e q g a hq hn
  let S := leftCosetDiffeomorph n d e q g a u
  let T := strongLeftCosetDiffeomorph hLee hDesc hImm n d e q g a hq hn u
  have hfun : (D : ProjectiveCarrier n → ProjectiveCarrier n) ∘
      (S : ProjectiveCarrier n → ProjectiveCarrier n) =
      (T : ProjectiveCarrier n → ProjectiveCarrier n) ∘
        (D : ProjectiveCarrier n → ProjectiveCarrier n) := by
    funext z
    rfl
  have hsquare := mfderiv_commuting_square D S T hfun y
  have hDy := oldToStrong_mfderiv_eq_coordinateEquiv
    hLee hDesc hImm n d e q g a hq hn y
  have hDSy := oldToStrong_mfderiv_eq_coordinateEquiv
    hLee hDesc hImm n d e q g a hq hn (S y)
  rw [hDy, hDSy] at hsquare
  intro v
  have hv := congrArg (fun L : RModel q →L[ℝ] EModel q => L v) hsquare
  simpa only [Diffeomorph.coe_trans, ContinuousLinearMap.comp_apply] using hv

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongTranslationDerivativeSquare
