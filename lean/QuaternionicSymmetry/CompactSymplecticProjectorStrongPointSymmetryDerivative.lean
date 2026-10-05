import QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetry
import QuaternionicSymmetry.ManifoldPointSymmetryDiffeomorphTransport

/-! The actual point reflection still differentiates to `-Id` at its fixed
center after the checked old-to-strong change of smooth atlas. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryDerivative

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStrongAtlasIdentityDiffeomorph
open CompactSymplecticProjectorStrongPointSymmetry
open CompactSymplecticProjectorStrongGaugeAtlas
open CompactSymplecticProjectorPointSymmetry
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open GeneralSmoothLocalSectionSource
open ManifoldPointSymmetryDiffeomorphTransport
open scoped Quaternion Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (q : ℕ) := Fin q → ℝ
private abbrev EModel (q : ℕ) := EuclideanSpace ℝ (Fin q)

theorem pointSymmetry_mfderiv_neg_strong
    (hLee : LeeLocalSectionTheorem)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (hn : 0 < n) (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
    ∀ v : EModel q,
      mfderiv 𝓘(ℝ, EModel q) 𝓘(ℝ, EModel q)
        (pointSymmetry n x) x v = -v := by
  letI := a.quotientCharts
  letI := strongEuclideanQuotientCharts hLee hDesc hImm n d e q g a hq hn
  let D := oldToStrongDiffeomorph hLee hDesc hImm n d e q g a hq hn
  let S := pointSymmetry_diffeomorph n d e q g a x
  intro v
  have hgen := conjugate_mfderiv_neg D S x
    (pointSymmetry_fixed n x)
    (pointSymmetry_mfderiv_neg hDesc hImm n d e q g a x) v
  have hfun :
      (D.symm.trans S |>.trans D : ProjectiveCarrier n → ProjectiveCarrier n) =
        pointSymmetry n x := by
    funext y
    rfl
  rw [hfun] at hgen
  simpa using hgen

end
end QuaternionicSymmetry.CompactSymplecticProjectorStrongPointSymmetryDerivative
