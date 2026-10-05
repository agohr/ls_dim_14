import QuaternionicSymmetry.CompactSymplecticProjectorFullIsotropyPlane
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Every actual compact-symplectic left translation is a smooth
diffeomorphism of the concrete projector quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTranslationDiffeomorph

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

private theorem leftCosetAction_coe (n : ℕ) (u z : G n) :
    leftCosetAction n u (z : ProjectiveCarrier n) =
      ((u * z : G n) : ProjectiveCarrier n) := rfl

theorem leftCosetAction_mul (n : ℕ) (u v : G n)
    (x : ProjectiveCarrier n) :
    leftCosetAction n u (leftCosetAction n v x) =
      leftCosetAction n (u * v) x := by
  induction x using Quotient.inductionOn' with
  | _ z =>
      rw [leftCosetAction_coe, leftCosetAction_coe,
        leftCosetAction_coe, mul_assoc]

theorem leftCosetAction_one (n : ℕ) (x : ProjectiveCarrier n) :
    leftCosetAction n (1 : G n) x = x := by
  induction x using Quotient.inductionOn' with
  | _ z =>
      rw [leftCosetAction_coe, one_mul]

theorem leftCosetAction_inverse (n : ℕ) (u : G n)
    (x : ProjectiveCarrier n) :
    leftCosetAction n u⁻¹ (leftCosetAction n u x) = x := by
  rw [leftCosetAction_mul, inv_mul_cancel, leftCosetAction_one]

theorem leftCosetAction_smooth (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (u : G n) :
    letI := atlas.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
      (leftCosetAction n u) := by
  letI := g.charts
  letI := atlas.quotientCharts
  have hpair : ContMDiff 𝓘(ℝ, RModel q)
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
      (fun y : ProjectiveCarrier n => (u, y)) :=
    contMDiff_const.prodMk contMDiff_id
  exact atlas.actionSmooth.comp hpair

/-- A genuine diffeomorphism, with inverse translation by `u⁻¹`. -/
def leftCosetDiffeomorph (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (atlas : SmoothHomogeneousAtlas n d e q g) (u : G n) :
    letI := atlas.quotientCharts
    Diffeomorph 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) (ProjectiveCarrier n) ∞ := by
  letI := atlas.quotientCharts
  refine {
    toEquiv := {
      toFun := leftCosetAction n u
      invFun := leftCosetAction n u⁻¹
      left_inv := leftCosetAction_inverse n u
      right_inv := by
        intro x
        simpa only [inv_inv] using leftCosetAction_inverse n u⁻¹ x
    }
    contMDiff_toFun := leftCosetAction_smooth n d e q g atlas u
    contMDiff_invFun := leftCosetAction_smooth n d e q g atlas u⁻¹
  }

end
end QuaternionicSymmetry.CompactSymplecticProjectorTranslationDiffeomorph
