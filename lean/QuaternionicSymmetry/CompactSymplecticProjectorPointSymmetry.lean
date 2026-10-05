import QuaternionicSymmetry.CompactSymplecticProjectorReflection
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Genuine Riemannian point symmetries of the compact projector quotient.
These are actual smooth involutive isometries, with derivative `-Id` at
their centers. No quaternionic-Kähler or twistor identification is made. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetry

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticProjectorReflection
open CompactSymplecticProjectorRiemannianMetric
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

private theorem leftCosetAction_coe (n : ℕ)
    (u z : CompactSymplecticHaar.Group (n + 1)) :
    leftCosetAction n u (z : ProjectiveCarrier n) =
      ((u * z : CompactSymplecticHaar.Group (n + 1)) : ProjectiveCarrier n) := rfl

/-- The actual reflection squares to the identity in `Sp(n+1)`. -/
theorem reflectionElement_sq (n : ℕ) (x : ProjectiveCarrier n) :
    reflectionElement n x * reflectionElement n x = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change ((reflectionElement n x).1 : Mat n) *
    ((reflectionElement n x).1 : Mat n) = 1
  rw [reflectionElement_matrix, reflectionMatrix_sq]
  induction x using Quotient.inductionOn' with
  | _ u => exact CompactSymplecticProjectorOrbit.orbitProjector_idempotent n u

/-- The genuine point symmetry at a coset is translation by its actual
compact-symplectic reflection. -/
def pointSymmetry (n : ℕ) (x : ProjectiveCarrier n) :
    ProjectiveCarrier n → ProjectiveCarrier n :=
  leftCosetAction n (reflectionElement n x)

theorem pointSymmetry_fixed (n : ℕ) (x : ProjectiveCarrier n) :
    pointSymmetry n x x = x := reflectionElement_fixes n x

theorem pointSymmetry_involutive (n : ℕ) (x y : ProjectiveCarrier n) :
    pointSymmetry n x (pointSymmetry n x y) = y := by
  induction y using Quotient.inductionOn' with
  | _ z =>
    change leftCosetAction n (reflectionElement n x)
      (leftCosetAction n (reflectionElement n x) (z : ProjectiveCarrier n)) = z
    rw [leftCosetAction_coe, leftCosetAction_coe, ← mul_assoc, reflectionElement_sq]
    simp

/-- Every point reflection is smooth for the actual Lee quotient atlas. -/
theorem pointSymmetry_smooth (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ContMDiff 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q) ∞
      (pointSymmetry n x) := by
  letI := g.charts
  letI := a.quotientCharts
  have hpair : ContMDiff 𝓘(ℝ, RModel q)
      (𝓘(ℝ, RModel d).prod 𝓘(ℝ, RModel q)) ∞
      (fun y : ProjectiveCarrier n => (reflectionElement n x, y)) :=
    contMDiff_const.prodMk contMDiff_id
  exact a.actionSmooth.comp hpair

/-- The point symmetry is a smooth diffeomorphism, with itself as inverse. -/
def pointSymmetry_diffeomorph (n d e q : ℕ)
    (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    Diffeomorph 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
      (ProjectiveCarrier n) (ProjectiveCarrier n) ∞ := by
  letI := a.quotientCharts
  refine {
    toEquiv := {
      toFun := pointSymmetry n x
      invFun := pointSymmetry n x
      left_inv := pointSymmetry_involutive n x
      right_inv := pointSymmetry_involutive n x
    }
    contMDiff_toFun := pointSymmetry_smooth n d e q g a x
    contMDiff_invFun := pointSymmetry_smooth n d e q g a x
  }

/-- The actual point symmetry has derivative `-Id` at its fixed center. -/
theorem pointSymmetry_mfderiv_neg
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) x),
      mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (pointSymmetry n x) x v = -v :=
  reflectionElement_mfderiv_neg hDesc hImm n d e q g a x

/-- Point reflection preserves the actual Frobenius-pullback smooth metric. -/
theorem pointSymmetry_metric_invariant
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x y : ProjectiveCarrier n) :
    letI := a.quotientCharts
    letI := a.quotientManifold
    ∀ (v w : TangentSpace 𝓘(ℝ, RModel q) y),
      (smoothProjectorMetric hDesc hImm n d e q g a).inner
        (pointSymmetry n x y)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (pointSymmetry n x) y v)
        (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (pointSymmetry n x) y w) =
      (smoothProjectorMetric hDesc hImm n d e q g a).inner y v w :=
  smoothProjectorMetric_invariant hDesc hImm n d e q g a (reflectionElement n x) y

end
end QuaternionicSymmetry.CompactSymplecticProjectorPointSymmetry
