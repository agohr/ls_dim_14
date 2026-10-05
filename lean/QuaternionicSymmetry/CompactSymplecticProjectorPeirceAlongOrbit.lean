import QuaternionicSymmetry.CompactSymplecticProjectorPeirceDerivative
import QuaternionicSymmetry.CompactSymplecticProjectorSmoothAction

/-! Differentiate the genuine projector-dependent orthogonal tangent
projection along the actual quotient orbit, not an abstract model curve. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorPeirceAlongOrbit

open Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorPeirceDerivative
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem mfderiv_tangentPart_along_orbit
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (x : ProjectiveCarrier n) (A : Mat n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ,RModel q) x),
    let P := quotientOrbitProjector n x
    let X : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (quotientOrbitProjector n) x v
    mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      (fun y : ProjectiveCarrier n => tangentPart (quotientOrbitProjector n y) A)
      x v = X * A + A * X - 2 • (X * A * P + P * A * X) := by
  letI := a.quotientCharts
  intro v
  let P : Mat n := quotientOrbitProjector n x
  let X : Mat n := mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (quotientOrbitProjector n) x v
  have hf := smooth_quotientOrbitProjector_actual hDesc n d e q g a
  have hpoly : DifferentiableAt ℝ (fun B : Mat n => tangentPart B A) P := by
    unfold tangentPart
    fun_prop
  have hcomp := mfderiv_comp x hpoly.mdifferentiableAt
    (hf.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
      ((fun B : Mat n => tangentPart B A) ∘ quotientOrbitProjector n) x = _ at hcomp
  rw [mfderiv_eq_fderiv] at hcomp
  have hv := congrArg
    (fun D : TangentSpace 𝓘(ℝ,RModel q) x →L[ℝ] Mat n => D v) hcomp
  change mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
    (fun y : ProjectiveCarrier n => tangentPart (quotientOrbitProjector n y) A)
      x v = (fderiv ℝ (fun B : Mat n => tangentPart B A) P) X at hv
  rw [fderiv_tangentPart n P A X] at hv
  exact hv

end
end QuaternionicSymmetry.CompactSymplecticProjectorPeirceAlongOrbit
