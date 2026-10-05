import QuaternionicSymmetry.CompactSymplecticProjectorTangentRangeEverywhere
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceOrthogonal
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceQuaternionic
import QuaternionicSymmetry.CompactSymplecticProjectorPeirceTangent
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! At every actual projector, the Frobenius-self-adjoint Peirce
idempotent sends each quaternionic-Hermitian ambient matrix onto a
genuine tangent image and fixes all genuine tangent images. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorActualOrthogonalProjection

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorTangentRangeEverywhere
open CompactSymplecticProjectorPeirceTangent
open CompactSymplecticProjectorPeirceQuaternionic
open CompactSymplecticProjectorPeirceOrthogonal
open CompactSymplecticQuaternionicOrbit
open CompactSymplecticHomogeneousAtlasSource
open CompactSymplecticClosedSubgroupSource
open ProjectorPeirceTangentProjection
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

theorem actual_tangentPart_in_differential_range
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n)
    (x : ProjectiveCarrier n) (A : Mat n)
    (hSelf : Aᴴ = A)
    (hQuat : A * CompactSymplecticHaar.standardJ (n + 1) =
      CompactSymplecticHaar.standardJ (n + 1) * A.map star) :
    letI := a.quotientCharts
    ∃ v : TangentSpace 𝓘(ℝ,RModel q) x,
      mfderiv 𝓘(ℝ,RModel q) 𝓘(ℝ,Mat n)
        (quotientOrbitProjector n) x v =
      tangentPart (quotientOrbitProjector n x) A := by
  letI := a.quotientCharts
  let P : Mat n := quotientOrbitProjector n x
  let J : Mat n := CompactSymplecticHaar.standardJ (n + 1)
  have hPself : Pᴴ = P := by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_selfAdjoint n u
  have hPquat : P * J = J * P.map star := by
    induction x using Quotient.inductionOn' with
    | _ u => exact orbitProjector_commutes_quaternionicJ n u
  exact actual_quaternionicHermitian_tangent_surjective hDesc hImm
    n d e q g a hq x (tangentPart P A)
    (tangentPart_hermitian n P A hPself hSelf)
    (tangentPart_tangent P A (by
      induction x using Quotient.inductionOn' with
      | _ u => exact orbitProjector_idempotent n u))
    (tangentPart_quaternionic n J P A hPquat hQuat)

end
end QuaternionicSymmetry.CompactSymplecticProjectorActualOrthogonalProjection
