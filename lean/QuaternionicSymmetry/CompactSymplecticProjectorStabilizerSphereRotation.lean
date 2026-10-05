import QuaternionicSymmetry.CompactSymplecticProjectorAssociatedAmbientEquiv
import QuaternionicSymmetry.CompactSymplecticProjectorFullIsotropyPlane

/-! The checked stabilizer sphere action rotates each coefficient by exactly
the same literal quaternionic conjugation that appeared in the genuine
base-tangent isotropy computation. This is the representation-level bridge
needed to match associated S² with the actual Q-plane unit sphere. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerSphereRotation

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorStabilizerHopfAction
open CompactSymplecticProjectorFirstBlockUnitQuaternion
open CompactSymplecticProjectorFirstBlockQuaternionHom
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorBaseQuaternionAction
open FourDimensionalHalfSpinHopfAction
open QuaternionicUnitScalarIsometries
open ManifoldTwistorSphereBundle
open scoped Quaternion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem stabilizer_sphere_pureScalar (n : ℕ)
    (S : QuaternionicStructure E) (k : firstPairStabilizer n)
    (a : coefficientSphere) :
    letI := sphereFiberAction n S
    pureScalar ((k • a).1) =
      firstBlockQuaternion (blockPair n k).1 * pureScalar a.1 *
        star (firstBlockQuaternion (blockPair n k).1) := by
  letI := sphereFiberAction n S
  change pureScalar
      (QuaternionicIsometryNormalizer.rotationLinear S
        (unitQuaternionNormalizerAction S (stabilizerUnitQuaternionHom n k)) a.1) = _
  simpa [stabilizerUnitQuaternionHom, firstBlockUnitQuaternionHom_apply,
    firstBlockUnitQuaternion_coe] using
      pureScalar_rotation S (firstBlockUnitQuaternion (blockPair n k).1) a.1

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerSphereRotation
