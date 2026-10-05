import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockUnitQuaternion
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfAction

/-! The proven Hopf equivariance applies to the actual first Sp(1) block
of every projector-stabilizer element, with exactly its literal complex
two-by-two matrix action on projective-line coordinates. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHopfAction

open Matrix
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorFirstBlockHalfSpin
open CompactSymplecticProjectorFirstBlockUnitQuaternion
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfAction
open FourDimensionalHalfSpinMatrix
open ManifoldTwistorSphereBundle
open FourDimensionalTwistorNormalizerQuotient
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Quaternion Matrix LinearAlgebra.Projectivization

noncomputable section

theorem firstBlock_halfSpin_apply (A : FirstBlockGroup)
    (v : Fin 2 → ℂ) :
    halfSpinLinearEquiv (firstBlockUnitQuaternion A) v =
      (A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [halfSpinLinearEquiv_apply]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M *ᵥ v)
    (firstBlock_halfSpinMatrix A)

theorem firstBlock_projective_action_mk (A : FirstBlockGroup)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveHalfSpin (firstBlockUnitQuaternion A)
        (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ ((A.1.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)
        (by
          rw [← firstBlock_halfSpin_apply A]
          simpa using
            (halfSpinLinearEquiv (firstBlockUnitQuaternion A)).injective.ne hv) := by
  rw [projectiveHalfSpin_mk]
  congr 1
  exact firstBlock_halfSpin_apply A v

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

theorem actualFirstBlock_projectiveHopf_action
    (S : QuaternionicStructure E) (A : FirstBlockGroup)
    (p : ProjectiveSpinor) :
    FourDimensionalHalfSpinHopfProjectiveDescent.projectiveHopf
        (projectiveHalfSpin (firstBlockUnitQuaternion A) p) =
      act S
        (QuaternionicUnitScalarIsometries.unitQuaternionNormalizerAction S
          (firstBlockUnitQuaternion A))
        (FourDimensionalHalfSpinHopfProjectiveDescent.projectiveHopf p) :=
  projectiveHopf_action S (firstBlockUnitQuaternion A) p

end
end QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockHopfAction
