import QuaternionicSymmetry.FourDimensionalHalfSpinHopfEquiv
import QuaternionicSymmetry.FourDimensionalTwistorNormalizerQuotient

/-! The checked Hopf equivalence intertwines the actual projective
half-spin SU(2) representation with the normalizer's adjoint rotation on
the quaternionic twistor sphere.  This fixes the local action convention;
the SO(4) associated-bundle and AHS differential comparison remain open. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfAction

open scoped Quaternion Matrix
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicIsometryNormalizer QuaternionicUnitScalarIsometries
open FourDimensionalTwistorNormalizerQuotient
open FourDimensionalHalfSpinProjective
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinHopfEquivariance
open ManifoldTwistorSphereBundle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  (S : QuaternionicStructure E)

private theorem pureScalar_injective : Function.Injective pureScalar := by
  intro a b h
  funext i
  fin_cases i
  · exact congrArg (fun p : ℍ => p.imI) h
  · exact congrArg (fun p : ℍ => p.imJ) h
  · exact congrArg (fun p : ℍ => p.imK) h

/-- Actual normalizer rotation is quaternionic conjugation under the
coefficient-to-imaginary-quaternion map. -/
theorem pureScalar_rotation (q : unitary ℍ) (a : Fin 3 → ℝ) :
    pureScalar (rotationLinear S (unitQuaternionNormalizerAction S q) a) =
      (q : ℍ) * pureScalar a * star (q : ℍ) := by
  have hs := synth_rotationLinear S (unitQuaternionNormalizerAction S q) a
  change synth S (rotationLinear S (unitQuaternionNormalizerAction S q) a) =
    conjugation (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q))
      (synth S a) at hs
  rw [unitScalar_conjugation] at hs
  apply action_injective S
  apply LinearMap.ext
  intro v
  have he := congrArg (fun A : E →L[ℝ] E => A v) hs
  simpa only [action_pureScalar] using he

/-- Pointwise local Hopf map is genuinely equivariant for the checked
SU(2) matrix and quaternionic normalizer actions. -/
theorem hopfSphere_action (q : unitary ℍ)
    (v : Spinor) (hv : v ≠ 0) :
    hopfSphere (halfSpinLinearEquiv q v) (matrix_nonzero q v hv) =
      act S (unitQuaternionNormalizerAction S q) (hopfSphere v hv) := by
  apply Subtype.ext
  apply pureScalar_injective
  calc
    pureScalar (hopfSphere (halfSpinLinearEquiv q v)
        (matrix_nonzero q v hv)).1 =
      (q : ℍ) * pureScalar (hopfSphere v hv).1 * star (q : ℍ) :=
        hopfSphere_pureScalar_halfSpin q v hv
    _ = pureScalar (act S (unitQuaternionNormalizerAction S q)
          (hopfSphere v hv)).1 :=
        (pureScalar_rotation S q (hopfSphere v hv).1).symm

/-- The true projective half-spin action and actual twistor-sphere action
commute with the explicit Hopf equivalence. -/
theorem projectiveHopf_action (q : unitary ℍ) (p : ProjectiveSpinor) :
    projectiveHopf (projectiveHalfSpin q p) =
      act S (unitQuaternionNormalizerAction S q) (projectiveHopf p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveHalfSpin_mk, projectiveHopf_mk, projectiveHopf_mk]
    exact hopfSphere_action S q v hv

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfAction
