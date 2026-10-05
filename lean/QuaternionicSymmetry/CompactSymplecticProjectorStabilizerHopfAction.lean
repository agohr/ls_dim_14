import QuaternionicSymmetry.CompactSymplecticProjectorFirstBlockQuaternionHom

/-! The genuine projector stabilizer acts on its complex projective-line
fiber through the checked first Sp(1) block, and on the quaternionic
coefficient sphere through its actual normalizer rotation. The checked Hopf
map intertwines these two full stabilizer actions. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorStabilizerHopfAction

open CompactSymplecticProjectiveQuotient
open CompactSymplecticStabilizerBlockPair
open CompactSymplecticProjectorFirstBlockQuaternionHom
open CompactSymplecticProjectorFirstBlockHopfAction
open FourDimensionalHalfSpinProjective
open FourDimensionalHalfSpinHopfProjectiveDescent
open FourDimensionalTwistorNormalizerQuotient
open QuaternionicUnitScalarIsometries
open QuaternionicIsometryNormalizer
open ManifoldTwistorSphereBundle
open scoped Quaternion LinearAlgebra.Projectivization

noncomputable section

private abbrev K (n : ℕ) := firstPairStabilizer n

def stabilizerUnitQuaternionHom (n : ℕ) : K n →* unitary ℍ :=
  firstBlockUnitQuaternionHom.comp
    ((MonoidHom.fst FirstBlockGroup (CompactSymplecticHaar.Group n)).comp
      (blockPairHom n))

private theorem projectiveHalfSpin_one (p : ProjectiveSpinor) :
    projectiveHalfSpin (1 : unitary ℍ) p = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectiveHalfSpin_mk]
    have h : halfSpinLinearEquiv (1 : unitary ℍ) v = v := by
      rw [halfSpinLinearEquiv_apply]
      simp [FourDimensionalHalfSpinMatrix.halfSpinMatrix_one]
    simpa only [h]

def projectiveFiberAction (n : ℕ) : MulAction (K n) ProjectiveSpinor where
  smul k p := projectiveHalfSpin (stabilizerUnitQuaternionHom n k) p
  one_smul p := by
    change projectiveHalfSpin (stabilizerUnitQuaternionHom n 1) p = p
    rw [map_one]
    exact projectiveHalfSpin_one p
  mul_smul k l p := by
    change projectiveHalfSpin (stabilizerUnitQuaternionHom n (k * l)) p =
      projectiveHalfSpin (stabilizerUnitQuaternionHom n k)
        (projectiveHalfSpin (stabilizerUnitQuaternionHom n l) p)
    rw [map_mul, projectiveHalfSpin_mul]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

def sphereFiberAction (n : ℕ) (S : QuaternionicStructure E) :
    MulAction (K n) coefficientSphere where
  smul k a := act S (unitQuaternionNormalizerAction S
    (stabilizerUnitQuaternionHom n k)) a
  one_smul a := by
    change act S (unitQuaternionNormalizerAction S
      (stabilizerUnitQuaternionHom n 1)) a = a
    rw [map_one, map_one]
    change (1 : normalizer S) • a = a
    exact one_smul _ a
  mul_smul k l a := by
    change act S (unitQuaternionNormalizerAction S
      (stabilizerUnitQuaternionHom n (k * l))) a =
      act S (unitQuaternionNormalizerAction S
        (stabilizerUnitQuaternionHom n k))
        (act S (unitQuaternionNormalizerAction S
          (stabilizerUnitQuaternionHom n l)) a)
    rw [map_mul, map_mul]
    change ((unitQuaternionNormalizerAction S
      (stabilizerUnitQuaternionHom n k) *
        unitQuaternionNormalizerAction S
          (stabilizerUnitQuaternionHom n l)) : normalizer S) • a =
      (unitQuaternionNormalizerAction S
        (stabilizerUnitQuaternionHom n k) : normalizer S) •
        ((unitQuaternionNormalizerAction S
          (stabilizerUnitQuaternionHom n l) : normalizer S) • a)
    exact mul_smul _ _ a

theorem projectiveHopf_stabilizer_equivariant
    (n : ℕ) (S : QuaternionicStructure E)
    (k : K n) (p : ProjectiveSpinor) :
    letI := projectiveFiberAction n
    letI := sphereFiberAction n S
    projectiveHopf (k • p) = k • projectiveHopf p := by
  letI := projectiveFiberAction n
  letI := sphereFiberAction n S
  exact actualFirstBlock_projectiveHopf_action S (blockPair n k).1 p

end
end QuaternionicSymmetry.CompactSymplecticProjectorStabilizerHopfAction
