import QuaternionicSymmetry.QuaternionicProjectiveKernelEquivariance
import QuaternionicSymmetry.QuaternionicProjectiveLineMaurer

/-! Equivariance of the quaternionic-line infinitesimal action under an
actual unit-quaternion scalar rotation. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveScalarEquivariance

open scoped Quaternion
open QuaternionicUnitScalarIsometries
open QuaternionicIsometryNormalizer
open QuaternionicLieAlgebraProjection
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardLieBracket
open QuaternionicProjectiveLineMaurer
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicRankThreeOrthogonal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S : QuaternionicStructure E)

theorem commutes_scalarAction_of_commutes_synth
    (A : E →L[ℝ] E)
    (hA : ∀ a : Fin 3 → ℝ, A * synth S a = synth S a * A)
    (q : ℍ) :
    A * QuaternionicManifoldSmoothProductLifts.scalarActionLinear S q =
      QuaternionicManifoldSmoothProductLifts.scalarActionLinear S q * A := by
  have hI (v : E) : A (S.I v) = S.I (A v) := by
    have h := congrArg (fun T : E →L[ℝ] E => T v)
      (hA (Pi.basisFun ℝ (Fin 3) 0))
    simpa only [synth_basis, VectorBundleFrameTransitions.quaternionicGenerator] using h
  have hJ (v : E) : A (S.J v) = S.J (A v) := by
    have h := congrArg (fun T : E →L[ℝ] E => T v)
      (hA (Pi.basisFun ℝ (Fin 3) 1))
    simpa only [synth_basis, VectorBundleFrameTransitions.quaternionicGenerator] using h
  apply ContinuousLinearMap.ext
  intro v
  exact S.action_commutes A.toLinearMap hI hJ q v

theorem scalarLineLie_conjugation_synth (q : unitary ℍ)
    (a : Fin 3 → ℝ) :
    scalarLineLie S
      (conjugation (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q))
        (synth S a)) =
      rightStar (q : ℍ) * scalarLineLie S (synth S a) *
        rightStar (star (q : ℍ)) := by
  rw [unitScalar_conjugation]
  have hp : ((q : ℍ) * pureScalar a * star (q : ℍ)).re = 0 :=
    conjugate_imaginary (q : ℍ) (pureScalar a) (pureScalar_re a)
  apply ContinuousLinearMap.ext
  intro w
  change scalarLineLie S
    (QuaternionicManifoldSmoothProductLifts.scalarActionLinear S
      ((q : ℍ) * pureScalar a * star (q : ℍ))) w = _
  rw [QuaternionicProjectiveLineMaurer.scalarLineLie_scalarAction_pure S _ hp w]
  change w * -((q : ℍ) * pureScalar a * star (q : ℍ)) =
    rightStar (q : ℍ) (scalarLineLie S (synth S a)
      (rightStar (star (q : ℍ)) w))
  rw [scalarLineLie_synth]
  have hi : imaginary a = pureScalar a := by
    ext <;> simp [pureScalar]
  rw [hi]
  simp [rightStar, mul_assoc]

theorem scalarLineLie_conjugation_scalar (q : unitary ℍ)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    scalarLineLie S
      (conjugation (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q)) A) =
      rightStar (q : ℍ) * scalarLineLie S A *
        rightStar (star (q : ℍ)) := by
  rw [← scalarLineLie_scalarProjection S
      (conjugation (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q)) A)]
  change scalarLineLie S
    (scalarProjection S (conjugation (unitQuaternionNormalizerAction S q).1 A)) = _
  rw [scalarProjection_conjugation S (unitQuaternionNormalizerAction S q) A hA]
  change scalarLineLie S (conjugation
      (unitScalarIsometry S (q : ℍ) (normSq_one_of_unitary q)) (synth S _)) = _
  rw [scalarLineLie_conjugation_synth]
  change rightStar (q : ℍ) * scalarLineLie S (scalarProjection S A) *
      rightStar (star (q : ℍ)) = _
  rw [scalarLineLie_scalarProjection]

end
end QuaternionicSymmetry.QuaternionicProjectiveScalarEquivariance
