import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionEquivariance
import QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket
import QuaternionicSymmetry.QuaternionicUnitScalarIsometries

/-! The symplectic-kernel factor acts trivially on the quaternionic-line
infinitesimal representation. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveKernelEquivariance

open scoped Quaternion
open QuaternionicIsometryNormalizer
open QuaternionicLieAlgebraProjection
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardLieBracket
open QuaternionicUnitScalarIsometries
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable (S : QuaternionicStructure E)

theorem kernel_commutes_synth (h : symplecticKernel S)
    (a : Fin 3 → ℝ) :
    (h.1.1 : E →L[ℝ] E) * synth S a =
      synth S a * (h.1.1 : E →L[ℝ] E) := by
  obtain ⟨hI, hJ⟩ := (mem_symplecticKernel_iff S h.1).mp h.2
  apply ContinuousLinearMap.ext
  intro v
  change h.1.1 (synth S a v) = synth S a (h.1.1 v)
  rw [← action_pureScalar S a v, ← action_pureScalar S a (h.1.1 v)]
  exact S.action_commutes h.1.1.toLinearEquiv.toLinearMap hI hJ (pureScalar a) v

theorem kernel_conjugation_synth (h : symplecticKernel S)
    (a : Fin 3 → ℝ) :
    conjugation h.1.1 (synth S a) = synth S a := by
  apply ContinuousLinearMap.ext
  intro v
  have hc := congrArg (fun A : E →L[ℝ] E => A (h.1.1.symm v))
    (kernel_commutes_synth S h a)
  change h.1.1 (synth S a (h.1.1.symm v)) = synth S a v
  simpa using hc

theorem scalarLineLie_conjugation_kernel (h : symplecticKernel S)
    (A : E →L[ℝ] E)
    (hA : ∀ a, symplecticProjection S A * synth S a =
      synth S a * symplecticProjection S A) :
    scalarLineLie S (conjugation h.1.1 A) = scalarLineLie S A := by
  rw [← scalarLineLie_scalarProjection,
    scalarProjection_conjugation S h.1 A hA]
  change scalarLineLie S (conjugation h.1.1 (synth S _)) = _
  rw [kernel_conjugation_synth S h]
  exact scalarLineLie_scalarProjection S A

end
end QuaternionicSymmetry.QuaternionicProjectiveKernelEquivariance
