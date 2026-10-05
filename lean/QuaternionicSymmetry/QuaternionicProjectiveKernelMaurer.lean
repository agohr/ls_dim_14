import QuaternionicSymmetry.QuaternionicProjectiveLineMaurer
import QuaternionicSymmetry.ContinuousLinearConstraintDerivative
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws

/-! Derivatives of smooth symplectic-kernel gauges remain quaternion-linear. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveKernelMaurer

open scoped Topology
open ContinuousLinearConstraintDerivative
open ManifoldQuaternionicAdjointConnection
open QuaternionicLieAlgebraProjection
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [FiniteDimensional ℝ E] in
theorem fderiv_commutes_synth (S : QuaternionicStructure E)
    (h : X → E →L[ℝ] E) (x u : X) (hd : DifferentiableAt ℝ h x)
    (hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ y in 𝓝 x, h y * synth S a = synth S a * h y)
    (a : Fin 3 → ℝ) :
    fderiv ℝ h x u * synth S a = synth S a * fderiv ℝ h x u := by
  let T := synth S a
  have hz := annihilates_fderiv (commutatorMap.flip T) h x u hd (by
    filter_upwards [hc a] with y hy
    change h y * T - T * h y = 0
    exact sub_eq_zero.mpr hy)
  exact sub_eq_zero.mp hz

theorem symplecticProjection_fderiv (S : QuaternionicStructure E)
    (h : X → E →L[ℝ] E) (x u : X) (hd : DifferentiableAt ℝ h x)
    (hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ y in 𝓝 x, h y * synth S a = synth S a * h y) :
    symplecticProjection S (fderiv ℝ h x u) = fderiv ℝ h x u := by
  change fderiv ℝ h x u - scalarProjection S (fderiv ℝ h x u) = _
  rw [scalarProjection_eq_zero_of_commutes S _
    (fderiv_commutes_synth S h x u hd hc), sub_zero]

theorem symplecticProjection_left_mul_fderiv (S : QuaternionicStructure E)
    (h : X → E →L[ℝ] E) (hInv : E →L[ℝ] E) (x u : X)
    (hd : DifferentiableAt ℝ h x)
    (hc : ∀ a : Fin 3 → ℝ,
      ∀ᶠ y in 𝓝 x, h y * synth S a = synth S a * h y)
    (hInvC : ∀ a : Fin 3 → ℝ,
      hInv * synth S a = synth S a * hInv) :
    symplecticProjection S (hInv * fderiv ℝ h x u) =
      hInv * fderiv ℝ h x u := by
  have hcomm (a : Fin 3 → ℝ) :
      (hInv * fderiv ℝ h x u) * synth S a =
        synth S a * (hInv * fderiv ℝ h x u) := by
    rw [mul_assoc, fderiv_commutes_synth S h x u hd hc a,
      ← mul_assoc, hInvC a, mul_assoc]
  change hInv * fderiv ℝ h x u -
    scalarProjection S (hInv * fderiv ℝ h x u) = _
  rw [scalarProjection_eq_zero_of_commutes S _ hcomm, sub_zero]

end
end QuaternionicSymmetry.QuaternionicProjectiveKernelMaurer
