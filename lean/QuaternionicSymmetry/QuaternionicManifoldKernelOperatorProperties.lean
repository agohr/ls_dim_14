import QuaternionicSymmetry.QuaternionicManifoldProductGaugeIdentity

/-! The smooth local operator factor belongs pointwise to the quaternionic
unitary kernel; its adjoint is its inverse and remains quaternion-linear. -/

namespace QuaternionicSymmetry.QuaternionicManifoldKernelOperatorProperties

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open QuaternionicIsometryNormalizer
open QuaternionicUnitScalarIsometries
open VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem symplecticFactor_commutes_synth (i j : atlas E M)
    (q : unitary ℍ) (x : M) (hx : x ∈ liftNeighborhood Q i j q)
    (a : Fin 3 → ℝ) :
    symplecticFactorOperator S Q i j q x * synth S a =
      synth S a * symplecticFactorOperator S Q i j q x := by
  obtain ⟨h, hh, _⟩ := exists_smooth_operator_factor S Q i j q x hx
  rw [← hh]
  obtain ⟨hI, hJ⟩ := (mem_symplecticKernel_iff S h.1).mp h.2
  apply ContinuousLinearMap.ext
  intro v
  change h.1.1 (synth S a v) = synth S a (h.1.1 v)
  rw [← action_pureScalar S a v, ← action_pureScalar S a (h.1.1 v)]
  exact S.action_commutes h.1.1.toLinearEquiv.toLinearMap hI hJ (pureScalar a) v

theorem symplecticFactor_adjoint_inverse (i j : atlas E M)
    (q : unitary ℍ) (x : M) (hx : x ∈ liftNeighborhood Q i j q) :
    (symplecticFactorOperator S Q i j q x).adjoint *
        symplecticFactorOperator S Q i j q x = 1 ∧
      symplecticFactorOperator S Q i j q x *
        (symplecticFactorOperator S Q i j q x).adjoint = 1 := by
  obtain ⟨h, hh, _⟩ := exists_smooth_operator_factor S Q i j q x hx
  rw [← hh]
  constructor
  · change (h.1.1 : E →L[ℝ] E).adjoint * (h.1.1 : E →L[ℝ] E) = 1
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro v
    exact h.1.1.symm_apply_apply v
  · change (h.1.1 : E →L[ℝ] E) * (h.1.1 : E →L[ℝ] E).adjoint = 1
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro v
    exact h.1.1.apply_symm_apply v

theorem symplecticFactor_adjoint_commutes_synth (i j : atlas E M)
    (q : unitary ℍ) (x : M) (hx : x ∈ liftNeighborhood Q i j q)
    (a : Fin 3 → ℝ) :
    (symplecticFactorOperator S Q i j q x).adjoint * synth S a =
      synth S a * (symplecticFactorOperator S Q i j q x).adjoint := by
  let h := symplecticFactorOperator S Q i j q x
  let T := synth S a
  have hc : h * T = T * h := symplecticFactor_commutes_synth S Q i j q x hx a
  obtain ⟨hleft, hright⟩ := symplecticFactor_adjoint_inverse S Q i j q x hx
  calc
    h.adjoint * T = h.adjoint * (T * (h * h.adjoint)) := by rw [hright, mul_one]
    _ = h.adjoint * ((T * h) * h.adjoint) := by rw [mul_assoc]
    _ = h.adjoint * ((h * T) * h.adjoint) := by rw [hc]
    _ = (h.adjoint * h) * (T * h.adjoint) := by simp only [mul_assoc]
    _ = T * h.adjoint := by rw [hleft, one_mul]

end
end QuaternionicSymmetry.QuaternionicManifoldKernelOperatorProperties
