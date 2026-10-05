import QuaternionicSymmetry.ContinuousLinearMapTraceDerivative

/-! Trace in a basis carried by a continuous linear equivalence. -/
namespace QuaternionicSymmetry.ContinuousLinearMapTraceBasis
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedSpace ℝ E := inferInstance

theorem trace_in_frame (e : E ≃L[ℝ] E) (A : E →L[ℝ] E) :
    realTraceCLM A =
      ∑ i : Fin (Module.finrank ℝ E),
        inner ℝ (e (A (e.symm (stdOrthonormalBasis ℝ E i))))
          (stdOrthonormalBasis ℝ E i) := by
  have h : LinearMap.trace ℝ E A.toLinearMap =
      LinearMap.trace ℝ E
        (e.toLinearEquiv.conj A.toLinearMap) := by
    symm
    exact LinearMap.trace_conj' A.toLinearMap e.toLinearEquiv
  rw [realTraceCLM_apply, h,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  exact real_inner_comm _ _

end
end QuaternionicSymmetry.ContinuousLinearMapTraceBasis
