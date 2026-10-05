import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! Generator-level preservation of a quaternionic endomorphism span
extends linearly to every member of that span. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicCommutatorSpan

open VectorBundleFrameTransitions
open scoped Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem commutator_mem_of_generators
    (Q : QuaternionicStructure E) (Γ : E →L[ℝ] E)
    (h : ∀ t : Fin 3,
      Γ * quaternionicGenerator Q t - quaternionicGenerator Q t * Γ ∈
        quaternionicSpan Q)
    (T : E →L[ℝ] E) (hT : T ∈ quaternionicSpan Q) :
    Γ * T - T * Γ ∈ quaternionicSpan Q := by
  change T ∈ Submodule.span ℝ (Set.range (quaternionicGenerator Q)) at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨t, rfl⟩ := hT
    exact h t
  | zero =>
    simp
  | add A B _ _ hA hB =>
    have hsum := (quaternionicSpan Q).add_mem hA hB
    convert hsum using 1 <;> simp [mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  | smul c A _ hA =>
    have hsmul := (quaternionicSpan Q).smul_mem c hA
    convert hsmul using 1 <;> simp [mul_smul, smul_sub]

end
end QuaternionicSymmetry.ManifoldQuaternionicCommutatorSpan
