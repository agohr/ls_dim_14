import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws
import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Real trace orthogonality of quaternion-linear operators and scalar
quaternionic generators. This fixes an actual trace identity needed for
comparison of the tangent and standard representations. -/
namespace QuaternionicSymmetry.QuaternionicTraceOrthogonality

open LocalEndomorphismTrace VectorBundleFrameTransitions
  VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem trace_zero_of_anticommutes (J C : E →L[ℝ] E)
    (hJ : J * J = -1) (hC : J * C = -(C * J)) : traceCLM C = 0 := by
  have he : (J * C) * J = C := by rw [hC, neg_mul, mul_assoc, hJ]; simp
  have hc := traceCLM_cyclic J (J * C)
  rw [← mul_assoc, hJ, neg_one_mul, map_neg, he] at hc
  linarith

variable [Nontrivial E]

theorem trace_mul_generator (S : QuaternionicStructure E) (A : E →L[ℝ] E)
    (hA : ∀ a, A * synth S a = synth S a * A) (t : Fin 3) :
    traceCLM (A * quaternionicGenerator S t) = 0 := by
  let j : Fin 3 := if t = 0 then 1 else 0
  have hj : quaternionicGenerator S j * quaternionicGenerator S j = -1 := by
    fin_cases t <;> ext v <;> simp [j, quaternionicGenerator, S.I_sq, S.J_sq]
  have hanti : quaternionicGenerator S j * quaternionicGenerator S t =
      -(quaternionicGenerator S t * quaternionicGenerator S j) := by
    fin_cases t <;> ext v <;>
      simp [j, quaternionicGenerator, S.J_I_anti, S.I_sq]
  have hcomm : A * quaternionicGenerator S j = quaternionicGenerator S j * A := by
    simpa only [synth_basis] using hA (Pi.basisFun ℝ (Fin 3) j)
  apply trace_zero_of_anticommutes (quaternionicGenerator S j) _ hj
  calc
    _ = (quaternionicGenerator S j * A) * quaternionicGenerator S t := by rw [mul_assoc]
    _ = A * (quaternionicGenerator S j * quaternionicGenerator S t) := by rw [← hcomm, mul_assoc]
    _ = -(A * quaternionicGenerator S t * quaternionicGenerator S j) := by rw [hanti]; simp [mul_assoc]

theorem trace_mul_synth (S : QuaternionicStructure E) (A : E →L[ℝ] E)
    (hA : ∀ a, A * synth S a = synth S a * A) (a : Fin 3 → ℝ) :
    traceCLM (A * synth S a) = 0 := by
  rw [synth_apply, Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, trace_mul_generator S A hA, smul_zero, Finset.sum_const_zero]

end
end QuaternionicSymmetry.QuaternionicTraceOrthogonality
