import QuaternionicSymmetry.QuaternionicTorusWeightKernel

/-! Every nonzero integral torus character takes the value -1. The
witness is an explicit single-coordinate circle element. -/
namespace QuaternionicSymmetry.TorusWeightHalfTurn
open ManifoldQuaternionicTorusAction QuaternionicTorusWeightKernel
noncomputable section

theorem exists_halfTurn {r : ℕ} (μ : Fin r → ℤ) (hμ : μ ≠ 0) :
    ∃ t : Torus r, (weightCharacter μ t : ℂ) = -1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    apply hμ
    funext i
    simpa using not_exists.mp h i
  have hiR : (μ i : ℝ) ≠ 0 := by exact_mod_cast hi
  refine ⟨Pi.mulSingle i (Circle.exp (Real.pi / (μ i : ℝ))), ?_⟩
  rw [weightCharacter_mulSingle, ← Circle.exp_intCast_mul]
  have he : (μ i : ℝ) * (Real.pi / (μ i : ℝ)) = Real.pi := by field_simp
  rw [he, Circle.coe_exp, Complex.exp_pi_mul_I]

end
end QuaternionicSymmetry.TorusWeightHalfTurn
