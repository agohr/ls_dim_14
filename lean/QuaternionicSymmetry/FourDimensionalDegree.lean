import QuaternionicSymmetry.FourDimensionalForms
import QuaternionicSymmetry.ExteriorDimension

/-! Genuine exterior degrees and local nilpotence of the four-coordinate model. -/

namespace QuaternionicSymmetry.FourDimensionalForms

noncomputable section

private theorem g_degree_one (k : Fin 4) :
    g k ∈ ExteriorAlgebra.exteriorPower ℝ 1 V := by
  change g k ∈ (LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] E)) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] E) (e k)

private theorem pair_degree_two (i j : Fin 4) :
    g i * g j ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  simpa only [one_add_one_eq_two] using SetLike.mul_mem_graded (g_degree_one i) (g_degree_one j)

theorem alpha_degree : α ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  rw [α]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 V).sub_mem
    (pair_degree_two 0 1) (pair_degree_two 2 3)

theorem omegaI_degree : ωI ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  rw [ωI]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 V).add_mem
    (pair_degree_two 0 1) (pair_degree_two 2 3)

theorem omegaJ_degree : ωJ ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  rw [ωJ]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 V).sub_mem
    (pair_degree_two 0 2) (pair_degree_two 1 3)

theorem omegaK_degree : ωK ∈ ExteriorAlgebra.exteriorPower ℝ 2 V := by
  rw [ωK]
  exact (ExteriorAlgebra.exteriorPower ℝ 2 V).add_mem
    (pair_degree_two 0 3) (pair_degree_two 1 2)

theorem vol_degree : vol ∈ ExteriorAlgebra.exteriorPower ℝ 4 V := by
  rw [vol]
  simpa only [mul_assoc, two_add_two_eq_four] using
    SetLike.mul_mem_graded (pair_degree_two 0 1) (pair_degree_two 2 3)

private theorem finrank_V : Module.finrank ℝ V = 4 := by
  exact (Module.finrank_fintype_fun_eq_card ℝ (η := Fin 4)).trans rfl

theorem alpha_cube : α ^ 3 = 0 := by
  apply ExteriorDimension.pow_eq_zero_of_degree alpha_degree
  rw [finrank_V]
  norm_num

theorem vol_sq : vol ^ 2 = 0 := by
  apply ExteriorDimension.pow_eq_zero_of_degree vol_degree
  rw [finrank_V]
  norm_num

end
end QuaternionicSymmetry.FourDimensionalForms
