import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

/-! Dimension bounds for genuine homogeneous exterior forms. -/

namespace QuaternionicSymmetry.ExteriorDimension

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

private theorem iMulti_eq_zero_of_finrank_lt (n : ℕ)
    (h : Module.finrank ℝ V < n) (v : Fin n → V) :
    ExteriorAlgebra.ιMulti ℝ n v = 0 := by
  apply AlternatingMap.map_linearDependent
  intro hv
  exact (not_le_of_gt h) (by simpa using hv.fintype_card_le_finrank)

/-- Exterior powers above the actual finite dimension are zero. -/
theorem exteriorPower_eq_bot_of_finrank_lt (n : ℕ)
    (h : Module.finrank ℝ V < n) :
    ExteriorAlgebra.exteriorPower ℝ n V = ⊥ := by
  apply le_antisymm
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
    apply Submodule.span_le.2
    rintro x ⟨v, rfl⟩
    rw [iMulti_eq_zero_of_finrank_lt n h v]
    exact Submodule.zero_mem _
  · exact bot_le

/-- A product whose homogeneous exterior degree exceeds the dimension vanishes. -/
theorem mul_eq_zero_of_degrees {m n : ℕ} {x y : ExteriorAlgebra ℝ V}
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℝ m V)
    (hy : y ∈ ExteriorAlgebra.exteriorPower ℝ n V)
    (h : Module.finrank ℝ V < m + n) : x * y = 0 := by
  have hxy : x * y ∈ ExteriorAlgebra.exteriorPower ℝ (m + n) V :=
    SetLike.mul_mem_graded hx hy
  rw [exteriorPower_eq_bot_of_finrank_lt (m + n) h] at hxy
  exact hxy

/-- A homogeneous exterior form has zero powers once its total degree exceeds the dimension. -/
theorem pow_eq_zero_of_degree {m k : ℕ} {x : ExteriorAlgebra ℝ V}
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℝ m V)
    (h : Module.finrank ℝ V < k * m) : x ^ k = 0 := by
  have hxk : x ^ k ∈ ExteriorAlgebra.exteriorPower ℝ (k * m) V := by
    simpa only [Nat.nsmul_eq_mul] using SetLike.pow_mem_graded k hx
  rw [exteriorPower_eq_bot_of_finrank_lt (k * m) h] at hxk
  exact hxk

end
end QuaternionicSymmetry.ExteriorDimension
