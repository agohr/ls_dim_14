import QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Pointwise uniqueness of metric torsion-free forms, without presuming
the existence of a global connection. -/
namespace QuaternionicSymmetry.MetricTorsionFormUniqueness
open AlgebraicLeviCivitaUniqueness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_of_metric_torsion (S : E ≃L[ℝ] E) (dS : E → E → E)
    (A B : E →L[ℝ] E →L[ℝ] E)
    (hA : ∀ u v w, inner ℝ (A u v) w + inner ℝ v (A u w) = 0)
    (hB : ∀ u v w, inner ℝ (B u v) w + inner ℝ v (B u w) = 0)
    (hTA : ∀ u v, dS u v - dS v u + A u (S v) - A v (S u) = 0)
    (hTB : ∀ u v, dS u v - dS v u + B u (S v) - B v (S u) = 0) : A = B := by
  let D : E → E → E → ℝ := fun u v w => inner ℝ (A (S.symm u) v - B (S.symm u) v) w
  have hsym (u v w : E) : D u v w = D v u w := by
    have ha := hTA (S.symm u) (S.symm v)
    have hb := hTB (S.symm u) (S.symm v)
    rw [S.apply_symm_apply,S.apply_symm_apply] at ha hb
    have he : A (S.symm u) v - B (S.symm u) v = A (S.symm v) u - B (S.symm v) u := by
      linear_combination (norm := module) ha - hb
    exact congrArg (fun z => inner ℝ z w) he
  have hskew (u v w : E) : D u v w = -D u w v := by
    have ha := hA (S.symm u) v w
    have hb := hB (S.symm u) v w
    dsimp only [D]
    simp only [inner_sub_left]
    rw [← real_inner_comm v (A (S.symm u) w)] at ha
    rw [← real_inner_comm v (B (S.symm u) w)] at hb
    linarith
  ext u v
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simpa only [D,S.symm_apply_apply] using
    symmetric_skew_tensor_zero D hsym hskew (S u) v (A u v - B u v)

end QuaternionicSymmetry.MetricTorsionFormUniqueness
