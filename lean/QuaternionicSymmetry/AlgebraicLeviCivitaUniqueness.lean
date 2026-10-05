import Mathlib.Tactic

/-! The algebraic core of uniqueness of a metric torsion-free connection. -/
namespace QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness

theorem symmetric_skew_tensor_zero {E : Type*} (B : E → E → E → ℝ)
    (hsym : ∀ u v w, B u v w = B v u w)
    (hskew : ∀ u v w, B u v w = -B u w v)
    (u v w : E) : B u v w = 0 := by
  have h : B u v w = -B u v w := calc
    B u v w = B v u w := hsym u v w
    _ = -B v w u := hskew v u w
    _ = -B w v u := by rw [hsym v w u]
    _ = B w u v := by rw [hskew w v u]; ring
    _ = B u w v := hsym w u v
    _ = -B u v w := hskew u w v
  linarith

end QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
