import QuaternionicSymmetry.GeneralLeviCivitaCoordinatePositive
import QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness

/-! Uniqueness of the ordinary metric-compatible torsion-free coordinate
connection at each valid chart point, directly from the algebraic
skew/symmetric tensor identity. No quaternionic connection is assumed. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaCoordinateUniqueness

open Manifold Bundle GeneralLeviCivitaSource
open GeneralLeviCivitaCoordinatePositive
open QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem form_eq_on_chart
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (D₁ D₂ : CoordinateLeviCivitaConnection g)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    D₁.form p y = D₂.form p y := by
  let G : E → E → ℝ := chartMetric g p y
  let B : E → E → E → ℝ := fun u v w =>
    G (D₁.form p y u v) w - G (D₂.form p y u v) w
  have hGsym (v w : E) : G v w = G w v := by
    dsimp [G, chartMetric]
    exact g.symm _ _ _
  have hGsub (v w z : E) : G (v - w) z = G v z - G w z := by
    simp [G, chartMetric]
  have hskew : ∀ u v w, B u v w = -B u w v := by
    intro u v w
    have h₁ := D₁.metric p y u v w hy
    have h₂ := D₂.metric p y u v w hy
    have heq := h₁.symm.trans h₂
    change G (D₁.form p y u v) w + G v (D₁.form p y u w) =
      G (D₂.form p y u v) w + G v (D₂.form p y u w) at heq
    dsimp [B]
    rw [hGsym (D₁.form p y u w) v, hGsym (D₂.form p y u w) v]
    dsimp [G] at heq ⊢
    linarith only [heq]
  have hsym : ∀ u v w, B u v w = B v u w := by
    intro u v w
    dsimp [B]
    rw [D₁.torsion p y u v hy, D₂.torsion p y u v hy]
  ext u v
  let z : E := D₁.form p y u v - D₂.form p y u v
  have hz : G z z = 0 := by
    have h := symmetric_skew_tensor_zero B hsym hskew u v z
    simpa only [B, z, hGsub] using h
  by_contra hne
  have hpos : 0 < G z z := chartMetric_pos g p y z hy (sub_ne_zero.mpr hne)
  linarith

end
end QuaternionicSymmetry.GeneralLeviCivitaCoordinateUniqueness
