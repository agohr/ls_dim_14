import QuaternionicSymmetry.ManifoldTwistorVerticalComplex

/-! The fixed points on the unit coefficient sphere of a half-turn on
the vertical plane are exactly its two axis directions. -/
namespace QuaternionicSymmetry.QuaternionicSphereHalfTurn
open ManifoldTwistorSphereBundle ManifoldTwistorVerticalComplex
open scoped Matrix
noncomputable section

theorem fixed_unit_eq_axis_or_neg
    (a b : coefficientSphere) (L : Module.End ℝ (Fin 3 → ℝ))
    (haxis : L a.1 = a.1)
    (hvertical : ∀ v : verticalSubmodule a, L v.1 = -v.1)
    (hb : L b.1 = b.1) : b.1 = a.1 ∨ b.1 = -a.1 := by
  let c : ℝ := a.1 ⬝ᵥ b.1
  let v : Fin 3 → ℝ := b.1 - c • a.1
  have hv : v ∈ verticalSubmodule a := by
    change a.1 ⬝ᵥ (b.1 - c • a.1) = 0
    rw [dotProduct_sub, dotProduct_smul, dot_self]
    simp [c]
  have hLv : L v = v := by simp [v, map_sub, map_smul, hb, haxis]
  have hvneg : v = -v := hLv.symm.trans (hvertical ⟨v, hv⟩)
  have hvzero : v = 0 := by
    funext i
    have hi := congrFun hvneg i
    change v i = -(v i) at hi
    change v i = 0
    linarith
  have hbmul : b.1 = c • a.1 := sub_eq_zero.mp hvzero
  have hcsq : c*c = 1 := by
    have hbb := dot_self b
    rw [hbmul, dotProduct_smul, smul_dotProduct, dot_self] at hbb
    simpa using hbb
  have hc : c = 1 ∨ c = -1 := by
    have hfactor : (c - 1) * (c + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left; linarith
    · right; linarith
  rcases hc with hc | hc
  · left; simpa [hc] using hbmul
  · right; simpa [hc] using hbmul

end
end QuaternionicSymmetry.QuaternionicSphereHalfTurn
