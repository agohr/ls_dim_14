import QuaternionicSymmetry.GeneralImmersionLeviCivitaProjectionOnHessian

/-! Continuous-linear version of the exact Hessian-range Gauss algebra,
matching actual chart derivatives and the Frobenius pairing directly. -/

namespace QuaternionicSymmetry.GeneralImmersionLeviCivitaProjectionContinuous

open AlgebraicLeviCivitaUniqueness

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (F : E →L[ℝ] V) (proj : V →L[ℝ] V)
  (g : V →L[ℝ] V →L[ℝ] ℝ) (Γ : E → E → E) (H : E → E → V)

theorem projected_christoffel_eq_second_derivative_on_hessian
    (hpos : ∀ Z : V, g Z Z = 0 → Z = 0)
    (hproj : ∀ u v : E, ∃ w : E, proj (H u v) = F w)
    (hfix : ∀ w : E, proj (F w) = F w)
    (hadjoint : ∀ Z W : V, g (proj Z) W = g Z (proj W))
    (hΓ : ∀ u v, Γ u v = Γ v u)
    (hH : ∀ u v, H u v = H v u)
    (hmetric : ∀ u v w,
      g (H u v) (F w) + g (F v) (H u w) =
        g (F (Γ u v)) (F w) + g (F v) (F (Γ u w)))
    (hsymm : ∀ Z W : V, g Z W = g W Z)
    (u v : E) : F (Γ u v) = proj (H u v) := by
  let B : E → E → E → ℝ := fun a b c =>
    g (F (Γ a b)) (F c) - g (H a b) (F c)
  have hBsym : ∀ a b c, B a b c = B b a c := by
    intro a b c
    simp only [B, hΓ a b, hH a b]
  have hBskew : ∀ a b c, B a b c = -B a c b := by
    intro a b c
    have hm := hmetric a b c
    dsimp [B]
    rw [hsymm (F b) (H a c), hsymm (F b) (F (Γ a c))] at hm
    linarith
  have horth (w : E) : g (F (Γ u v)) (F w) = g (H u v) (F w) := by
    have hzero := symmetric_skew_tensor_zero B hBsym hBskew u v w
    dsimp [B] at hzero
    linarith
  obtain ⟨w, hw⟩ := hproj u v
  let δ : V := F (Γ u v) - proj (H u v)
  have hδrange : δ = F (Γ u v - w) := by
    simp only [δ, hw, map_sub]
  have hδorth (t : E) : g δ (F t) = 0 := by
    simp only [δ, map_sub, ContinuousLinearMap.sub_apply]
    rw [hadjoint, hfix, horth]
    simp
  have hδzero : g δ δ = 0 := by
    have h := hδorth (Γ u v - w)
    rw [← hδrange] at h
    exact h
  exact sub_eq_zero.mp (hpos δ hδzero)

end QuaternionicSymmetry.GeneralImmersionLeviCivitaProjectionContinuous
