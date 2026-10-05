import QuaternionicSymmetry.QuaternionicStructure
import QuaternionicSymmetry.AlgebraicLeviCivitaUniqueness

/-! The algebraic vanishing of a quaternionic second fundamental form.
A symmetric normal-valued form whose quaternionic covariance holds modulo
the tangent image must vanish. -/
namespace QuaternionicSymmetry.QuaternionicSecondFundamentalAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma normal_covariance_of_tangent_defect
    (A : F → E) (H : F → F → E) (J : E → E) (j : F → F)
    (hskew : ∀ v w, inner ℝ (J v) w = -inner ℝ v (J w))
    (hinter : ∀ w, J (A w) = A (j w))
    (hnormal : ∀ u v w, inner ℝ (H u v) (A w) = 0)
    (hdefect : ∀ u v, ∃ w, H u (j v) - J (H u v) = A w)
    (u v : F) : H u (j v) = J (H u v) := by
  obtain ⟨w, hw⟩ := hdefect u v
  have hzero : inner ℝ (H u (j v) - J (H u v)) (A w) = 0 := by
    rw [inner_sub_left, hnormal, hskew, hinter, hnormal]
    ring
  rw [← hw] at hzero
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hzero)

/-- Symmetry and covariance under two anticommuting invertible target
complex structures leave no nonzero normal second fundamental form. -/
theorem secondFundamental_zero
    (Q : QuaternionicStructure E) (A : F → E) (H : F → F → E)
    (i j : F → F)
    (hsymm : ∀ u v, H u v = H v u)
    (hnormal : ∀ u v w, inner ℝ (H u v) (A w) = 0)
    (hI : ∀ w, Q.I (A w) = A (i w))
    (hJ : ∀ w, Q.J (A w) = A (j w))
    (hdI : ∀ u v, ∃ w, H u (i v) - Q.I (H u v) = A w)
    (hdJ : ∀ u v, ∃ w, H u (j v) - Q.J (H u v) = A w)
    (u v : F) : H u v = 0 := by
  have hcovI := normal_covariance_of_tangent_defect A H Q.I i Q.I_skew hI hnormal hdI
  have hcovJ := normal_covariance_of_tangent_defect A H Q.J j Q.J_skew hJ hnormal hdJ
  have hleftI (a b : F) : H (i a) b = Q.I (H a b) := by
    rw [hsymm, hcovI, hsymm b a]
  have hleftJ (a b : F) : H (j a) b = Q.J (H a b) := by
    rw [hsymm, hcovJ, hsymm b a]
  have hcomm : Q.I (Q.J (H u v)) = Q.J (Q.I (H u v)) := by
    rw [← hcovJ, ← hleftI, hcovJ, hleftI]
  have hneg : Q.I (Q.J (H u v)) = -Q.I (Q.J (H u v)) :=
    hcomm.trans (Q.J_I_anti _)
  have hz : Q.I (Q.J (H u v)) = 0 := by
    have hinner := congrArg (fun z => inner ℝ z (Q.I (Q.J (H u v)))) hneg
    simp only [inner_neg_left] at hinner
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    linarith
  apply Q.J.injective
  apply Q.I.injective
  simpa using hz

/-- The metric and torsion identities give normality by the elementary
symmetric/skew tensor argument. -/
theorem normal_of_metric_and_symmetry
    (A : F → E) (H : F → F → E)
    (hsymm : ∀ u v, H u v = H v u)
    (hmetric : ∀ u v w,
      inner ℝ (H u v) (A w) + inner ℝ (A v) (H u w) = 0)
    (u v w : F) : inner ℝ (H u v) (A w) = 0 := by
  apply AlgebraicLeviCivitaUniqueness.symmetric_skew_tensor_zero
    (fun a b c => inner ℝ (H a b) (A c))
  · intro a b c
    rw [hsymm a b]
  · intro a b c
    have h := hmetric a b c
    rw [← real_inner_comm (A b) (H a c)] at h
    linarith

end QuaternionicSymmetry.QuaternionicSecondFundamentalAlgebra
