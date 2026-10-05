import QuaternionicSymmetry.GeneralLeviCivitaInvariantEndomorphismJet

/-! At a genuine Riemannian point reflection, the covariant first jets of
an endomorphism field and its reflected field cancel. The exact correction
from the reflection's second chart jet is the Levi-Civita commutator. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaReflectionEndomorphismCancellation

open Filter GeneralLeviCivitaInvariantEndomorphismJet
open scoped Manifold ContDiff Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def covariantEndomorphismJet (Γ : E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (y u v : E) : E :=
  fderiv ℝ A y u v + Γ u (A y v) - A y (Γ u v)

theorem reflected_covariantEndomorphismJet_neg
    (F : E → E) (A B : E → E →L[ℝ] E)
    (Γ : E →L[ℝ] E →L[ℝ] E) (y u v : E)
    (hF : ContDiffAt ℝ 2 F y)
    (hA : DifferentiableAt ℝ A y)
    (hB : DifferentiableAt ℝ B (F y))
    (heq : ∀ᶠ z in 𝓝 y,
      B (F z) ((fderiv ℝ F z) v) = (fderiv ℝ F z) (A z v))
    (hcenter : F y = y)
    (hneg : ∀ w : E, fderiv ℝ F y w = -w)
    (hsecond : ∀ a b : E,
      fderiv ℝ (fderiv ℝ F) y a b = -(Γ a b + Γ a b))
    (hBA : B y = A y) :
    covariantEndomorphismJet Γ A y u v +
      covariantEndomorphismJet Γ B y u v = 0 := by
  have h := endomorphism_intertwining_first_jet F A B y u v hF hA hB heq
  dsimp only at h
  rw [hcenter, hneg u, hneg v, hsecond u v, hBA,
    hneg (fderiv ℝ A y u v)] at h
  rw [hsecond u (A y v)] at h
  simp at h
  calc
    covariantEndomorphismJet Γ A y u v +
        covariantEndomorphismJet Γ B y u v =
      (((fderiv ℝ B y) u) v + -2 • (A y) (Γ u v)) -
        (-2 • Γ u (A y v) + -1 • ((fderiv ℝ A y) u v)) := by
          dsimp only [covariantEndomorphismJet]
          rw [hBA]
          abel
    _ = 0 := by
      apply sub_eq_zero.mpr
      convert h using 1 <;> abel

end
end QuaternionicSymmetry.GeneralLeviCivitaReflectionEndomorphismCancellation
