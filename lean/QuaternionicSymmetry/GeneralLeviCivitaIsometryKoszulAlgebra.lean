import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoordinateMetricJet
import QuaternionicSymmetry.GeneralLeviCivitaCoordinateKoszul

/-! Algebraic Koszul cancellation for a metric first jet transported by a
genuine chart isometry. The symmetric second derivative contributes the
inhomogeneous Christoffel transformation term. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulAlgebra

open scoped Manifold ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem koszul_transform_pairing
    (Gs Gt : E → E → ℝ) (Ds Dt : E → E → E → ℝ)
    (Cs Ct : E → E → E) (R : E →L[ℝ] E)
    (S : E →L[ℝ] E →L[ℝ] E)
    (hGtSym : ∀ a b, Gt a b = Gt b a)
    (hGtAdd : ∀ a b c, Gt (a + b) c = Gt a c + Gt b c)
    (hS : ∀ a b, S a b = S b a)
    (hmetric : ∀ a b, Gs a b = Gt (R a) (R b))
    (hjet : ∀ a b c,
      Ds a b c = Dt (R a) (R b) (R c) +
        Gt (S a b) (R c) + Gt (R b) (S a c))
    (hKs : ∀ a b c,
      2 * Gs (Cs a b) c = Ds a b c + Ds b a c - Ds c a b)
    (hKt : ∀ a b c,
      2 * Gt (Ct a b) c = Dt a b c + Dt b a c - Dt c a b)
    (u v w : E) :
    Gs (Cs u v) w = Gt (Ct (R u) (R v) + S u v) (R w) := by
  have hs := hKs u v w
  have ht := hKt (R u) (R v) (R w)
  rw [hmetric, hjet u v w, hjet v u w, hjet w u v] at hs
  rw [hmetric (Cs u v) w, hGtAdd]
  rw [hS v u, hS w u, hS w v,
    hGtSym (R v) (S u w)] at hs
  linarith only [hs, ht]

end
end QuaternionicSymmetry.GeneralLeviCivitaIsometryKoszulAlgebra
