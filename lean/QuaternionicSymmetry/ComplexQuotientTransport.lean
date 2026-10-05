import QuaternionicSymmetry.HorizontalQuotientTransport
import Mathlib.Analysis.Complex.Basic

/-! An identity-induced quotient equivalence is complex linear when the two
quotient complex structures are induced by the same real tangent operator.
This statement is independent of the twistor bundle constructions. -/

namespace QuaternionicSymmetry.ComplexQuotientTransport
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (P Q : Submodule ℝ V)
  [Module ℂ (V ⧸ P)] [Module ℂ (V ⧸ Q)]
  [IsScalarTower ℝ ℂ (V ⧸ P)] [IsScalarTower ℝ ℂ (V ⧸ Q)]
  (h : ∀ v : V, v ∈ P ↔ v ∈ Q)
  (J : V →ₗ[ℝ] V)
  (hP : ∀ v : V, Complex.I • (Submodule.Quotient.mk v : V ⧸ P) =
    Submodule.Quotient.mk (J v))
  (hQ : ∀ v : V, Complex.I • (Submodule.Quotient.mk v : V ⧸ Q) =
    Submodule.Quotient.mk (J v))

theorem equiv_map_i
    (J : V →ₗ[ℝ] V)
    (hP : ∀ v : V, Complex.I • (Submodule.Quotient.mk v : V ⧸ P) =
      Submodule.Quotient.mk (J v))
    (hQ : ∀ v : V, Complex.I • (Submodule.Quotient.mk v : V ⧸ Q) =
      Submodule.Quotient.mk (J v)) (v : V ⧸ P) :
    HorizontalQuotientTransport.equiv P Q h (Complex.I • v) =
      Complex.I • HorizontalQuotientTransport.equiv P Q h v := by
  induction v using Quotient.inductionOn' with
  | h v =>
    change HorizontalQuotientTransport.equiv P Q h
        (Complex.I • (Submodule.Quotient.mk v : V ⧸ P)) =
      Complex.I • HorizontalQuotientTransport.equiv P Q h
        (Submodule.Quotient.mk v)
    rw [hP v, HorizontalQuotientTransport.equiv_mk,
      HorizontalQuotientTransport.equiv_mk, hQ v]

def complexEquiv : (V ⧸ P) ≃ₗ[ℂ] (V ⧸ Q) := by
  let f := HorizontalQuotientTransport.equiv P Q h
  exact {
    f with
    map_smul' := by
      intro c v
      change f (c • v) = c • f v
      rw [← Complex.re_add_im c]
      simp only [add_smul, map_add, mul_smul]
      have hreal (r : ℝ) (x : V ⧸ P) :
          f ((r : ℂ) • x) = (r : ℂ) • f x := by
        change f ((algebraMap ℝ ℂ) r • x) = (algebraMap ℝ ℂ) r • f x
        rw [IsScalarTower.algebraMap_smul ℂ r x,
          IsScalarTower.algebraMap_smul ℂ r (f x)]
        exact f.map_smul r x
      rw [hreal c.re v, hreal c.im (Complex.I • v),
        equiv_map_i P Q h J hP hQ v]
  }

end
end QuaternionicSymmetry.ComplexQuotientTransport
