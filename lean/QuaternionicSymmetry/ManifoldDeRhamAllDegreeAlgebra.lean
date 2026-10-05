import QuaternionicSymmetry.ManifoldDeRhamAllDegrees
import QuaternionicSymmetry.ContinuousWedgeZeroComm

/-! Algebra laws for the normalized wedge in every form degree. -/

namespace QuaternionicSymmetry.ManifoldDeRhamAllDegreeAlgebra

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamWedge
  QuaternionicSymmetry.ManifoldDeRhamRing
  QuaternionicSymmetry.ManifoldDeRhamAllDegrees
  QuaternionicSymmetry.ContinuousWedgeZeroComm
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem castForm_apply {m n : ℕ} (h : m = n)
    (α : Form 𝓘(ℝ, E) M m) (x : M)
    (v : Fin n → TangentSpace 𝓘(ℝ, E) x) :
    castForm h α x v = α x (v ∘ finCongr h) := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem formWedge_zero_swap {p : ℕ}
    (α : Form 𝓘(ℝ, E) M p)
    (β : Form 𝓘(ℝ, E) M 0) :
    castForm (Nat.zero_add p) (formWedge β α) =
      formWedge α β := by
  funext x
  ext v
  rw [castForm_apply]
  change ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
      (β x) (α x) (v ∘ finCongr (Nat.zero_add p)) =
    ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ) (α x) (β x) v
  simpa only [QuaternionicSymmetry.ContinuousWedgeUnit.castAlt_apply] using
    congrArg (fun f => f v) (wedge_zero_swap (α x) (β x))

theorem closedWedgeAll_assoc {p q r : ℕ}
    (α : closedForms (E := E) (M₀ := M) p)
    (β : closedForms (E := E) (M₀ := M) q)
    (γ : closedForms (E := E) (M₀ := M) r) :
    castClosedDegree (Nat.add_assoc p q r)
      (closedWedgeAll (closedWedgeAll α β) γ) =
        closedWedgeAll α (closedWedgeAll β γ) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [castClosedDegree_form]
  exact formWedge_assoc α.1.1 β.1.1 γ.1.1

end QuaternionicSymmetry.ManifoldDeRhamAllDegreeAlgebra
