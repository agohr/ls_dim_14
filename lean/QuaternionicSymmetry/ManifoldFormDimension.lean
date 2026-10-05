import QuaternionicSymmetry.ManifoldDifferentialForms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Genuine manifold forms vanish above the model dimension. In particular,
every top-degree form is closed for the constructed exterior derivative. -/
namespace QuaternionicSymmetry.ManifoldFormDimension

open Module ManifoldDifferentialForms
open scoped Manifold ContDiff Topology
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem form_eq_zero_of_degree_gt {n : ℕ} (α : Form 𝓘(ℝ, E) M n)
    (hn : Module.finrank ℝ E < n) : α = 0 := by
  funext x
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) := by
    change FiniteDimensional ℝ E
    infer_instance
  ext v
  apply (α x).toAlternatingMap.map_linearDependent
  intro hv
  have h := hv.fintype_card_le_finrank
  change Fintype.card (Fin n) ≤ Module.finrank ℝ E at h
  simp only [Fintype.card_fin] at h
  omega

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem top_form_closed (α : Form 𝓘(ℝ, E) M (Module.finrank ℝ E)) :
    exteriorDerivative α = 0 :=
  form_eq_zero_of_degree_gt _ (Nat.lt_succ_self _)

end QuaternionicSymmetry.ManifoldFormDimension
