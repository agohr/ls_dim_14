import QuaternionicSymmetry.ManifoldQuaternionicMetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Genuine infinitesimal isometries of the quaternionic Riemannian metric.
The Killing equation is the vanishing of the metric Lie derivative, tested
on smooth vector fields. No symmetry dimension or section count is a field. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicKillingFields

open ManifoldQuaternionicMetric
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

abbrev SmoothVectorFields :=
  ContMDiffSection 𝓘(ℝ,E) E ∞ (TangentSpace 𝓘(ℝ,E) : M → Type _)

variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The usual tensor formula `(L_X g)(Y,Z)` using the actual manifold
derivative, actual metric and actual Lie brackets. -/
def metricLieDerivative (X Y Z : SmoothVectorFields (E := E) (M := M)) (x : M) : ℝ :=
  (show ℝ from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun y => Q.tangentMetricForm y (Y y) (Z y)) x (X x)) -
    Q.tangentMetricForm x (VectorField.mlieBracket 𝓘(ℝ,E) X Y x) (Z x) -
    Q.tangentMetricForm x (Y x) (VectorField.mlieBracket 𝓘(ℝ,E) X Z x)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem metricLieDerivative_zero (Y Z : SmoothVectorFields (E := E) (M := M)) (x : M) :
    metricLieDerivative Q 0 Y Z x = 0 := by
  simp [metricLieDerivative, ContMDiffSection.coe_zero,
    VectorField.mlieBracket_zero_left]

omit [Nontrivial E] in
theorem metricLieDerivative_add (X X' Y Z : SmoothVectorFields (E := E) (M := M))
    (x : M) : metricLieDerivative Q (X + X') Y Z x =
      metricLieDerivative Q X Y Z x + metricLieDerivative Q X' Y Z x := by
  have hX := (X.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hX' := (X'.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  simp only [metricLieDerivative, ContMDiffSection.coe_add,
    VectorField.mlieBracket_add_left hX hX', Pi.add_apply, map_add,
    ContinuousLinearMap.add_apply]
  ring

omit [Nontrivial E] in
theorem metricLieDerivative_smul (c : ℝ)
    (X Y Z : SmoothVectorFields (E := E) (M := M)) (x : M) :
    metricLieDerivative Q (c • X) Y Z x = c * metricLieDerivative Q X Y Z x := by
  have hX := (X.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  simp only [metricLieDerivative, ContMDiffSection.coe_smul,
    VectorField.mlieBracket_const_smul_left hX, Pi.smul_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Smooth vector fields satisfying the actual metric Killing equation. -/
def killingFields : Submodule ℝ (SmoothVectorFields (E := E) (M := M)) where
  carrier := {X | ∀ Y Z x, metricLieDerivative Q X Y Z x = 0}
  zero_mem' := metricLieDerivative_zero Q
  add_mem' := by
    intro X X' hX hX' Y Z x
    rw [metricLieDerivative_add, hX, hX', add_zero]
  smul_mem' := by
    intro c X hX Y Z x
    rw [metricLieDerivative_smul, hX, mul_zero]

abbrev KillingFields := killingFields Q

/-- The complexification appearing in the cited twistor section/isometry
comparison. The underlying real space is defined by the Killing equation. -/
abbrev ComplexKillingFields := ℂ ⊗[ℝ] KillingFields Q

def killingDimension : ℕ := Module.finrank ℝ (KillingFields Q)

theorem complexKillingFields_finrank :
    Module.finrank ℂ (ComplexKillingFields Q) = killingDimension Q := by
  letI : Module.Free ℝ (KillingFields Q) := Module.Free.of_divisionRing ℝ _
  exact Module.finrank_baseChange

end
end QuaternionicSymmetry.ManifoldQuaternionicKillingFields
