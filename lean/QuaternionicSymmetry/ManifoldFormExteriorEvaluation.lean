import QuaternionicSymmetry.ManifoldEvenClosedAlgebra
import QuaternionicSymmetry.ExteriorContinuousPowers
import QuaternionicSymmetry.EvenForms

/-! Evaluating actual tangent forms in a chart and a linear frame preserves
the normalized wedge product in the genuine exterior algebra. -/
namespace QuaternionicSymmetry.ManifoldFormExteriorEvaluation
open Module ManifoldDifferentialForms ManifoldDeRhamWedge
open ExteriorContinuousPairing ExteriorContinuousWedge
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (p : M) (y : E) (L : E →L[ℝ] E)

def localForm (n : ℕ) : Form 𝓘(ℝ,E) M n →ₗ[ℝ] (E [⋀^Fin n]→L[ℝ] ℝ) where
  toFun α := (inChartModel p α y).compContinuousLinearMap L
  map_add' α β := by ext v; rw [inChartModel_add]; rfl
  map_smul' r α := by ext v; rw [inChartModel_smul]; rfl

def representative (n : ℕ) : Form 𝓘(ℝ,E) M n →ₗ[ℝ] Power E n :=
  (ExteriorContinuousPairing.equiv n).symm.toLinearMap.comp (localForm p y L n)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem representative_pairing (n : ℕ) (α : Form 𝓘(ℝ,E) M n) :
    toContinuous n (representative p y L n α) = localForm p y L n α :=
  (ExteriorContinuousPairing.equiv n).apply_symm_apply _

def value (n : ℕ) : Form 𝓘(ℝ,E) M n →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ E) :=
  (ExteriorAlgebra.exteriorPower ℝ n (Module.Dual ℝ E)).subtype.comp
    (representative p y L n)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem value_cast {m n : ℕ} (h : m = n) (α : Form 𝓘(ℝ,E) M m) :
    value p y L n (castForm h α) = value p y L m α := by
  cases h
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem representative_wedge {m n : ℕ}
    (α : Form 𝓘(ℝ,E) M m) (β : Form 𝓘(ℝ,E) M n) :
    representative p y L (m+n) (formWedge α β) =
      mulPower (representative p y L m α) (representative p y L n β) := by
  apply toContinuous_injective
  rw [toContinuous_mulPower, representative_pairing, representative_pairing,
    representative_pairing]
  change (inChartModel p (formWedge α β) y).compContinuousLinearMap L = _
  rw [inChartModel_formWedge]
  exact ExteriorContinuousPowers.wedge_comp L _ _

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem value_wedge {m n : ℕ}
    (α : Form 𝓘(ℝ,E) M m) (β : Form 𝓘(ℝ,E) M n) :
    value p y L (m+n) (formWedge α β) =
      value p y L m α * value p y L n β :=
  congrArg Subtype.val (representative_wedge p y L α β)

end
end QuaternionicSymmetry.ManifoldFormExteriorEvaluation
