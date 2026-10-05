import QuaternionicSymmetry.CompactRepresentationTrivialLocus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The connected-family triviality theorem with its probability Haar
measure and integrability hypotheses discharged internally. -/

namespace QuaternionicSymmetry.CompactRepresentationTriviality

open MeasureTheory MeasureTheory.Measure
open CompactRepresentationTrivialLocus
noncomputable section

variable {G A X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [TopologicalSpace X]

def probability : Measure G := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure (probability (G := G)) where
  measure_univ := Measure.haarMeasure_self

instance : IsHaarMeasure (probability (G := G)) := by
  unfold probability
  infer_instance

omit [T2Space G] [MeasurableMul G] [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem integrable_family (ρ : X → G →* A)
    (hρ : Continuous (fun p : G × X => ρ p.2 p.1)) (x : X) :
    Integrable (fun g => ρ x g) (probability (G := G)) := by
  have hcont : Continuous (fun g => ρ x g) :=
    hρ.comp (continuous_id.prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport
    (isClosed_tsupport (fun g => ρ x g)).isCompact

theorem trivial_everywhere [PreconnectedSpace X]
    (ρ : X → G →* A)
    (hρ : Continuous (fun p : G × X => ρ p.2 p.1))
    (x₀ : X) (hx₀ : ∀ g, ρ x₀ g = 1) : ∀ x g, ρ x g = 1 :=
  trivial_everywhere_of_trivial_at (μ := probability (G := G))
    ρ hρ (integrable_family ρ hρ) x₀ hx₀

end
end QuaternionicSymmetry.CompactRepresentationTriviality
