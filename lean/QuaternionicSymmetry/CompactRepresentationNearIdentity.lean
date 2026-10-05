import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Normed

/-! A uniformly small representation is trivial: averaging over a
probability left-Haar measure gives an invertible invariant operator.
This general analytic lemma supports local constancy of isotropy on
the quaternionic bundle without assuming character multiplicities. -/

namespace QuaternionicSymmetry.CompactRepresentationNearIdentity

open MeasureTheory MeasureTheory.Measure
noncomputable section

variable {G A : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {μ : Measure G} [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]

theorem representation_eq_one_of_uniform_small
    (ρ : G →* A) (hρ : Integrable (fun g => ρ g) μ)
    {c : ℝ} (hc : c < 1) (hsmall : ∀ g, ‖ρ g - 1‖ ≤ c) :
    ∀ g, ρ g = 1 := by
  let B : A := ∫ g, ρ g ∂μ
  have hclose : ‖B - 1‖ ≤ c := by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (C := c) (f := fun g => ρ g - 1)
      (Filter.Eventually.of_forall hsmall)
    simpa only [integral_sub hρ (integrable_const (1 : A)),
      integral_const, probReal_univ, one_smul, mul_one, B] using h
  have hunit : IsUnit B := by
    have h := isUnit_one_sub_of_norm_lt_one
      (x := (1 : A) - B) (by rw [norm_sub_rev]; exact hclose.trans_lt hc)
    simpa using h
  have hinvariant (g : G) : ρ g * B = B := by
    change ρ g * (∫ h, ρ h ∂μ) = ∫ h, ρ h ∂μ
    rw [← integral_const_mul_of_integrable hρ]
    simpa only [← map_mul] using integral_mul_left_eq_self (μ := μ) (fun h => ρ h) g
  intro g
  obtain ⟨u, hu⟩ := hunit
  have h := hinvariant g
  rw [← hu] at h
  have hcanc := congrArg (fun a : A => a * ↑u⁻¹) h
  simpa [mul_assoc] using hcanc

end
end QuaternionicSymmetry.CompactRepresentationNearIdentity
