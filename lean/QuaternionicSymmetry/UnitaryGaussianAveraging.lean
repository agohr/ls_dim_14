import QuaternionicSymmetry.UnitaryRadialAverage
import QuaternionicSymmetry.ComplexGaussianLawMoments
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini's theorem compares homogeneous Haar averages with Gaussian moments.
Integrability follows from Gaussian unitary invariance. -/

namespace QuaternionicSymmetry.UnitaryGaussianAveraging

open Matrix MeasureTheory ComplexGaussianUnitaryInvariant
open scoped BigOperators

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

instance gaussian_isProbabilityMeasure :
    IsProbabilityMeasure (standardMeasure (κ := κ)) :=
  GaussianProductCurry.vector_hasLaw.isProbabilityMeasure_iff.mp inferInstance

theorem continuous_action : Continuous
    (fun p : Matrix.unitaryGroup κ ℂ × (κ → ℂ) => (p.1 : Matrix κ κ ℂ) *ᵥ p.2) := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finset_sum
  intro j _
  have hv : Continuous (fun p : Matrix.unitaryGroup κ ℂ × (κ → ℂ) =>
      (p.1 : Matrix κ κ ℂ)) := continuous_subtype_val.comp continuous_fst
  exact ((continuous_apply j).comp ((continuous_apply i).comp hv)).mul
    ((continuous_apply j).comp continuous_snd)

theorem integrable_action (f : (κ → ℂ) → ℝ) (hc : Continuous f)
    (hi : Integrable f standardMeasure) :
    Integrable
      (fun p : Matrix.unitaryGroup κ ℂ × (κ → ℂ) => f ((p.1 : Matrix κ κ ℂ) *ᵥ p.2))
      (UnitaryHaarMeasure.probability.prod standardMeasure) := by
  apply (integrable_prod_iff (hc.comp continuous_action).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro U
    have hm := map_mulVec_standardMeasure (U : Matrix κ κ ℂ)
      (Matrix.mem_unitaryGroup_iff.mp U.property)
    have hmc : Continuous (fun z : κ → ℂ => (U : Matrix κ κ ℂ) *ᵥ z) :=
      continuous_action.comp (continuous_const.prodMk continuous_id)
    apply (integrable_map_measure hc.aestronglyMeasurable hmc.measurable.aemeasurable).mp
    rwa [hm]
  · have he (U : Matrix.unitaryGroup κ ℂ) :
        (∫ z, ‖f ((U : Matrix κ κ ℂ) *ᵥ z)‖ ∂standardMeasure) =
          ∫ z, ‖f z‖ ∂standardMeasure :=
      integral_mulVec_standardMeasure (U : Matrix κ κ ℂ)
        (Matrix.mem_unitaryGroup_iff.mp U.property) (fun z => ‖f z‖)
        hc.norm.aestronglyMeasurable
    change Integrable (fun U : Matrix.unitaryGroup κ ℂ =>
      ∫ z, ‖f ((U : Matrix κ κ ℂ) *ᵥ z)‖ ∂standardMeasure) _
    simp_rw [he]
    exact integrable_const _

theorem integral_average (f : (κ → ℂ) → ℝ) (hc : Continuous f)
    (hi : Integrable f standardMeasure) :
    (∫ z, (∫ U : Matrix.unitaryGroup κ ℂ, f ((U : Matrix κ κ ℂ) *ᵥ z)
      ∂UnitaryHaarMeasure.probability) ∂standardMeasure) =
        ∫ z, f z ∂standardMeasure := by
  rw [← integral_integral_swap (integrable_action f hc hi)]
  have he (U : Matrix.unitaryGroup κ ℂ) :
      (∫ z, f ((U : Matrix κ κ ℂ) *ᵥ z) ∂standardMeasure) =
        ∫ z, f z ∂standardMeasure :=
    integral_mulVec_standardMeasure (U : Matrix κ κ ℂ)
      (Matrix.mem_unitaryGroup_iff.mp U.property) f hc.aestronglyMeasurable
  simp_rw [he]
  simp

theorem radial_moment_mul_average (f : (κ → ℂ) → ℝ) (k : ℕ)
    (hc : Continuous f) (hi : Integrable f standardMeasure)
    (hf : ∀ (r : ℝ), 0 ≤ r → ∀ z : κ → ℂ, f (r • z) = r ^ (2 * k) * f z)
    (i₀ : κ) :
    ((Fintype.card κ).ascFactorial k : ℝ) *
      (∫ U : Matrix.unitaryGroup κ ℂ,
        f ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1) ∂UnitaryHaarMeasure.probability) =
      ∫ z, f z ∂standardMeasure := by
  have he (z : κ → ℂ) :
      (∫ U : Matrix.unitaryGroup κ ℂ, f ((U : Matrix κ κ ℂ) *ᵥ z)
        ∂UnitaryHaarMeasure.probability) =
      (∑ i, ‖z i‖ ^ 2) ^ k *
        (∫ U : Matrix.unitaryGroup κ ℂ,
          f ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1) ∂UnitaryHaarMeasure.probability) := by
    simpa only [pow_mul, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply] using
      UnitaryRadialAverage.integral_homogeneous f (2 * k) hf (WithLp.toLp 2 z) i₀
  calc
    _ = ∫ z : κ → ℂ, (∑ i, ‖z i‖ ^ 2) ^ k *
        (∫ U : Matrix.unitaryGroup κ ℂ,
          f ((U : Matrix κ κ ℂ) *ᵥ Pi.single i₀ 1) ∂UnitaryHaarMeasure.probability)
        ∂standardMeasure := by
      rw [integral_mul_const, ComplexGaussianLawMoments.integral_radial_pow]
    _ = ∫ z, (∫ U : Matrix.unitaryGroup κ ℂ, f ((U : Matrix κ κ ℂ) *ᵥ z)
        ∂UnitaryHaarMeasure.probability) ∂standardMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => (he z).symm)
    _ = _ := integral_average f hc hi

end
end QuaternionicSymmetry.UnitaryGaussianAveraging
