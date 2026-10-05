import QuaternionicSymmetry.OrbitalHaarCoefficientExtraction
import Mathlib.Analysis.Analytic.Uniqueness

/-!
The spectral quotient only needs to be supplied for positive parameters.
Analytic continuation proves the cross-multiplied identity at every real
parameter, including zero, before extracting its Taylor coefficients.
-/

namespace QuaternionicSymmetry.OrbitalHaarPositiveParameter

open Matrix MeasureTheory CompactSymplecticHaar OrbitalAnalyticOddKernel
  OrbitalOddDeterminantBase OrbitalHaarCoefficientExtraction
open scoped Topology

noncomputable section

theorem analyticAt_sourceDeterminant {n : ℕ} (x y : Fin n → ℚ) (t : ℝ) :
    AnalyticAt ℝ (sourceDeterminant x y : ℝ → ℝ) t := by
  have hfun : (sourceDeterminant x y : ℝ → ℝ) = fun s =>
      (Matrix.of fun i j => Real.exp ((x i : ℝ) * (y j : ℝ) * s) -
        Real.exp (-((x i : ℝ) * (y j : ℝ)) * s)).det := by
    funext s
    rw [sourceDeterminant_apply]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Real.sinh_eq, neg_mul]
    ring
  rw [hfun]
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (analyticAt_rexp.comp
    (analyticAt_const.mul analyticAt_id)).sub
    (analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A positive-parameter spectral quotient determines all real parameters
after cross multiplication. No value at a zero denominator is assumed. -/
theorem cross_multiplied_of_positive_quotient {n : ℕ} (x y : Fin n → ℚ)
    (J B X : Matrix κ κ ℂ)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0)
    (hquotient : ∀ t : ℝ, 0 < t → exponentialIntegral J B X t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t /
        (t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ))) :
    ∀ t : ℝ,
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        exponentialIntegral J B X t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t := by
  have hleft : AnalyticOnNhd ℝ (fun t : ℝ =>
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        exponentialIntegral J B X t) Set.univ := by
    intro t _
    exact ((analyticAt_id.pow _).mul analyticAt_const).mul
      (analyticAt_exponentialIntegral J B X t)
  have hright : AnalyticOnNhd ℝ (fun t : ℝ =>
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t) Set.univ :=
    fun t _ => analyticAt_const.mul (analyticAt_sourceDeterminant x y t)
  have heq : (fun t : ℝ =>
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        exponentialIntegral J B X t) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)]
      with t ht
    rw [hquotient t ht]
    have hden : t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (ne_of_gt ht)) (by exact_mod_cast hΔ)
    exact mul_div_cancel₀ _ hden
  exact congrFun (hleft.eq_of_eventuallyEq hright heq)

theorem coefficient_of_positive_quotient {n : ℕ} (x y : Fin n → ℚ)
    (J B X : Matrix κ κ ℂ)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0)
    (hquotient : ∀ t : ℝ, 0 < t → exponentialIntegral J B X t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t /
        (t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ)))
    (k : ℕ) :
    ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
        (evenMoment J B X k / ((2 * k).factorial : ℝ)) =
      (sourceConstant n : ℝ) *
        ((PowerSeries.coeff (n ^ 2 + 2 * k)
          (OrbitalOddFormalKernel.sourceFullFormalOddKernel x y).det : ℚ) : ℝ) :=
  coefficient_of_cross_multiplied_identity x y J B X
    (cross_multiplied_of_positive_quotient x y J B X hΔ hquotient) k

end
end QuaternionicSymmetry.OrbitalHaarPositiveParameter
