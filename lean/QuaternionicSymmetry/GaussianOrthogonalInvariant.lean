import QuaternionicSymmetry.GaussianAlgebra
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
  Orthogonal changes of finite real coordinates preserve the actual product
  standard Gaussian measure.
-/

namespace QuaternionicSymmetry.GaussianOrthogonalInvariant

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The coordinate change associated to a real matrix. -/
def transform (U : Matrix β β ℝ) : (β → ℝ) → β → ℝ :=
  fun x i => ∑ j, U i j * x j

omit [DecidableEq β] in
private theorem transform_eq_mulVec (U : Matrix β β ℝ) (x : β → ℝ) :
    transform U x = U.mulVec x := by
  ext i
  rfl

private instance standard_isProbabilityMeasure :
    IsProbabilityMeasure (GaussianAlgebra.standardMeasure (ι := β)) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : β => gaussianReal 0 1))
  infer_instance

omit [DecidableEq β] in
private theorem coordinate_hasGaussianLaw (i : β) :
    HasGaussianLaw (fun x : β → ℝ => x i) GaussianAlgebra.standardMeasure := by
  exact (measurePreserving_eval (fun _ : β => gaussianReal 0 1) i).hasLaw.hasGaussianLaw

omit [DecidableEq β] in
private theorem coordinate_memLp_two (i : β) :
    MemLp (fun x : β → ℝ => x i) 2 GaussianAlgebra.standardMeasure :=
  (coordinate_hasGaussianLaw i).memLp_two

omit [DecidableEq β] in
private theorem coordinate_mean (i : β) :
    (∫ x : β → ℝ, x i ∂GaussianAlgebra.standardMeasure) = 0 := by
  unfold GaussianAlgebra.standardMeasure
  rw [show (fun x : β → ℝ => x i) = fun x => x i ^ 1 by
    funext x
    simp]
  rw [GaussianCombination.integral_pow_of_hasLaw
    (measurePreserving_eval (fun _ : β => gaussianReal 0 1) i).hasLaw]
  exact GaussianMoments.integral_odd_1 (1 : ℝ≥0)

private theorem coordinate_covariance (i j : β) :
    cov[(fun x : β → ℝ => x i), (fun x : β → ℝ => x j);
      GaussianAlgebra.standardMeasure] = if i = j then 1 else 0 := by
  rw [covariance_eq_sub (coordinate_memLp_two i) (coordinate_memLp_two j),
    coordinate_mean, coordinate_mean]
  change (∫ x : β → ℝ, x i * x j ∂GaussianAlgebra.standardMeasure) - 0 * 0 = _
  rw [GaussianAlgebra.coordinate_integral_mul]
  simp

private def transformLinear (U : Matrix β β ℝ) :
    (β → ℝ) →L[ℝ] (β → ℝ) :=
  ContinuousLinearMap.mk (Matrix.toLin' U)
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' U))

private theorem transformLinear_apply (U : Matrix β β ℝ) (x : β → ℝ) :
    transformLinear U x = transform U x := by
  change (Matrix.toLin' U) x = transform U x
  rw [Matrix.toLin'_apply, transform_eq_mulVec]

omit [DecidableEq β] in
private theorem input_joint_gaussian :
    HasGaussianLaw (fun x : β → ℝ => x) GaussianAlgebra.standardMeasure := by
  apply iIndepFun.hasGaussianLaw
  · exact coordinate_hasGaussianLaw
  · simpa [GaussianAlgebra.standardMeasure] using
      (iIndepFun_pi (μ := fun _ : β => gaussianReal 0 1)
        (X := fun _ x => x) (fun _ => aemeasurable_id))

private theorem transform_joint_gaussian (U : Matrix β β ℝ) :
    HasGaussianLaw (transform U) GaussianAlgebra.standardMeasure := by
  have h := input_joint_gaussian.map (transformLinear U)
  simpa only [Function.comp_apply, transformLinear_apply] using h

private theorem transform_coordinate_hasLaw (U : Matrix β β ℝ)
    (hU : ∀ i j, ∑ k, U i k * U j k = if i = j then 1 else 0) (i : β) :
    HasLaw (fun x : β → ℝ => transform U x i) (gaussianReal 0 1)
      GaussianAlgebra.standardMeasure := by
  have h := GaussianCombination.product_combination_hasLaw (U i)
  rw [show (fun x : β → ℝ => transform U x i) =
      GaussianCombination.combination (U i) (fun j x => x j) by
        funext x
        simp [transform, GaussianCombination.combination]]
  have hvar : GaussianCombination.variance (U i) = 1 := by
    ext
    simpa [GaussianCombination.variance, pow_two] using hU i i
  simpa [hvar] using h

private theorem transform_covariance (U : Matrix β β ℝ)
    (hU : ∀ i j, ∑ k, U i k * U j k = if i = j then 1 else 0) (i j : β) :
    cov[(fun x : β → ℝ => transform U x i), (fun x : β → ℝ => transform U x j);
      GaussianAlgebra.standardMeasure] = if i = j then 1 else 0 := by
  change cov[(fun x : β → ℝ => ∑ k, U i k * x k),
    (fun x : β → ℝ => ∑ l, U j l * x l); GaussianAlgebra.standardMeasure] = _
  rw [covariance_fun_sum_fun_sum
    (fun k => (coordinate_memLp_two k).const_mul (U i k))
    (fun l => (coordinate_memLp_two l).const_mul (U j l))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, coordinate_covariance]
  calc
    _ = ∑ k, U i k * (∑ l, U j l * (if k = l then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ k, U i k * U j k := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [show (fun l => U j l * (if k = l then 1 else 0)) =
          (fun l => if l = k then U j l else 0) by
            funext l
            by_cases h : l = k
            · subst l
              simp
            · have h' : k ≠ l := fun hkl => h hkl.symm
              simp [h, h']]
      simp
    _ = _ := hU i j

/-- An orthogonal real matrix preserves the finite standard Gaussian product measure. -/
theorem map_transform_standardMeasure (U : Matrix β β ℝ)
    (hU : ∀ i j, ∑ k, U i k * U j k = if i = j then 1 else 0) :
    Measure.map (transform U) GaussianAlgebra.standardMeasure = GaussianAlgebra.standardMeasure := by
  have hgauss := transform_joint_gaussian U
  have hindep : iIndepFun (fun i x => transform U x i) GaussianAlgebra.standardMeasure := by
    apply hgauss.iIndepFun_of_covariance_eq_zero
    intro i j hij
    rw [transform_covariance U hU i j, if_neg hij]
  calc
    Measure.map (transform U) GaussianAlgebra.standardMeasure =
        Measure.pi (fun i => Measure.map (fun x : β → ℝ => transform U x i)
          GaussianAlgebra.standardMeasure) := by
      exact (iIndepFun_iff_map_fun_eq_pi_map
        (fun i => (transform_coordinate_hasLaw U hU i).aemeasurable)).1 hindep
    _ = Measure.pi (fun _ : β => gaussianReal 0 1) := by
      congr 1
      funext i
      exact (transform_coordinate_hasLaw U hU i).map_eq
    _ = GaussianAlgebra.standardMeasure := rfl

end
end QuaternionicSymmetry.GaussianOrthogonalInvariant
