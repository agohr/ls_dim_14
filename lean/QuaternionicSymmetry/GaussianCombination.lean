import QuaternionicSymmetry.GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Scalar Wick moments for finite Gaussian combinations

This file concerns ordinary real-valued random variables.  It proves that a
finite linear combination of independent centred standard Gaussians has the
Gaussian law with variance the sum of squared coefficients, and transfers the
second through eighth moments from `GaussianMoments`.
-/

namespace QuaternionicSymmetry.GaussianCombination

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Fintype ι] [DecidableEq ι]

/-- The nonnegative variance of a real coefficient family. -/
def variance (t : ι → ℝ) : ℝ≥0 :=
  ⟨∑ i, t i ^ 2, Finset.sum_nonneg fun i _ ↦ sq_nonneg (t i)⟩

/-- The finite real linear combination of coordinate random variables. -/
def combination (t : ι → ℝ) (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ i, t i * X i ω

/-- A partial version used for the induction proving the Gaussian law. -/
def partialCombination (s : Finset ι) (t : ι → ℝ) (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ s, t i * X i ω

def partialVariance (s : Finset ι) (t : ι → ℝ) : ℝ≥0 :=
  ⟨∑ i ∈ s, t i ^ 2, Finset.sum_nonneg fun i _ ↦ sq_nonneg (t i)⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem partialVariance_empty (t : ι → ℝ) : partialVariance ∅ t = 0 := by
  ext
  simp [partialVariance]

omit [Fintype ι] in
private theorem partialVariance_insert {s : Finset ι} {i : ι} (hi : i ∉ s) (t : ι → ℝ) :
    partialVariance (insert i s) t = ⟨t i ^ 2, sq_nonneg (t i)⟩ + partialVariance s t := by
  ext
  simp [partialVariance, Finset.sum_insert, hi]

omit [DecidableEq ι] in
private theorem partialVariance_univ (t : ι → ℝ) : partialVariance Finset.univ t = variance t := by
  rfl

/-- The integral of a power transfers along an explicitly supplied law. -/
theorem integral_pow_of_hasLaw {Y : Ω → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P) (n : ℕ) :
    (∫ ω, Y ω ^ n ∂P) = ∫ x : ℝ, x ^ n ∂gaussianReal 0 v := by
  simpa only [Function.comp_apply] using
    hY.integral_comp (f := fun x : ℝ ↦ x ^ n) (by fun_prop)

omit [Fintype ι] in
theorem partial_hasLaw_standard_sum [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) (s : Finset ι) :
    HasLaw (partialCombination s t X) (gaussianReal 0 (partialVariance s t)) P := by
  let Z : ι → Ω → ℝ := fun i ω ↦ t i * X i ω
  have hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 ⟨t i ^ 2, sq_nonneg (t i)⟩) P := by
    intro i
    simpa [Z] using gaussianReal_const_mul (hX i) (t i)
  have hZIndep : iIndepFun Z P := by
    exact hIndep.comp (fun i x ↦ t i * x) (fun _ ↦ by fun_prop)
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_⟩
      · change AEMeasurable (fun _ : Ω ↦ (0 : ℝ)) P
        fun_prop
      · change Measure.map (fun _ : Ω ↦ (0 : ℝ)) P =
          gaussianReal 0 (partialVariance ∅ t)
        rw [partialVariance_empty, gaussianReal_zero_var]
        rw [Measure.map_const, measure_univ]
        simp
  | insert i s hi hs =>
      have hsumIndep : IndepFun (partialCombination s t X) (Z i) P := by
        have h := hZIndep.indepFun_finset₀ s {i} (Finset.disjoint_singleton_right.2 hi)
          (fun j ↦ (hZ j).aemeasurable)
        let sumOnSubtype : ({j // j ∈ s} → ℝ) → ℝ := fun q ↦ ∑ j, q j
        let sumOnSingleton : ({j // j ∈ ({i} : Finset ι)} → ℝ) → ℝ := fun q ↦ ∑ j, q j
        have h' := h.comp (φ := sumOnSubtype) (ψ := sumOnSingleton) (by fun_prop) (by fun_prop)
        convert h' using 1
        · ext ω
          simp only [Function.comp_apply, sumOnSubtype, partialCombination, Z]
          exact (Finset.sum_attach s fun j ↦ t j * X j ω).symm
        · ext ω
          simp [Function.comp_apply, sumOnSingleton, Z]
      have hadd := gaussianReal_add_gaussianReal_of_indepFun hsumIndep hs.map_eq (hZ i).map_eq
      have hcomb : partialCombination (insert i s) t X = partialCombination s t X + Z i := by
        ext ω
        change (∑ x ∈ insert i s, t x * X x ω) =
          (∑ x ∈ s, t x * X x ω) + t i * X i ω
        rw [Finset.sum_insert hi]
        ac_rfl
      refine ⟨?_, ?_⟩
      · rw [hcomb]
        exact hs.aemeasurable.add (hZ i).aemeasurable
      · rw [hcomb, partialVariance_insert hi t]
        simpa [add_comm] using hadd

/-- A finite independent standard-Gaussian combination has the stated law. -/
theorem combination_hasLaw_standard_sum [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) :
    HasLaw (combination t X) (gaussianReal 0 (variance t)) P := by
  simpa [combination, partialCombination, partialVariance_univ] using
    partial_hasLaw_standard_sum t X hX hIndep Finset.univ

theorem combination_square [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) :
    (∫ ω, combination t X ω ^ 2 ∂P) = (variance t : ℝ) := by
  rw [integral_pow_of_hasLaw (combination_hasLaw_standard_sum t X hX hIndep)]
  exact GaussianMoments.integral_square _

theorem combination_fourth [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) :
    (∫ ω, combination t X ω ^ 4 ∂P) = 3 * (variance t : ℝ) ^ 2 := by
  rw [integral_pow_of_hasLaw (combination_hasLaw_standard_sum t X hX hIndep)]
  exact GaussianMoments.integral_fourth _

theorem combination_sixth [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) :
    (∫ ω, combination t X ω ^ 6 ∂P) = 15 * (variance t : ℝ) ^ 3 := by
  rw [integral_pow_of_hasLaw (combination_hasLaw_standard_sum t X hX hIndep)]
  exact GaussianMoments.integral_sixth _

theorem combination_eighth [IsProbabilityMeasure P]
    (t : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P)
    (hIndep : iIndepFun X P) :
    (∫ ω, combination t X ω ^ 8 ∂P) = 105 * (variance t : ℝ) ^ 4 := by
  rw [integral_pow_of_hasLaw (combination_hasLaw_standard_sum t X hX hIndep)]
  exact GaussianMoments.integral_eighth _

/-- The actual finite product of standard Gaussian measures supplies independent coordinates. -/
theorem product_combination_hasLaw (t : ι → ℝ) :
    HasLaw (combination t (fun i (ω : ι → ℝ) ↦ ω i))
      (gaussianReal 0 (variance t))
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  let μ : ι → Measure ℝ := fun _ ↦ gaussianReal 0 1
  have hX : ∀ i, HasLaw (fun ω : ι → ℝ ↦ ω i) (gaussianReal 0 1) (Measure.pi μ) := by
    intro i
    exact (measurePreserving_eval μ i).hasLaw
  have hIndep : iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) (Measure.pi μ) := by
    simpa using (iIndepFun_pi (μ := μ) (X := fun _ x ↦ x)
      (fun _ ↦ aemeasurable_id))
  simpa [μ] using combination_hasLaw_standard_sum t (fun i (ω : ι → ℝ) ↦ ω i) hX hIndep

theorem product_combination_square (t : ι → ℝ) :
    (∫ ω : ι → ℝ, combination t (fun i ω ↦ ω i) ω ^ 2
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = (variance t : ℝ) := by
  exact combination_square t (fun i (ω : ι → ℝ) ↦ ω i)
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw)
    (by simpa using (iIndepFun_pi (μ := fun _ : ι ↦ gaussianReal 0 1)
      (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)))

theorem product_combination_fourth (t : ι → ℝ) :
    (∫ ω : ι → ℝ, combination t (fun i ω ↦ ω i) ω ^ 4
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = 3 * (variance t : ℝ) ^ 2 := by
  exact combination_fourth t (fun i (ω : ι → ℝ) ↦ ω i)
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw)
    (by simpa using (iIndepFun_pi (μ := fun _ : ι ↦ gaussianReal 0 1)
      (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)))

theorem product_combination_sixth (t : ι → ℝ) :
    (∫ ω : ι → ℝ, combination t (fun i ω ↦ ω i) ω ^ 6
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = 15 * (variance t : ℝ) ^ 3 := by
  exact combination_sixth t (fun i (ω : ι → ℝ) ↦ ω i)
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw)
    (by simpa using (iIndepFun_pi (μ := fun _ : ι ↦ gaussianReal 0 1)
      (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)))

theorem product_combination_eighth (t : ι → ℝ) :
    (∫ ω : ι → ℝ, combination t (fun i ω ↦ ω i) ω ^ 8
      ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1)) = 105 * (variance t : ℝ) ^ 4 := by
  exact combination_eighth t (fun i (ω : ι → ℝ) ↦ ω i)
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw)
    (by simpa using (iIndepFun_pi (μ := fun _ : ι ↦ gaussianReal 0 1)
      (X := fun _ x ↦ x) (fun _ ↦ aemeasurable_id)))

end
end QuaternionicSymmetry.GaussianCombination
