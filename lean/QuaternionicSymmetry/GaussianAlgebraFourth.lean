import QuaternionicSymmetry.GaussianAlgebra
import QuaternionicSymmetry.FourthPolarization

/-!
# Fourth scalar moments on the finite Gaussian product

This file begins the degree-four algebra-valued Wick calculation with the
mixed scalar four-coordinate moment.  It uses the actual product Gaussian
measure and derives the mixed moment by fourth polarization.
-/

namespace QuaternionicSymmetry.GaussianAlgebraFourth

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev standardMeasure : Measure (ι → ℝ) := GaussianAlgebra.standardMeasure

def scalarCombination (t : ι → ℝ) : (ι → ℝ) → ℝ :=
  fun ω ↦ ∑ i, t i * ω i

omit [DecidableEq ι] in
private theorem scalarCombination_eq (t : ι → ℝ) :
    scalarCombination t = GaussianCombination.combination t (fun i (ω : ι → ℝ) ↦ ω i) := by
  rfl

/-- The fourth moment of a real coefficient combination on the product Gaussian space. -/
theorem scalarCombination_fourth (t : ι → ℝ) :
    (∫ ω : ι → ℝ, scalarCombination t ω ^ 4 ∂standardMeasure) =
      3 * FourthPolarization.quartic t := by
  rw [scalarCombination_eq]
  simpa [pow_two, GaussianAlgebra.standardMeasure, GaussianCombination.variance,
    FourthPolarization.quartic, FourthPolarization.dot] using
    GaussianCombination.product_combination_fourth t

/-- Fourth powers of scalar combinations are integrable on the product Gaussian space. -/
theorem scalarCombination_integrable_fourth (t : ι → ℝ) :
    Integrable (fun ω : ι → ℝ ↦ scalarCombination t ω ^ 4) standardMeasure := by
  have hLaw := GaussianCombination.product_combination_hasLaw t
  have h : Integrable (fun x : ℝ ↦ x ^ 4)
      (gaussianReal 0 (GaussianCombination.variance t)) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) 4
  rw [← hLaw.map_eq] at h
  rw [scalarCombination_eq]
  exact h.comp_aemeasurable hLaw.aemeasurable

omit [DecidableEq ι] in
private theorem scalarCombination_add (s t : ι → ℝ) :
    scalarCombination (s + t) = scalarCombination s + scalarCombination t := by
  ext ω
  simp [scalarCombination, Finset.sum_add_distrib, add_mul]

omit [DecidableEq ι] in
private theorem scalarCombination_add3 (r s t : ι → ℝ) :
    scalarCombination (r + s + t) = scalarCombination r + scalarCombination s + scalarCombination t := by
  rw [scalarCombination_add, scalarCombination_add]

omit [DecidableEq ι] in
private theorem scalarCombination_add4 (r s t u : ι → ℝ) :
    scalarCombination (r + s + t + u) =
      scalarCombination r + scalarCombination s + scalarCombination t + scalarCombination u := by
  rw [scalarCombination_add, scalarCombination_add, scalarCombination_add]

private def IntegralValue (f : (ι → ℝ) → ℝ) (a : ℝ) : Prop :=
  Integrable f standardMeasure ∧ (∫ ω, f ω ∂standardMeasure) = a

omit [DecidableEq ι] in
private theorem integralValue_add {f g : (ι → ℝ) → ℝ} {a b : ℝ}
    (hf : IntegralValue f a) (hg : IntegralValue g b) : IntegralValue (f + g) (a + b) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  change (∫ ω, f ω + g ω ∂standardMeasure) = a + b
  rw [integral_add hf.1 hg.1, hf.2, hg.2]

omit [DecidableEq ι] in
private theorem integralValue_sub {f g : (ι → ℝ) → ℝ} {a b : ℝ}
    (hf : IntegralValue f a) (hg : IntegralValue g b) : IntegralValue (f - g) (a - b) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  change (∫ ω, f ω - g ω ∂standardMeasure) = a - b
  rw [integral_sub hf.1 hg.1, hf.2, hg.2]

omit [DecidableEq ι] in
private theorem integralValue_const_mul {f : (ι → ℝ) → ℝ} {a : ℝ}
    (hf : IntegralValue f a) (c : ℝ) : IntegralValue (fun ω => c * f ω) (c * a) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  rw [integral_const_mul, hf.2]

private theorem integralValue_fourth (t : ι → ℝ) :
    IntegralValue (fun ω => scalarCombination t ω ^ 4) (3 * FourthPolarization.quartic t) :=
  ⟨scalarCombination_integrable_fourth t, scalarCombination_fourth t⟩

/-- Polarization computes mixed fourth moments, and also proves their integrability. -/
theorem scalarCombination_mixed_fourth (x y z w : ι → ℝ) :
    Integrable (fun ω => scalarCombination x ω * scalarCombination y ω *
      scalarCombination z ω * scalarCombination w ω) standardMeasure ∧
    (∫ ω, scalarCombination x ω * scalarCombination y ω *
      scalarCombination z ω * scalarCombination w ω ∂standardMeasure) =
      FourthPolarization.dot x y * FourthPolarization.dot z w +
        FourthPolarization.dot x z * FourthPolarization.dot y w +
        FourthPolarization.dot x w * FourthPolarization.dot y z := by
  let H := fun t : ι → ℝ => integralValue_fourth t
  have htotal := integralValue_sub
    (integralValue_add
      (integralValue_sub (H (x + y + z + w))
        (integralValue_add (integralValue_add (integralValue_add
          (H (x + y + z)) (H (x + y + w))) (H (x + z + w))) (H (y + z + w))))
      (integralValue_add (integralValue_add (integralValue_add (integralValue_add
        (integralValue_add (H (x + y)) (H (x + z))) (H (x + w))) (H (y + z)))
        (H (y + w))) (H (z + w))))
    (integralValue_add (integralValue_add (integralValue_add (H x) (H y)) (H z)) (H w))
  have hpolar : IntegralValue
      (fun ω => FourthPolarization.scalarPolarization
        (scalarCombination x ω) (scalarCombination y ω)
        (scalarCombination z ω) (scalarCombination w ω))
      (3 * FourthPolarization.polarization FourthPolarization.quartic x y z w) := by
    convert htotal using 1
    · funext ω
      simp only [FourthPolarization.scalarPolarization, scalarCombination_add,
        Pi.add_apply, Pi.sub_apply]
    · unfold FourthPolarization.polarization
      ring
  have hscaled := integralValue_const_mul hpolar (1 / 24)
  change IntegralValue _ _
  convert hscaled using 1
  · funext ω
    rw [FourthPolarization.scalarPolarization_eq]
    ring
  · rw [FourthPolarization.polarization_quartic]
    ring

private theorem scalarCombination_single (i : ι) :
    scalarCombination (Pi.single i 1) = fun ω => ω i := by
  ext ω
  simp [scalarCombination, Pi.single_apply]

private theorem dot_single (i j : ι) :
    FourthPolarization.dot (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
  simp [FourthPolarization.dot, Pi.single_apply, eq_comm]

theorem coordinate_mixed_fourth_integrable (i j k l : ι) :
    Integrable (fun ω : ι → ℝ => ω i * ω j * ω k * ω l) standardMeasure := by
  simpa only [scalarCombination_single] using
    (scalarCombination_mixed_fourth (Pi.single i 1) (Pi.single j 1)
      (Pi.single k 1) (Pi.single l 1)).1

theorem coordinate_mixed_fourth (i j k l : ι) :
    (∫ ω : ι → ℝ, ω i * ω j * ω k * ω l ∂standardMeasure) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) +
        (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  simpa only [scalarCombination_single, dot_single] using
    (scalarCombination_mixed_fourth (Pi.single i 1) (Pi.single j 1)
      (Pi.single k 1) (Pi.single l 1)).2

end
end QuaternionicSymmetry.GaussianAlgebraFourth
