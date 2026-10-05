import QuaternionicSymmetry.UnitaryHaarMeasure
import QuaternionicSymmetry.AlgebraPolynomialExt
import QuaternionicSymmetry.PositiveRay
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Coefficientwise integration of unitary matrix polynomials over actual
Haar probability measure. Arbitrary real-linear functionals recover the
scalar integrals, with no topology on the coefficient algebra. -/

namespace QuaternionicSymmetry.UnitaryPolynomialExpectation

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {κ S T : Type*} [Fintype κ] [DecidableEq κ]
  [CommRing S] [Algebra ℝ S] [CommRing T] [Algebra ℝ T]

abbrev Variables (κ : Type*) := (κ × κ) × Fin 2

def coordinates (U : Matrix.unitaryGroup κ ℂ) (p : Variables κ) : ℝ :=
  if p.2 = 0 then (U.val p.1.1 p.1.2).re else (U.val p.1.1 p.1.2).im

theorem continuous_coordinates : Continuous (coordinates (κ := κ)) := by
  apply continuous_pi
  intro p
  have hc : Continuous (fun U : Matrix.unitaryGroup κ ℂ => U.val p.1.1 p.1.2) :=
    (continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp continuous_subtype_val)
  unfold coordinates
  split_ifs
  · exact Complex.continuous_re.comp hc
  · exact Complex.continuous_im.comp hc

def monomialMoment (d : Variables κ →₀ ℕ) : ℝ :=
  ∫ U : Matrix.unitaryGroup κ ℂ, ∏ i, coordinates U i ^ d i
    ∂UnitaryHaarMeasure.probability

def expectation : MvPolynomial (Variables κ) S →ₗ[S] S :=
  Finsupp.linearCombination S (fun d => algebraMap ℝ S (monomialMoment d))

@[simp] theorem expectation_monomial (d : Variables κ →₀ ℕ) (c : S) :
    expectation (MvPolynomial.monomial d c) = c * algebraMap ℝ S (monomialMoment d) := by
  exact Finsupp.linearCombination_single _ _ _

theorem expectation_map (f : S →ₐ[ℝ] T) (p : MvPolynomial (Variables κ) S) :
    f (expectation p) = expectation (MvPolynomial.map f.toRingHom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c => simp
  | add p q hp hq => simp [hp, hq]

theorem polynomial_integrable (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial (Variables κ) S) :
    Integrable (fun U : Matrix.unitaryGroup κ ℂ =>
      L (p.eval (fun i => algebraMap ℝ S (coordinates U i))))
      UnitaryHaarMeasure.probability := by
  simp_rw [← AlgebraPolynomialExt.eval_mapCoefficients]
  have hc := (MvPolynomial.continuous_eval
    (AlgebraPolynomialExt.mapCoefficients L p)).comp continuous_coordinates
  exact (integrableOn_univ).mp (hc.continuousOn.integrableOn_compact isCompact_univ)

private theorem apply_scalar (L : S →ₗ[ℝ] ℝ) (c : S) (r : ℝ) :
    L (c * algebraMap ℝ S r) = L c * r := by
  rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm r]

theorem integral_polynomial (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial (Variables κ) S) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
      L (p.eval (fun i => algebraMap ℝ S (coordinates U i)))
        ∂UnitaryHaarMeasure.probability) = L (expectation p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
      simp only [← map_pow, ← map_prod, apply_scalar, expectation_monomial]
      rw [integral_const_mul]
      rfl
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (polynomial_integrable L p) (polynomial_integrable L q), hp, hq]

theorem expectation_contains {v : S} (hv : v ≠ 0)
    (p : MvPolynomial (Variables κ) S)
    (hp : ∀ U : Matrix.unitaryGroup κ ℂ,
      PositiveRay.Contains v (p.eval (fun i => algebraMap ℝ S (coordinates U i)))) :
    PositiveRay.Contains v (expectation p) := by
  apply (PositiveRay.contains_iff_functional_nonneg hv).mpr
  intro L hLv
  rw [← integral_polynomial]
  exact integral_nonneg (fun U => PositiveRay.functional_nonneg (hp U) L hLv)

end
end QuaternionicSymmetry.UnitaryPolynomialExpectation
