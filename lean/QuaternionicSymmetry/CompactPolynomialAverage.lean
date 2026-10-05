import QuaternionicSymmetry.PositiveRay
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Coefficientwise averaging over a compact space, including coefficient rings
with nilpotents. The scalar integrals are actual Bochner integrals, and their
comparison with every real-linear functional proves preservation of positive
rays without choosing a norm on the coefficient algebra.
-/

namespace QuaternionicSymmetry.CompactPolynomialAverage

open MeasureTheory
open scoped MeasureTheory

noncomputable section

variable {Ω β S : Type*} [MeasurableSpace Ω] [Fintype β]
  [CommRing S] [Algebra ℝ S]

def monomialMoment (μ : Measure Ω) (f : Ω → β → ℝ) (d : β →₀ ℕ) : ℝ :=
  ∫ ω, MvPolynomial.eval (f ω) (MvPolynomial.monomial d (1 : ℝ)) ∂μ

def average (μ : Measure Ω) (f : Ω → β → ℝ) : MvPolynomial β S →ₗ[S] S :=
  Finsupp.linearCombination S
    (fun d => algebraMap ℝ S (monomialMoment μ f d))

omit [Fintype β] in
@[simp] theorem average_monomial (μ : Measure Ω) (f : Ω → β → ℝ)
    (d : β →₀ ℕ) (a : S) :
    average μ f (MvPolynomial.monomial d a) =
      a * algebraMap ℝ S (monomialMoment μ f d) :=
  Finsupp.linearCombination_single _ _ _

omit [Fintype β] in
theorem average_C_mul (μ : Measure Ω) (f : Ω → β → ℝ)
    (a : S) (p : MvPolynomial β S) :
    average μ f (MvPolynomial.C a * p) = a * average μ f p := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

omit [Fintype β] in
set_option maxRecDepth 1024 in
theorem average_signed_mixed (μ : Measure Ω) (f : Ω → β → ℝ)
    (p : MvPolynomial β S) (a : S) (k : ℕ) :
    average μ f ((-p ^ 2) ^ k * MvPolynomial.C a) =
      (-1 : S) ^ k * average μ f (p ^ (2 * k)) * a := by
  have hp : (-p ^ 2) ^ k * MvPolynomial.C a =
      MvPolynomial.C ((-1 : S) ^ k * a) * p ^ (2 * k) := by
    rw [neg_pow, ← pow_mul]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  rw [hp, average_C_mul]
  ring

private theorem apply_scalar (L : S →ₗ[ℝ] ℝ) (a : S) (r : ℝ) :
    L (a * algebraMap ℝ S r) = L a * r := by
  rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm r]

omit [Fintype β] in
/-- Coefficientwise averaging commutes with every real algebra morphism;
the target algebra may contain nilpotents. -/
theorem average_map {T : Type*} [CommRing T] [Algebra ℝ T]
    (μ : Measure Ω) (f : Ω → β → ℝ) (φ : S →ₐ[ℝ] T)
    (p : MvPolynomial β S) :
    φ (average μ f p) = average μ f (MvPolynomial.map φ.toRingHom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a => simp
  | add p q hp hq => simp [hp, hq]

private theorem eval_monomial (L : S →ₗ[ℝ] ℝ) (d : β →₀ ℕ)
    (a : S) (x : β → ℝ) :
    L (MvPolynomial.eval (fun i => algebraMap ℝ S (x i)) (MvPolynomial.monomial d a)) =
      L a * MvPolynomial.eval x (MvPolynomial.monomial d (1 : ℝ)) := by
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul]
  simp only [← map_pow, ← map_prod]
  exact apply_scalar L a _

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → β → ℝ)
  (hf : Continuous f)

include hf

omit [MeasurableSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
theorem continuous_evaluation (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S) :
    Continuous (fun ω => L (p.eval (fun i => algebraMap ℝ S (f ω i)))) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      simp_rw [eval_monomial]
      exact continuous_const.mul ((MvPolynomial.monomial d (1 : ℝ)).continuous_eval.comp hf)
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq

theorem integrable_evaluation (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S) :
    Integrable (fun ω => L (p.eval (fun i => algebraMap ℝ S (f ω i)))) μ :=
  (continuous_evaluation f hf L p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Scalar evaluation of the coefficient average equals the actual integral. -/
theorem integral_evaluation (L : S →ₗ[ℝ] ℝ) (p : MvPolynomial β S) :
    (∫ ω, L (p.eval (fun i => algebraMap ℝ S (f ω i))) ∂μ) = L (average μ f p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      simp_rw [eval_monomial]
      rw [integral_const_mul, average_monomial, apply_scalar]
      rfl
  | add p q hp hq =>
      simp only [map_add]
      rw [integral_add (integrable_evaluation μ f hf L p)
        (integrable_evaluation μ f hf L q), hp, hq]

/-- Positive-ray membership is preserved by compact averaging, in arbitrary
real coefficient algebras including the even exterior algebra. -/
theorem average_contains {v : S} (hv : v ≠ 0) (p : MvPolynomial β S)
    (hp : ∀ ω, PositiveRay.Contains v
      (p.eval (fun i => algebraMap ℝ S (f ω i)))) :
    PositiveRay.Contains v (average μ f p) := by
  apply (PositiveRay.contains_iff_functional_nonneg hv).mpr
  intro L hLv
  rw [← integral_evaluation μ f hf L p]
  apply integral_nonneg
  intro ω
  exact PositiveRay.functional_nonneg (hp ω) L hLv

end
end QuaternionicSymmetry.CompactPolynomialAverage
