import QuaternionicSymmetry.CompactSymplecticHaar
import QuaternionicSymmetry.CompactPolynomialAverage
import QuaternionicSymmetry.CompactMomentPolynomial
import QuaternionicSymmetry.GaussianPolynomialExpectation
import QuaternionicSymmetry.QuaternionicSpectralSign

/-!
Actual compact symplectic Haar averages of quaternionic mixed forms.
Coefficientwise integration permits coefficients in the even exterior algebra,
including nilpotents, without imposing an artificial topology on that algebra.
The sign is deduced from the quaternionic spectral theorem before averaging.
Identification of these integrals with the finite Schur formula is separate.
-/

namespace QuaternionicSymmetry.QuaternionicHaarOrbital

open Matrix MeasureTheory Module
open QuaternionicFundamental HyperholomorphicExterior
open CompactSymplecticHaar GaussianPolynomialExpectation
open scoped MeasureTheory

noncomputable section

variable {κ β ι V : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
  [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Coordinates of the full real complex-trace conjugation pairing. -/
def traceCoordinates (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (g : stabilizer J) (b : β) : ℝ := 2 * halfTrace J A (B b) g

omit [Fintype β] in
theorem continuous_traceCoordinates (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) :
    Continuous (traceCoordinates J A B) :=
  continuous_pi fun b => continuous_const.mul (continuous_halfTrace J A (B b))

omit [Fintype β] in
theorem traceCoordinates_eq_trace (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (g : stabilizer J) (b : β) :
    traceCoordinates J A B g b =
      (Matrix.trace (A * (g.1 : Matrix κ κ ℂ) * B b *
        (g.1 : Matrix κ κ ℂ)ᴴ)).re := by
  unfold traceCoordinates halfTrace
  ring

def contraction (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (g : stabilizer J) : E V :=
  ∑ b, traceCoordinates J A B g b • η b

omit [FiniteDimensional ℝ V] in
theorem contraction_mem (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (g : stabilizer J) :
    contraction J A B η g ∈ formSpace Q c := by
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hη b)

def mixedPolynomial (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (η : β → E V) (k : ℕ) : MvPolynomial β (E V) :=
  (-(linearPolynomial η) ^ 2) ^ k *
    MvPolynomial.C (QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))

omit [FiniteDimensional ℝ V] in
set_option synthInstance.maxHeartbeats 100000 in
theorem eval_mixedPolynomial (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) (g : stabilizer J) :
    (mixedPolynomial Q c η k).eval
      (fun b => algebraMap ℝ (E V) (traceCoordinates J A B g b)) =
      (-(contraction J A B η g) ^ 2) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k) := by
  simp only [mixedPolynomial, map_mul, map_pow, map_neg, MvPolynomial.eval_C,
    eval_linearPolynomial, contraction]

/-- The factorial-normalized signed mixed orbital integral. -/
def mixedOrbitalForm (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) : E V :=
  ((Nat.factorial (2 * k) : ℝ)⁻¹) •
    CompactPolynomialAverage.average (probability J) (traceCoordinates J A B)
      (mixedPolynomial Q c η k)

omit [FiniteDimensional ℝ V] in
theorem functional_mixedOrbitalForm (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) (L : E V →ₗ[ℝ] ℝ) :
    L (mixedOrbitalForm Q c J A B η k) = ((Nat.factorial (2 * k) : ℝ)⁻¹) *
      ∫ g, L ((-(contraction J A B η g) ^ 2) ^ k *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k))
        ∂probability J := by
  unfold mixedOrbitalForm
  rw [map_smul, smul_eq_mul, ← CompactPolynomialAverage.integral_evaluation
    (probability J) (traceCoordinates J A B) (continuous_traceCoordinates J A B)]
  simp_rw [eval_mixedPolynomial]

/-- Positivity of the actual Haar average follows from the quaternionic spectral
sign at each group element, in every degree up to the quaternionic dimension. -/
theorem mixedOrbitalForm_mem_positiveRay (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c) (mixedOrbitalForm Q c J A B η k) := by
  apply PositiveRay.smul ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply CompactPolynomialAverage.average_contains (probability J) (traceCoordinates J A B)
    (continuous_traceCoordinates J A B) (QuaternionicSpectralSign.topForm_ne_zero Q c)
  intro g
  rw [eval_mixedPolynomial]
  apply (PositiveRay.contains_iff_functional_nonneg
    (QuaternionicSpectralSign.topForm_ne_zero Q c)).mpr
  intro L hL
  exact QuaternionicSpectralSign.formSpace_signed_mixed_nonneg Q c _
    (contraction_mem Q c J A B η hη g) k hk L hL

theorem mixedOrbitalForm_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (k : ℕ) (hk : k ≤ Q.quaternionicDimension)
    (L : E V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (topForm Q c)) :
    0 ≤ L (mixedOrbitalForm Q c J A B η k) :=
  PositiveRay.functional_nonneg
    (mixedOrbitalForm_mem_positiveRay Q c J A B η hη k hk) L hL

omit [FiniteDimensional ℝ V] in
set_option synthInstance.maxHeartbeats 100000 in
/-- A scalar identity for the factorial-normalized orbital moment continues
to the signed mixed form in the even exterior algebra. The scalar identity
is an explicit premise here; this theorem supplies the nilpotent continuation
and all sign/factorial bookkeeping. -/
theorem mixedOrbitalForm_eq_of_integral (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) (p : MvPolynomial β ℝ)
    (hp : ∀ x : β → ℝ,
      (∫ g, (∑ b, traceCoordinates J A B g b * x b) ^ (2 * k) ∂probability J) =
        (Nat.factorial (2 * k) : ℝ) * p.eval x) :
    mixedOrbitalForm Q c J A B η k =
      (-1 : E V) ^ k * MvPolynomial.aeval η p *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k) := by
  have hm := CompactMomentPolynomial.average_eq_aeval_of_integral_eq
    (probability J) (traceCoordinates J A B) (continuous_traceCoordinates J A B)
    (2 * k) (MvPolynomial.C (Nat.factorial (2 * k) : ℝ) * p)
    (by intro x; simpa only [map_mul, MvPolynomial.eval_C] using hp x) η
  simp only [map_mul, MvPolynomial.aeval_C] at hm
  unfold mixedOrbitalForm mixedPolynomial
  rw [CompactPolynomialAverage.average_signed_mixed, hm, Algebra.smul_def]
  have hn : (Nat.factorial (2 * k) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : algebraMap ℝ (E V) (Nat.factorial (2 * k) : ℝ)⁻¹ *
      algebraMap ℝ (E V) (Nat.factorial (2 * k) : ℝ) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hn, map_one]
  calc
    _ = (algebraMap ℝ (E V) (Nat.factorial (2 * k) : ℝ)⁻¹ *
          algebraMap ℝ (E V) (Nat.factorial (2 * k) : ℝ)) *
        ((-1 : E V) ^ k * MvPolynomial.aeval η p *
          QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Once the numerical Haar polynomial is identified, its signed evaluation
has the geometric positive ray, including for nilpotent form coefficients. -/
theorem polynomial_mem_positiveRay_of_integral (Q : QuaternionicStructure V)
    (c : Basis ι ℝ V) (J A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (η : β → E V) (hη : ∀ b, η b ∈ formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) (p : MvPolynomial β ℝ)
    (hp : ∀ x : β → ℝ,
      (∫ g, (∑ b, traceCoordinates J A B g b * x b) ^ (2 * k) ∂probability J) =
        (Nat.factorial (2 * k) : ℝ) * p.eval x) :
    PositiveRay.Contains (topForm Q c)
      ((-1 : E V) ^ k * MvPolynomial.aeval η p *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  rw [← mixedOrbitalForm_eq_of_integral Q c J A B η k p hp]
  exact mixedOrbitalForm_mem_positiveRay Q c J A B η hη k hk

end
end QuaternionicSymmetry.QuaternionicHaarOrbital
