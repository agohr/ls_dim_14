import QuaternionicSymmetry.QuaternionicBlockPencil
import QuaternionicSymmetry.AlgebraPolynomialExt
import QuaternionicSymmetry.GaussianRadialMoments

/-!
  A polynomial form of the quaternionic block-pencil identity.

  Coefficients lie in the commutative subalgebra of even exterior forms.  The
  extension lemmas reduce the identity to ordinary real evaluations, so this
  remains valid although the coefficient algebra has nilpotents.
-/

namespace QuaternionicSymmetry
namespace QuaternionicPencilPolynomial

open scoped BigOperators
open QuaternionicBlocks QuaternionicBlockPencil

noncomputable section

variable {β : Type*} [Fintype β] [DecidableEq β]

abbrev Eev (β : Type*) := EvenForms.evenSubalgebra ℝ (V β)

def alphaEven (j : β) : Eev β := ⟨α j, alpha_even j⟩
def omegaIEven (j : β) : Eev β := ⟨ωI j, omegaI_even j⟩
def omegaJEven (j : β) : Eev β := ⟨ωJ j, omegaJ_even j⟩
def omegaKEven (j : β) : Eev β := ⟨ωK j, omegaK_even j⟩

omit [Fintype β] in
@[simp] theorem coe_alphaEven (j : β) : (alphaEven j : E β) = α j := rfl
omit [Fintype β] in
@[simp] theorem coe_omegaIEven (j : β) : (omegaIEven j : E β) = ωI j := rfl
omit [Fintype β] in
@[simp] theorem coe_omegaJEven (j : β) : (omegaJEven j : E β) = ωJ j := rfl
omit [Fintype β] in
@[simp] theorem coe_omegaKEven (j : β) : (omegaKEven j : E β) = ωK j := rfl

/-- The anti-self-dual part of the block pencil. -/
def theta (lam : β → ℝ) : Eev β := ∑ j, lam j • alphaEven j

/-- The three invariant two-forms, as a three-vector. -/
def omega : Fin 3 → Eev β := ![
  ∑ j : β, omegaIEven j,
  ∑ j : β, omegaJEven j,
  ∑ j : β, omegaKEven j]

def volume : Eev β := ∏ j : β, volEven j

/-- The universal pencil with a formal scalar variable and three Gaussian
coordinates. -/
def pencilPolynomial (lam : β → ℝ) : MvPolynomial (Fin 3) (Polynomial (Eev β)) :=
  MvPolynomial.C (Polynomial.X * Polynomial.C (theta lam)) +
    GaussianPolynomialExpectation.linearPolynomial (fun i => Polynomial.C (omega i))

/-- The universal radial product of the block coefficients. -/
def coefficientPolynomial (lam : β → ℝ) : MvPolynomial (Fin 3) (Polynomial (Eev β)) :=
  ∏ j : β, ((GaussianRadialMoments.radial : MvPolynomial (Fin 3) (Polynomial (Eev β))) -
    MvPolynomial.C (Polynomial.X ^ 2 * Polynomial.C
      (algebraMap ℝ (Eev β) (lam j ^ 2))))

private theorem eval_omega (x : Fin 3 → ℝ) :
    ∑ i, x i • omega i =
      (x 0 • ∑ j : β, omegaIEven j) + (x 1 • ∑ j : β, omegaJEven j) +
        (x 2 • ∑ j : β, omegaKEven j) := by
  rw [Fin.sum_univ_three]
  rfl

omit [Fintype β] in
private theorem pencilEven_expanded (lam : β → ℝ) (j : β) (t a b c : ℝ) :
    pencilEven lam j t a b c =
      (t * lam j) • alphaEven j + a • omegaIEven j + b • omegaJEven j + c • omegaKEven j := by
  rfl

private theorem sum_pencilEven_eq (lam : β → ℝ) (t : ℝ) (x : Fin 3 → ℝ) :
    ∑ j : β, pencilEven lam j t (x 0) (x 1) (x 2) =
      t • theta lam + ∑ i, x i • omega i := by
  rw [eval_omega]
  simp_rw [pencilEven_expanded]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [theta]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  simp only [mul_smul]
  abel

private theorem eval_pencilPolynomial (lam : β → ℝ) (x : Fin 3 → ℝ) (t : ℝ) :
    Polynomial.eval (algebraMap ℝ (Eev β) t)
      (MvPolynomial.eval (fun i => algebraMap ℝ (Polynomial (Eev β)) (x i))
        (pencilPolynomial lam)) =
      ∑ j : β, pencilEven lam j t (x 0) (x 1) (x 2) := by
  rw [pencilPolynomial]
  rw [MvPolynomial.eval_add, MvPolynomial.eval_C,
    GaussianPolynomialExpectation.eval_linearPolynomial]
  rw [Fin.sum_univ_three]
  simp only [Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.algebraMap_apply, Algebra.smul_def]
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
  rw [show x 0 • omega 0 + x 1 • omega 1 + x 2 • omega 2 =
      ∑ i, x i • omega i by rw [Fin.sum_univ_three]]
  exact (sum_pencilEven_eq lam t x).symm

omit [DecidableEq β] in
private theorem eval_coefficientPolynomial (lam : β → ℝ) (x : Fin 3 → ℝ) (t : ℝ) :
    Polynomial.eval (algebraMap ℝ (Eev β) t)
      (MvPolynomial.eval (fun i => algebraMap ℝ (Polynomial (Eev β)) (x i))
        (coefficientPolynomial lam)) =
      algebraMap ℝ (Eev β) (∏ j : β, coefficient lam j t (x 0) (x 1) (x 2)) := by
  rw [coefficientPolynomial, map_prod, Polynomial.eval_prod, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_C, GaussianRadialMoments.eval_radial,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.algebraMap_apply, map_pow, Fin.sum_univ_three]
  rw [Polynomial.eval_add, Polynomial.eval_add]
  simp only [Polynomial.eval_pow, Polynomial.eval_C]
  simp only [coefficient]
  rw [RingHom.map_sub (algebraMap ℝ (Eev β)),
    RingHom.map_add (algebraMap ℝ (Eev β)), RingHom.map_add (algebraMap ℝ (Eev β)),
    RingHom.map_mul (algebraMap ℝ (Eev β)),
    RingHom.map_pow (algebraMap ℝ (Eev β)), RingHom.map_pow (algebraMap ℝ (Eev β)),
    RingHom.map_pow (algebraMap ℝ (Eev β)), RingHom.map_pow (algebraMap ℝ (Eev β)),
    RingHom.map_pow (algebraMap ℝ (Eev β))]

/-- The global exterior pencil identity as an equality of polynomials in the
three Gaussian coordinates and one formal scalar parameter. -/
theorem pencilPolynomial_top_power (lam : β → ℝ) :
    (pencilPolynomial lam) ^ (2 * Fintype.card β) =
      MvPolynomial.C (Polynomial.C
        (((2 * Fintype.card β).factorial : ℝ) • (volume : Eev β))) *
        coefficientPolynomial lam := by
  apply AlgebraPolynomialExt.mvPolynomial_ext
  intro x
  apply AlgebraPolynomialExt.polynomial_ext
  intro t
  rw [MvPolynomial.eval_pow, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C]
  rw [eval_pencilPolynomial, eval_coefficientPolynomial,
    sum_pencilEven_top_power]
  simp only [volume, Algebra.smul_def, map_natCast]
  ring

end
end QuaternionicPencilPolynomial
end QuaternionicSymmetry
