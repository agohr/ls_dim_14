import QuaternionicSymmetry.AlgebraPolynomialExt
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Polynomial identities on numerical Hermitian matrices extend to all
matrices with commuting coefficients in a complex algebra. -/

namespace QuaternionicSymmetry.HermitianPolynomialExt

open MvPolynomial

noncomputable section

variable {κ S : Type*} [Fintype κ] [CommRing S] [Algebra ℂ S]

def hermitianMatrix (x : Fin 2 × (κ × κ) → ℝ) : Matrix κ κ ℂ :=
  fun i j => (x (0, (i, j)) : ℂ) + (x (0, (j, i)) : ℂ) +
    Complex.I * ((x (1, (i, j)) : ℂ) - (x (1, (j, i)) : ℂ))

omit [Fintype κ] in
theorem hermitianMatrix_isHermitian (x : Fin 2 × (κ × κ) → ℝ) :
    (hermitianMatrix x).IsHermitian := by
  ext i j
  simp [hermitianMatrix, Matrix.conjTranspose_apply]
  ring

def coordinates (p : κ × κ) : MvPolynomial (Fin 2 × (κ × κ)) S :=
  X (0, p) + X (0, (p.2, p.1)) + C (algebraMap ℂ S Complex.I) *
    (X (1, p) - X (1, (p.2, p.1)))

omit [Fintype κ] in
theorem eval_coordinates (x : Fin 2 × (κ × κ) → ℝ) (p : κ × κ) :
    (coordinates p : MvPolynomial _ S).eval (fun i => algebraMap ℝ S (x i)) =
      algebraMap ℂ S (hermitianMatrix x p.1 p.2) := by
  simp only [coordinates, hermitianMatrix, map_add, map_mul, map_sub, eval_X, eval_C]
  rfl

private def inverseParameters (p : Fin 2 × (κ × κ)) : MvPolynomial (κ × κ) S :=
  if p.1 = 0 then C (algebraMap ℂ S (1 / 2)) * X p.2
    else C (algebraMap ℂ S (-Complex.I / 2)) * X p.2

omit [Fintype κ] in
private theorem bind_inverse_coordinates (p : κ × κ) :
    bind₁ (inverseParameters (S := S)) (coordinates p) = X p := by
  simp only [coordinates, map_add, map_mul, map_sub, bind₁_X_right, bind₁_C_right,
    inverseParameters, ↓reduceIte]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
  have hi : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) / 2 := by ring
      _ = _ := by rw [Complex.I_sq]; norm_num
  calc
    _ = C (algebraMap ℂ S (1 / 2 + Complex.I * (-Complex.I / 2))) * X p +
        C (algebraMap ℂ S (1 / 2 - Complex.I * (-Complex.I / 2))) * X (p.2, p.1) := by
      simp only [map_add, map_sub, map_mul]
      ring
    _ = X p := by rw [hi]; norm_num

/-- Hermitian numerical evaluations detect every polynomial identity, including
identities later evaluated in a coefficient ring with nilpotents. -/
theorem ext {p q : MvPolynomial (κ × κ) S}
    (h : ∀ A : Matrix κ κ ℂ, A.IsHermitian →
      p.eval (fun i => algebraMap ℂ S (A i.1 i.2)) =
        q.eval (fun i => algebraMap ℂ S (A i.1 i.2))) : p = q := by
  have hb : bind₁ (coordinates (S := S)) p = bind₁ (coordinates (S := S)) q := by
    apply AlgebraPolynomialExt.mvPolynomial_ext
    intro x
    change eval₂Hom (RingHom.id S) _ (bind₁ coordinates p) =
      eval₂Hom (RingHom.id S) _ (bind₁ coordinates q)
    rw [eval₂Hom_bind₁, eval₂Hom_bind₁]
    simp_rw [show ∀ i : κ × κ,
        eval₂Hom (RingHom.id S) (fun j => algebraMap ℝ S (x j)) (coordinates i) =
          algebraMap ℂ S (hermitianMatrix x i.1 i.2) from eval_coordinates x]
    exact h (hermitianMatrix x) (hermitianMatrix_isHermitian x)
  have hi := congrArg (bind₁ (inverseParameters (S := S))) hb
  simpa only [bind₁_bind₁, bind_inverse_coordinates, bind₁_X_left, AlgHom.id_apply] using hi

end
end QuaternionicSymmetry.HermitianPolynomialExt
