import QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Sound evaluation of finite rational characteristic polynomials in the
constant-coefficient even de Rham algebra. Grade `n` is actual degree `4*n`;
the degree-zero scalar map to `H⁰` is not asserted injective on empty manifolds.
-/

namespace QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness

open QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra
open scoped Manifold ContDiff Topology

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Finite rational expressions with degrees measured in units of four. -/
inductive EvenExpr : ℕ → Type
  | coeff (q : ℚ) : EvenExpr 0
  | u : EvenExpr 1
  | trace₂ : EvenExpr 1
  | trace₄ : EvenExpr 2
  | trace₆ : EvenExpr 3
  | add {n : ℕ} : EvenExpr n → EvenExpr n → EvenExpr n
  | neg {n : ℕ} : EvenExpr n → EvenExpr n
  | mul {p q : ℕ} : EvenExpr p → EvenExpr q → EvenExpr (p + q)
  | cast {p q : ℕ} (h : p = q) : EvenExpr p → EvenExpr q

namespace EvenExpr

noncomputable def polynomial : {n : ℕ} → EvenExpr n → MvPolynomial (Fin 4) ℚ
  | _, .coeff q => MvPolynomial.C q
  | _, .u => MvPolynomial.X 0
  | _, .trace₂ => MvPolynomial.X 1
  | _, .trace₄ => MvPolynomial.X 2
  | _, .trace₆ => MvPolynomial.X 3
  | _, .add P R => polynomial P + polynomial R
  | _, .neg P => -polynomial P
  | _, .mul P R => polynomial P * polynomial R
  | _, .cast _ P => polynomial P

/-- Evaluation in actual homogeneous de Rham classes. -/
noncomputable def evaluate
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3) :
    {n : ℕ} → EvenExpr n → Grade (E := E) (M := M) n
  | _, .coeff q => (q : ℝ)
  | _, .u => u
  | _, .trace₂ => t₂
  | _, .trace₄ => t₄
  | _, .trace₆ => t₆
  | _, .add P R => evaluate u t₂ t₄ t₆ P + evaluate u t₂ t₄ t₆ R
  | _, .neg P => -evaluate u t₂ t₄ t₆ P
  | _, .mul P R => gradeMul _ _ (evaluate u t₂ t₄ t₆ P)
      (evaluate u t₂ t₄ t₆ R)
  | _, .cast h P => castGrade h (evaluate u t₂ t₄ t₆ P)

noncomputable def generatorValues
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3) :
    Fin 4 → Total (E := E) (M := M) :=
  ![DirectSum.of _ 1 u, DirectSum.of _ 1 t₂,
    DirectSum.of _ 2 t₄, DirectSum.of _ 3 t₆]

/-- Ordinary rational polynomial evaluation into the genuine even de Rham
direct sum. -/
noncomputable def polynomialEvaluation
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3) :
    MvPolynomial (Fin 4) ℚ →+* Total (E := E) (M := M) :=
  MvPolynomial.eval₂Hom rationalConstants (generatorValues u t₂ t₄ t₆)

theorem evaluation_sound
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3) :
    ∀ {n : ℕ} (P : EvenExpr n),
      DirectSum.of (Grade (E := E) (M := M)) n
          (evaluate u t₂ t₄ t₆ P) =
        polynomialEvaluation u t₂ t₄ t₆ (polynomial P) := by
  intro n P
  induction P with
  | coeff q =>
      simp [evaluate, polynomial, polynomialEvaluation, rationalConstants,
        MvPolynomial.eval₂Hom_C]
      rfl
  | u =>
      simp [evaluate, polynomial, polynomialEvaluation, generatorValues,
        MvPolynomial.eval₂Hom_X']
  | trace₂ =>
      simp [evaluate, polynomial, polynomialEvaluation, generatorValues,
        MvPolynomial.eval₂Hom_X']
  | trace₄ =>
      simp [evaluate, polynomial, polynomialEvaluation, generatorValues,
        MvPolynomial.eval₂Hom_X']
  | trace₆ =>
      simp [evaluate, polynomial, polynomialEvaluation, generatorValues,
        MvPolynomial.eval₂Hom_X']
  | add P R hP hR =>
      simpa only [evaluate, polynomial, map_add, map_add] using
        congrArg₂ (· + ·) hP hR
  | neg P hP =>
      simpa only [evaluate, polynomial, map_neg] using congrArg Neg.neg hP
  | mul P R hP hR =>
      simp only [evaluate, polynomial, map_mul]
      rw [← hP, ← hR]
      exact (DirectSum.of_mul_of _ _).symm
  | cast h P hP =>
      cases h
      exact hP

theorem evaluate_eq_of_polynomial_eq
    (u t₂ : Grade (E := E) (M := M) 1)
    (t₄ : Grade (E := E) (M := M) 2)
    (t₆ : Grade (E := E) (M := M) 3)
    {n : ℕ} (P R : EvenExpr n)
    (h : polynomial P = polynomial R) :
    evaluate u t₂ t₄ t₆ P = evaluate u t₂ t₄ t₆ R := by
  apply DirectSum.of_injective (β := Grade (E := E) (M := M)) n
  rw [evaluation_sound, evaluation_sound, h]

theorem evaluate_congr
    {u u' t₂ t₂' : Grade (E := E) (M := M) 1}
    {t₄ t₄' : Grade (E := E) (M := M) 2}
    {t₆ t₆' : Grade (E := E) (M := M) 3}
    (hu : u = u') (h₂ : t₂ = t₂') (h₄ : t₄ = t₄') (h₆ : t₆ = t₆') :
    ∀ {n : ℕ} (P : EvenExpr n),
      evaluate u t₂ t₄ t₆ P = evaluate u' t₂' t₄' t₆' P := by
  intro n P
  induction P with
  | coeff q => rfl
  | u => exact hu
  | trace₂ => exact h₂
  | trace₄ => exact h₄
  | trace₆ => exact h₆
  | add P R hP hR => exact congrArg₂ (· + ·) hP hR
  | neg P hP => exact congrArg Neg.neg hP
  | mul P R hP hR => exact congrArg₂ (gradeMul _ _) hP hR
  | cast h P hP => exact congrArg (castGrade h) hP

end EvenExpr

end QuaternionicSymmetry.ManifoldCharacteristicPolynomialSoundness
