import QuaternionicSymmetry.AlgebraCertificates
import QuaternionicSymmetry.EvenForms

/-!
  Universal certificate identities evaluated in an actual exterior algebra.

  The ambient exterior algebra need not be commutative.  The evaluation first
  lands in `EvenForms.evenSubalgebra`, whose commutativity was proved from the
  exterior relations, and is only then coerced to the ambient algebra.
  No geometric interpretation of the supplied forms is asserted here.
-/

namespace QuaternionicSymmetry
namespace ExteriorCertificates

open EvenForms
open AlgebraCertificates

noncomputable section

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]

/-- Put a homogeneous even exterior form into the proved commutative subalgebra. -/
def liftEven (n : ℕ) (a : ExteriorAlgebra.exteriorPower R (2 * n) V) : evenSubalgebra R V :=
  ⟨a, even_degree_le n a.property⟩

set_option linter.unusedSectionVars false in
@[simp] theorem liftEven_coe (n : ℕ) (a : ExteriorAlgebra.exteriorPower R (2 * n) V) :
    (liftEven n a : ExteriorAlgebra R V) = a := rfl

/-- Evaluate a certificate polynomial in the commutative even subalgebra. -/
def evaluateEven
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) : AlgebraCertificates.P →ₐ[ℚ] evenSubalgebra R V :=
  AlgebraCertificates.evaluate (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄)

/-- The same evaluation, viewed in the ambient (possibly noncommutative) exterior algebra. -/
def evaluateExterior
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V)
    (p : AlgebraCertificates.P) : ExteriorAlgebra R V :=
  (evaluateEven u z₁ z₂ z₃ z₄ p : ExteriorAlgebra R V)

theorem certificate₂
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₂ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₂ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₂_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₃
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₃ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₃ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₃_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₄
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₄ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₄ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₄_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₅
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₅ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₅ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₅_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₆
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₆ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₆ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₆_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₇
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₇ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₇ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₇_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₈
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₈ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₈ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₈_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₉
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₉ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₉ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₉_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

theorem certificate₁₀
    (u : ExteriorAlgebra.exteriorPower R 4 V)
    (z₁ : ExteriorAlgebra.exteriorPower R 4 V)
    (z₂ : ExteriorAlgebra.exteriorPower R 8 V)
    (z₃ : ExteriorAlgebra.exteriorPower R 12 V)
    (z₄ : ExteriorAlgebra.exteriorPower R 16 V) :
    evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.K₁₀ = evaluateExterior u z₁ z₂ z₃ z₄ AlgebraCertificates.RHS₁₀ := by
  exact congrArg (fun x : evenSubalgebra R V => (x : ExteriorAlgebra R V))
    (AlgebraCertificates.certificate₁₀_eval (liftEven 2 u) (liftEven 2 z₁) (liftEven 4 z₂) (liftEven 6 z₃) (liftEven 8 z₄))

end
end ExteriorCertificates
end QuaternionicSymmetry
