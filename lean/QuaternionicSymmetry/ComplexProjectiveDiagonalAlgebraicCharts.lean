import QuaternionicSymmetry.ComplexProjectiveDiagonalJointHolomorphic
import QuaternionicSymmetry.CompactTorusPolynomialOrbitLaurent
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasis
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MvPolynomial.Eval

/-! Each diagonal projective affine coordinate is the evaluation of a
literal polynomial over the Laurent coordinate ring of the algebraic
complex torus. This is a source-free regular-coordinate bridge, not yet a
scheme action on the embedded twistor. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts

open TorusLaurentRepresentation CompactTorusPolynomialOrbitLaurent
open ComplexProjectiveDiagonalHolomorphic
open HolomorphicLineCoreProjectiveEigenbasis
open scoped BigOperators
noncomputable section

abbrev TorusCoordinateRing (r : ℕ) := AddMonoidAlgebra ℂ (Fin r → ℤ)

def laurentMonomial {r : ℕ} (ν : Fin r → ℤ) : TorusCoordinateRing r :=
  AddMonoidAlgebra.single ν 1

def exponentCharacter {r : ℕ} (z : ComplexTorus r) :
    Multiplicative (Fin r → ℤ) →* ℂ where
  toFun ν := (complexWeightCharacter ν.toAdd z : ℂ)
  map_one' := by
    simp [complexWeightCharacter]
  map_mul' ν τ := by
    change (complexWeightCharacter (ν.toAdd + τ.toAdd) z : ℂ) =
      (complexWeightCharacter ν.toAdd z : ℂ) *
        (complexWeightCharacter τ.toAdd z : ℂ)
    exact congrArg Units.val (character_add ν.toAdd τ.toAdd z)

def evalTorus {r : ℕ} (z : ComplexTorus r) : TorusCoordinateRing r →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ)
    (exponentCharacter z)
    (by intro a b; exact mul_comm a (exponentCharacter z b))

@[simp] theorem evalTorus_laurentMonomial {r : ℕ}
    (z : ComplexTorus r) (ν : Fin r → ℤ) :
    evalTorus z (laurentMonomial ν) =
      (complexWeightCharacter ν z : ℂ) := by
  simp [evalTorus, laurentMonomial, exponentCharacter]

def regularChartCoordinate {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ)
    (i : Fin (d + 1)) (k : Fin d) :
    MvPolynomial (Fin d) (TorusCoordinateRing r) :=
  MvPolynomial.C (laurentMonomial (μ (i.succAbove k) - μ i)) *
    MvPolynomial.X k

theorem eval_regularChartCoordinate {r d : ℕ}
    (μ : Fin (d + 1) → Fin r → ℤ)
    (i : Fin (d + 1)) (k : Fin d)
    (z : ComplexTorus r) (w : Fin d → ℂ) :
    MvPolynomial.eval₂ (evalTorus z) w
      (regularChartCoordinate μ i k) =
      chartDiagonal μ z i w k := by
  have hchar : (complexWeightCharacter
      (μ (i.succAbove k) - μ i) z : ℂ) =
      (complexWeightCharacter (μ (i.succAbove k)) z : ℂ) /
        (complexWeightCharacter (μ i) z : ℂ) := by
    rw [sub_eq_add_neg, character_add,
      complexWeightCharacter_neg]
    simp [div_eq_mul_inv]
  simp [regularChartCoordinate, MvPolynomial.eval₂_mul,
    evalTorus_laurentMonomial, hchar, chartDiagonal]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts
