import QuaternionicSymmetry.ComplexTorusLaurentEvaluationInjective
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! Literal Laurent-coordinate comultiplication for the algebraic complex
torus. It sends each integral character to the corresponding character in
both parameter factors. -/

namespace QuaternionicSymmetry.ComplexTorusLaurentComultiplication

open ComplexProjectiveDiagonalAlgebraicCharts
open TorusLaurentRepresentation
open CompactTorusPolynomialOrbitLaurent
noncomputable section

variable {r : ℕ}

abbrev DoubleTorusCoordinateRing (r : ℕ) :=
  AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin r → ℤ))

def diagonalWeight : (Fin r → ℤ) →+ ((Fin r → ℤ) × (Fin r → ℤ)) where
  toFun μ := (μ, μ)
  map_zero' := rfl
  map_add' _ _ := rfl

def comultiplication : TorusCoordinateRing r →+*
    DoubleTorusCoordinateRing r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (diagonalWeight (r := r))

@[simp] theorem comultiplication_laurentMonomial (μ : Fin r → ℤ) :
    comultiplication (laurentMonomial μ) =
      AddMonoidAlgebra.single (μ, μ) 1 := by
  simp [comultiplication, laurentMonomial, diagonalWeight]

def pairCharacter (z w : ComplexTorus r) :
    Multiplicative ((Fin r → ℤ) × (Fin r → ℤ)) →* ℂ where
  toFun ν := (complexWeightCharacter ν.toAdd.1 z : ℂ) *
    (complexWeightCharacter ν.toAdd.2 w : ℂ)
  map_one' := by simp [complexWeightCharacter]
  map_mul' ν τ := by
    change (complexWeightCharacter (ν.toAdd.1 + τ.toAdd.1) z : ℂ) *
        (complexWeightCharacter (ν.toAdd.2 + τ.toAdd.2) w : ℂ) = _
    rw [character_add, character_add]
    simp only [Units.val_mul]
    ring

def evalPair (z w : ComplexTorus r) : DoubleTorusCoordinateRing r →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ)
    (pairCharacter z w)
    (by intro a b; exact mul_comm a (pairCharacter z w b))

@[simp] theorem evalPair_single (z w : ComplexTorus r)
    (ν : (Fin r → ℤ) × (Fin r → ℤ)) :
    evalPair z w (AddMonoidAlgebra.single ν 1) =
      (complexWeightCharacter ν.1 z : ℂ) *
        (complexWeightCharacter ν.2 w : ℂ) := by
  simp [evalPair, pairCharacter]

theorem evalPair_comultiplication (z w : ComplexTorus r) :
    (evalPair z w).comp (comultiplication (r := r)) =
      evalTorus (z * w) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    simp [comultiplication, evalPair, evalTorus]
  · intro μ
    change evalPair z w (comultiplication (laurentMonomial μ)) =
      evalTorus (z * w) (laurentMonomial μ)
    rw [comultiplication_laurentMonomial, evalPair_single,
      evalTorus_laurentMonomial]
    simpa using (congrArg Units.val
      ((complexWeightCharacter μ).map_mul z w)).symm

end
end QuaternionicSymmetry.ComplexTorusLaurentComultiplication
