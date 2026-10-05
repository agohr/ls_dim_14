import QuaternionicSymmetry.ComplexTorusLaurentComultiplication

/-! Coassociativity of the literal Laurent coordinate-ring comultiplication.
This is the group law on the algebraic complex torus's coordinate ring. -/

namespace QuaternionicSymmetry.ComplexTorusLaurentCoassociative

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r : ℕ}

abbrev TripleTorusCoordinateRing (r : ℕ) :=
  AddMonoidAlgebra ℂ (((Fin r → ℤ) × (Fin r → ℤ)) × (Fin r → ℤ))

def leftDup : ((Fin r → ℤ) × (Fin r → ℤ)) →+
    (((Fin r → ℤ) × (Fin r → ℤ)) × (Fin r → ℤ)) where
  toFun ν := ((ν.1, ν.1), ν.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def rightDup : ((Fin r → ℤ) × (Fin r → ℤ)) →+
    (((Fin r → ℤ) × (Fin r → ℤ)) × (Fin r → ℤ)) where
  toFun ν := ((ν.1, ν.2), ν.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def leftComultiplication : DoubleTorusCoordinateRing r →+*
    TripleTorusCoordinateRing r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (leftDup (r := r))

def rightComultiplication : DoubleTorusCoordinateRing r →+*
    TripleTorusCoordinateRing r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (rightDup (r := r))

theorem comultiplication_coassociative :
    (leftComultiplication (r := r)).comp comultiplication =
      (rightComultiplication (r := r)).comp comultiplication := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    simp [leftComultiplication, rightComultiplication, comultiplication]
  · intro μ
    change leftComultiplication (comultiplication (laurentMonomial μ)) =
      rightComultiplication (comultiplication (laurentMonomial μ))
    simp [comultiplication_laurentMonomial,
      leftComultiplication, rightComultiplication,
      leftDup, rightDup]

end
end QuaternionicSymmetry.ComplexTorusLaurentCoassociative
