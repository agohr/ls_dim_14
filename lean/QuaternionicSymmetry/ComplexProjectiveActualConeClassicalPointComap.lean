import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPoint

/-! The quotient-Proj point attached to a classical line has precisely the
ambient line prime as its pullback along the homogeneous cone quotient. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointComap

open ComplexProjectiveTopology ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveLineProjPoint
open ComplexProjectiveActualConeClassicalPoint
noncomputable section

variable {d : ℕ}

theorem quotientLinePrime_comap (A : Set (Space d))
    (x : Space d) (hx : x ∈ A) :
    Ideal.comap (Ideal.Quotient.mk (vanishingIdeal A))
      (quotientLinePrime A x hx) = linePrimeIdeal x.rep := by
  ext p
  change quotientLineEval A x hx
    (Ideal.Quotient.mk (vanishingIdeal A) p) = 0 ↔
    lineEval x.rep p = 0
  rw [quotientLineEval_mk]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalPointComap
