import QuaternionicSymmetry.ComplexProjectiveProjContinuous

/-! An actual injective projective map with homogeneous image equations
identifies its domain with the closed points of that image's Proj locus.
For a continuous original map this identification is continuous towards
the Zariski topology, not necessarily in the reverse direction. -/

namespace QuaternionicSymmetry.ComplexProjectiveRangeClosedPointEquiv

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveLineProjPoint ComplexProjectiveProjCutoutClosedPointEquiv
open ComplexProjectiveProjContinuous
noncomputable section

variable {X : Type*} [Nonempty X] {d : ℕ}

def rangeClosedPointEquiv (f : X → Space d) (hf : Function.Injective f)
    (hEq : HasHomogeneousEquations (Set.range f)) :
    X ≃ ClosedCutoutPoint (Set.range f) :=
  (Equiv.ofInjective f hf).trans
    (cutoutClosedPointEquiv (Set.range f) hEq (Set.range_nonempty f))

theorem rangeClosedPointEquiv_apply (f : X → Space d)
    (hf : Function.Injective f) (hEq : HasHomogeneousEquations (Set.range f))
    (x : X) :
    (rangeClosedPointEquiv f hf hEq x).1.1 = projectivePointToProj (f x) := rfl

theorem rangeClosedPointEquiv_continuous [TopologicalSpace X]
    (f : X → Space d) (hf : Function.Injective f)
    (hEq : HasHomogeneousEquations (Set.range f)) (hc : Continuous f) :
    Continuous (rangeClosedPointEquiv f hf hEq) :=
  ((projectivePointToProj_continuous.comp hc).subtype_mk _).subtype_mk _

end
end QuaternionicSymmetry.ComplexProjectiveRangeClosedPointEquiv
