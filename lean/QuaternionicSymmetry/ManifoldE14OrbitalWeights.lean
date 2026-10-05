import QuaternionicSymmetry.ManifoldSevenVariableWeightedDensity

/-! The complete orbital remainders have the actual top degree. This is
deduced from the checked density identity and the witness-square degree,
without expanding the large rational orbital coefficients. -/
namespace QuaternionicSymmetry.ManifoldE14OrbitalWeights
open MvPolynomial DimensionThirteenFourteenDensity
  ManifoldSevenVariableWeightedDensity ManifoldSevenVariableGradedEvaluation
noncomputable section

theorem u_weighted : IsWeightedHomogeneous slotGrade u 1 :=
  isWeightedHomogeneous_X (R := ℚ) slotGrade 0

private theorem weighted_sub {p q : P} {n : ℕ}
    (hp : IsWeightedHomogeneous slotGrade p n)
    (hq : IsWeightedHomogeneous slotGrade q n) :
    IsWeightedHomogeneous slotGrade (p - q) n :=
  (weightedHomogeneousSubmodule ℚ slotGrade n).sub_mem hp hq

theorem orbitalSum13_weighted :
    IsWeightedHomogeneous slotGrade H2WitnessThirteen.orbitalSum 13 := by
  have he : H2WitnessThirteen.orbitalSum =
      density13 - C 392 * u ^ 13 -
        C 18 * (H2WitnessThirteen.factor ^ 2 * u ^ 7) := by
    rw [H2WitnessThirteen.density13_witness]
    unfold H2WitnessThirteen.witness
    ring
  rw [he]
  exact weighted_sub (weighted_sub density13_weighted (by
    simpa using (u_weighted.pow 13).C_mul 392)) (by
      simpa using ((factor13_weighted.pow 2).mul
        (u_weighted.pow 7)).C_mul 18)

theorem orbitalSum14_weighted :
    IsWeightedHomogeneous slotGrade H2WitnessFourteen.orbitalSum 14 := by
  have he : H2WitnessFourteen.orbitalSum =
      density14 - C 448 * u ^ 14 -
        C 20 * (H2WitnessFourteen.factor ^ 2 * u ^ 8) := by
    rw [H2WitnessFourteen.density14_witness]
    unfold H2WitnessFourteen.witness
    ring
  rw [he]
  exact weighted_sub (weighted_sub density14_weighted (by
    simpa using (u_weighted.pow 14).C_mul 448)) (by
      simpa using ((factor14_weighted.pow 2).mul
        (u_weighted.pow 8)).C_mul 20)

end
end QuaternionicSymmetry.ManifoldE14OrbitalWeights
