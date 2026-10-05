import QuaternionicSymmetry.DimensionElevenTwelveDensity

/-! Weighted homogeneity of the complete printed densities after evaluation
in any rational commutative algebra, including exterior forms. -/
namespace QuaternionicSymmetry.ElevenTwelveDensityScaling
open MvPolynomial DimensionElevenTwelveDensity
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def weightedValues (r : R) (v : Fin 6 → R) : Fin 6 → R :=
  ![r * v 0, r * v 1, r ^ 2 * v 2, r ^ 3 * v 3, r ^ 4 * v 4, r ^ 5 * v 5]

theorem density11_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) density11 = r ^ 11 * aeval v density11 := by
  rw [density11_printed]
  simp [printed11, q11, f5, u, p1, p2, p3, p4, p5, weightedValues]
  ring

theorem density12_eval_scale (r : R) (v : Fin 6 → R) :
    aeval (weightedValues r v) density12 = r ^ 12 * aeval v density12 := by
  rw [density12_printed]
  simp [printed12, q12, f5, u, p1, p2, p3, p4, p5, weightedValues]
  ring

end
end QuaternionicSymmetry.ElevenTwelveDensityScaling
