import QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization

/-! The genuine fiberwise holomorphic lift obeys a group action law on
the actual line-bundle total space. -/
namespace QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization

open HolomorphicLineCoreClasses TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

universe u
variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F X]
  (L : LineCore.{u} (B := X) 𝓘(ℂ,F)) {r : ℕ}

/-- A linearization is an actual complex-torus group action on the line
total space; the inverse is the lift of the inverse torus element. -/
def ComplexTorusLineLinearization.totalAction
    (lin : ComplexTorusLineLinearization L (r := r)) :
    ComplexTorus r →* Equiv.Perm (Bundle.TotalSpace ℂ L.core.Fiber) where
  toFun t := {
    toFun := lineTotalMap L lin.baseAction lin.fiberEquiv t
    invFun := lineTotalMap L lin.baseAction lin.fiberEquiv t⁻¹
    left_inv := by
      intro v
      rw [← lin.mul_total t⁻¹ t v, inv_mul_cancel, lin.one_total]
    right_inv := by
      intro v
      rw [← lin.mul_total t t⁻¹ v, mul_inv_cancel, lin.one_total] }
  map_one' := by
    apply Equiv.ext
    intro v
    change lineTotalMap L lin.baseAction lin.fiberEquiv 1 v = v
    exact lin.one_total v
  map_mul' s t := by
    apply Equiv.ext
    intro v
    change lineTotalMap L lin.baseAction lin.fiberEquiv (s * t) v =
      lineTotalMap L lin.baseAction lin.fiberEquiv s
        (lineTotalMap L lin.baseAction lin.fiberEquiv t v)
    exact lin.mul_total s t v

theorem ComplexTorusLineLinearization.totalAction_apply
    (lin : ComplexTorusLineLinearization L (r := r))
    (t : ComplexTorus r) (v : Bundle.TotalSpace ℂ L.core.Fiber) :
    lin.totalAction L t v = lineTotalMap L lin.baseAction lin.fiberEquiv t v := rfl

end
end QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization
