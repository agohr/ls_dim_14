import QuaternionicSymmetry.HolomorphicLineCyclicCohomology

/-! The integral first Chern class of an actual represented holomorphic
line: its genuine unit-sheaf cocycle class followed by the boundary of the
proved exponential sequence. This homomorphism requires no cohomological
vanishing. No pairing with a fundamental class is stipulated here. -/

namespace QuaternionicSymmetry.HolomorphicLineIntegralChernClass

open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicExponentialCohomology HolomorphicLineCyclicCohomology
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def integralFirstChern :
    Additive (CoreClass.{0} (B := B) IB) →+
      integralCohomology (B := B) 2 :=
  (exponentialBoundary IB 1).comp
    (HolomorphicLineDerivedTensor.classAddEquiv IB).toAddMonoidHom

theorem integralFirstChern_pow (L : CoreClass.{0} (B := B) IB) (k : ℕ) :
    integralFirstChern IB (Additive.ofMul (L ^ k)) =
      k • integralFirstChern IB (Additive.ofMul L) := by
  rw [ofMul_pow, map_nsmul]

theorem integralFirstChern_zpow (L : CoreClass.{0} (B := B) IB) (k : ℤ) :
    integralFirstChern IB (Additive.ofMul (L ^ k)) =
      k • integralFirstChern IB (Additive.ofMul L) := by
  rw [ofMul_zpow, map_zsmul]

theorem lineClassIntegralEquiv_apply_eq_integralFirstChern
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1))
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2))
    (L : Additive (CoreClass.{0} (B := B) IB)) :
    lineClassIntegralEquiv IB hvan₁ hvan₂ L = integralFirstChern IB L := rfl

theorem integralFirstChern_injective
    (hvan₁ : Subsingleton (functionCohomology (B := B) IB 1)) :
    Function.Injective (integralFirstChern (B := B) IB) :=
  (exponentialBoundary_injective IB 1 hvan₁).comp
    (HolomorphicLineDerivedTensor.classAddEquiv IB).injective

theorem integralFirstChern_surjective
    (hvan₂ : Subsingleton (functionCohomology (B := B) IB 2)) :
    Function.Surjective (integralFirstChern (B := B) IB) :=
  (exponentialBoundary_surjective IB 1 hvan₂).comp
    (HolomorphicLineDerivedTensor.classAddEquiv IB).surjective

end
end QuaternionicSymmetry.HolomorphicLineIntegralChernClass
