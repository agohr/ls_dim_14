import QuaternionicSymmetry.FourDimensionalExteriorUnitInverse

/-! The explicit quaternionic coefficient extraction is continuous for the
basis-independent finite-dimensional topology of genuine exterior forms. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorUnitInverseContinuous

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormCanonicalTopology
open FourDimensionalExteriorUnitInverse
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def firstThreeLinear :
    FourDimensionalCoordinateHodge.Two →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := firstThree
  map_add' x y := by funext t; rfl
  map_smul' r x := by funext t; rfl

def inverseCoefficientsLinear (b : Basis (Fin 4) ℝ V) :
    TwoForm V →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Real.sqrt 2) • (firstThreeLinear.comp (coordinates b))

theorem inverseCoefficientsLinear_apply (b : Basis (Fin 4) ℝ V)
    (α : TwoForm V) :
    inverseCoefficientsLinear b α = inverseCoefficients b α := rfl

theorem inverseCoefficients_continuous
    (hdim : Module.finrank ℝ V = 4) (b : Basis (Fin 4) ℝ V) :
    @Continuous (TwoForm V) (Fin 3 → ℝ)
      (canonicalTwoFormTopology hdim) inferInstance
      (inverseCoefficients b) := by
  letI : TopologicalSpace (TwoForm V) := canonicalTwoFormTopology hdim
  change @Continuous (TwoForm V) (Fin 3 → ℝ)
    (canonicalTwoFormTopology hdim) inferInstance
    (fun α => ((Real.sqrt 2) • firstThreeLinear) (coordinates b α))
  exact ((Real.sqrt 2) • firstThreeLinear).continuous_of_finiteDimensional.comp
    (continuous_coordinates hdim b)

end
end QuaternionicSymmetry.FourDimensionalExteriorUnitInverseContinuous
