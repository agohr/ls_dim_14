import QuaternionicSymmetry.FourDimensionalExteriorTwoFormCanonicalTopology
import QuaternionicSymmetry.FourDimensionalExteriorQuaternionicUnitSurjective

/-! The normalized quaternionic operator-to-exterior-form map is continuous
for the genuine basis-independent finite-dimensional exterior topology. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorUnitMapContinuous

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorTwoFormTopology
open FourDimensionalExteriorTwoFormCanonicalTopology
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def normalizedSynthFormLinear (Q : QuaternionicStructure V)
    (b : Basis (Fin 4) ℝ V) :
    (Fin 3 → ℝ) →ₗ[ℝ] TwoForm V :=
  (Real.sqrt 2)⁻¹ • (operatorForm b).comp (synth Q).toLinearMap

theorem normalizedSynthFormLinear_apply (Q : QuaternionicStructure V)
    (b : Basis (Fin 4) ℝ V) (a : Fin 3 → ℝ) :
    normalizedSynthFormLinear Q b a =
      (Real.sqrt 2)⁻¹ • operatorForm b (synth Q a) := rfl

theorem normalizedSynthForm_continuous
    (Q : QuaternionicStructure V) (hdim : Module.finrank ℝ V = 4)
    (b : Basis (Fin 4) ℝ V) :
    @Continuous (Fin 3 → ℝ) (TwoForm V) inferInstance
      (canonicalTwoFormTopology hdim) (normalizedSynthFormLinear Q b) := by
  rw [canonicalTwoFormTopology_eq hdim b]
  apply continuous_induced_rng.mpr
  exact ((coordinates b).comp (normalizedSynthFormLinear Q b))
    |>.continuous_of_finiteDimensional

end
end QuaternionicSymmetry.FourDimensionalExteriorUnitMapContinuous
