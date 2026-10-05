import QuaternionicSymmetry.FourDimensionalExteriorUnitInverseContinuous
import QuaternionicSymmetry.ManifoldTwistorSphereBundle

/-! The coordinate coefficient sphere and the reversed-Hodge negative unit
sphere of genuine exterior forms are homeomorphic in each Q-frame, using the
canonical basis-independent exterior topology. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorUnitSphereHomeomorphism

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorQuaternionicUnitSphere
open FourDimensionalExteriorQuaternionicUnitSurjective
open FourDimensionalExteriorTwoFormCanonicalTopology
open FourDimensionalExteriorUnitMapContinuous
open FourDimensionalExteriorUnitInverse
open FourDimensionalExteriorUnitInverseContinuous
open FourDimensionalQuaternionicHodgeFrame
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

def negativeUnitHalfTopology (hdim : Module.finrank ℝ V = 4)
    (b : OrthonormalBasis (Fin 4) ℝ V) :
    TopologicalSpace (negativeUnitHalf b) :=
  TopologicalSpace.induced Subtype.val (canonicalTwoFormTopology hdim)

def unitFormMap (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    coefficientSphere → negativeUnitHalf (frameBasis Q hdim v hv) := by
  intro a
  refine ⟨(Real.sqrt 2)⁻¹ •
    operatorForm (frameBasis Q hdim v hv).toBasis (synth Q a.1), ?_⟩
  exact normalized_synth_in_negativeUnitHalf Q hdim v hv a.1 a.2

def unitFormInverse (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    negativeUnitHalf (frameBasis Q hdim v hv) → coefficientSphere := by
  intro α
  refine ⟨inverseCoefficients (frameBasis Q hdim v hv).toBasis α.1, ?_⟩
  exact (inverseCoefficients_negativeUnitHalf Q hdim v hv α).1

theorem unitFormInverse_left (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (a : coefficientSphere) :
    unitFormInverse Q hdim v hv (unitFormMap Q hdim v hv a) = a := by
  apply Subtype.ext
  exact inverseCoefficients_normalized_synth Q hdim v hv a.1

theorem unitFormInverse_right (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1)
    (α : negativeUnitHalf (frameBasis Q hdim v hv)) :
    unitFormMap Q hdim v hv (unitFormInverse Q hdim v hv α) = α := by
  apply Subtype.ext
  exact (inverseCoefficients_negativeUnitHalf Q hdim v hv α).2

theorem unitFormMap_continuous (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    @Continuous coefficientSphere
      (negativeUnitHalf (frameBasis Q hdim v hv)) inferInstance
      (negativeUnitHalfTopology hdim (frameBasis Q hdim v hv))
      (unitFormMap Q hdim v hv) := by
  letI : TopologicalSpace (TwoForm V) := canonicalTwoFormTopology hdim
  letI : TopologicalSpace (negativeUnitHalf (frameBasis Q hdim v hv)) :=
    negativeUnitHalfTopology hdim (frameBasis Q hdim v hv)
  apply continuous_induced_rng.mpr
  change @Continuous coefficientSphere (TwoForm V) inferInstance
    (canonicalTwoFormTopology hdim)
    (fun a => normalizedSynthFormLinear Q (frameBasis Q hdim v hv).toBasis a.1)
  exact (normalizedSynthForm_continuous Q hdim _).comp continuous_subtype_val

theorem unitFormInverse_continuous (Q : QuaternionicStructure V)
    (hdim : Module.finrank ℝ V = 4) (v : V) (hv : ‖v‖ = 1) :
    @Continuous (negativeUnitHalf (frameBasis Q hdim v hv))
      coefficientSphere
      (negativeUnitHalfTopology hdim (frameBasis Q hdim v hv)) inferInstance
      (unitFormInverse Q hdim v hv) := by
  letI : TopologicalSpace (TwoForm V) := canonicalTwoFormTopology hdim
  letI : TopologicalSpace (negativeUnitHalf (frameBasis Q hdim v hv)) :=
    negativeUnitHalfTopology hdim (frameBasis Q hdim v hv)
  apply Continuous.subtype_mk
  change @Continuous (negativeUnitHalf (frameBasis Q hdim v hv))
    (Fin 3 → ℝ) (negativeUnitHalfTopology hdim _) inferInstance
      (fun α => inverseCoefficients (frameBasis Q hdim v hv).toBasis α.1)
  exact (inverseCoefficients_continuous hdim _).comp continuous_induced_dom

end
end QuaternionicSymmetry.FourDimensionalExteriorUnitSphereHomeomorphism
