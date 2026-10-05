import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberTopology
import QuaternionicSymmetry.FourDimensionalExteriorUnitInverseContinuous

/-! The actual local coefficient sphere and the tangent negative-Hodge unit
sphere have continuous maps in both directions for the canonical exterior
topology. The inverse uses explicit first-three coefficient extraction. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberHomeomorphism

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorTwoFormCanonicalTopology
open FourDimensionalExteriorPullbackContinuous
open FourDimensionalExteriorUnitInverse
open FourDimensionalExteriorUnitInverseContinuous
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourNegativeHodgeSphere
open ManifoldQuaternionicFourHodgeFiberEquiv
open ManifoldQuaternionicFourHodgeFiberTopology
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

def localCoefficientRaw (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      θ ∈ negativeTangentUnitHalf Q hdim x}) : Fin 3 → ℝ :=
  inverseCoefficients (localBasis Q hdim i)
    (ManifoldQuaternionicFourHodgeOverlapExterior.pullbackTwoForm
      (localBasis Q hdim i)
      (localToTangentEquiv Q i x hi).toLinearMap α.1)

theorem localCoefficientRaw_map (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : coefficientSphere) :
    localCoefficientRaw Q hdim i x hi
      (localHodgeSphereMap Q hdim i x hi a) = a.1 := by
  change inverseCoefficients (localBasis Q hdim i)
    (ManifoldQuaternionicFourHodgeOverlapExterior.pullbackTwoForm
      (localBasis Q hdim i)
      (localToTangentEquiv Q i x hi).toLinearMap
      (localTangentTwoForm Q hdim i x hi a.1)) = a.1
  rw [localTangentTwoForm_pullback]
  exact inverseCoefficients_normalized_synth
    (Q.reduction.Q i) hdim (unit : E) unit_norm a.1

theorem localCoefficientRaw_unit (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      θ ∈ negativeTangentUnitHalf Q hdim x}) :
    FourDimensionalExteriorQuaternionicUnitSphere.coefficientSquare
      (localCoefficientRaw Q hdim i x hi α) = 1 := by
  obtain ⟨a,ha⟩ := localHodgeSphereMap_surjective Q hdim i x hi α
  rw [← ha, localCoefficientRaw_map]
  exact a.2

def localHodgeSphereInverse (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      θ ∈ negativeTangentUnitHalf Q hdim x} → coefficientSphere :=
  fun α => ⟨localCoefficientRaw Q hdim i x hi α,
    localCoefficientRaw_unit Q hdim i x hi α⟩

theorem localHodgeSphereInverse_left (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (a : coefficientSphere) :
    localHodgeSphereInverse Q hdim i x hi
      (localHodgeSphereMap Q hdim i x hi a) = a := by
  apply Subtype.ext
  exact localCoefficientRaw_map Q hdim i x hi a

theorem localHodgeSphereInverse_right (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (α : {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      θ ∈ negativeTangentUnitHalf Q hdim x}) :
    localHodgeSphereMap Q hdim i x hi
      (localHodgeSphereInverse Q hdim i x hi α) = α := by
  obtain ⟨a,ha⟩ := localHodgeSphereMap_surjective Q hdim i x hi α
  rw [← ha, localHodgeSphereInverse_left]

theorem localHodgeSphereInverse_continuous (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    @Continuous
      {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        θ ∈ negativeTangentUnitHalf Q hdim x}
      coefficientSphere (negativeTangentUnitHalfTopology Q hdim x)
      inferInstance (localHodgeSphereInverse Q hdim i x hi) := by
  letI : TopologicalSpace (TwoForm E) := canonicalTwoFormTopology hdim
  letI : TopologicalSpace
      {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        θ ∈ negativeTangentUnitHalf Q hdim x} :=
    negativeTangentUnitHalfTopology Q hdim x
  let b := localBasis Q hdim i
  let T : E →ₗ[ℝ] E :=
    (localToTangentEquiv Q i x hi).toLinearMap
  apply Continuous.subtype_mk
  change @Continuous
      {θ : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        θ ∈ negativeTangentUnitHalf Q hdim x}
      (Fin 3 → ℝ) (negativeTangentUnitHalfTopology Q hdim x)
      inferInstance
      (fun α => inverseCoefficients b (pullbackTwoFormLinear b T α.1))
  exact (inverseCoefficients_continuous hdim b).comp
    ((pullbackTwoFormLinear_continuous hdim b T).comp
      continuous_induced_dom)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberHomeomorphism
