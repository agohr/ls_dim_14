import QuaternionicSymmetry.ManifoldQuaternionicContactPowerGeometricWeights
import QuaternionicSymmetry.HolomorphicLineSectionRatios
import Mathlib.Topology.LocallyConstant.Basic

/-! The genuine integral vertical weight is locally constant on the actual
torus-fixed twistor locus. A nonvanishing eigenbasis section of a generating
positive contact power identifies the weight on an open neighborhood.
Preferred fiber coordinates are not assumed globally continuous. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedWeightLocalConstancy

open ManifoldQuaternionicTorusAction ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicContactPowerWeights ManifoldQuaternionicContactPowerFixedWeights
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactIsotropyScalar TorusWeightSeparation
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hCircle : TorusCharacterInput.CircleCharacterSource)
  {r : ℕ} (T : ContinuousTorusAction Q r)

abbrev FixedTwistor := {z : SphereBundleTotal Q // ∀ t, T.representation t • z = z}

def fixedPointWeight (z : FixedTwistor Q T) : Fin r → ℤ :=
  Classical.choose (TorusCharacterInput.exists_weightCharacter hCircle
    (torusVerticalCircleCharacter Q hR3 T z.1 z.2))

theorem fixedPointWeight_spec (z : FixedTwistor Q T) (t : Torus r) :
    torusVerticalCircleCharacter Q hR3 T z.1 z.2 t =
      weightCharacter (fixedPointWeight Q hR3 hCircle T z) t :=
  Classical.choose_spec (TorusCharacterInput.exists_weightCharacter hCircle
    (torusVerticalCircleCharacter Q hR3 T z.1 z.2)) t

variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B) (k : ℕ)
  {ι : Type*} (b : letI := B.charts; Module.Basis ι ℂ (PowerSections Q D B C k))
  (μ : ι → Fin r → ℤ)
  (hEigen : letI := B.charts
    ∀ (t : Torus r) (i : ι), contactPowerTorusRepresentation Q T D B C k t (b i) =
      (weightCharacter (μ i) t : ℂ) • b i)
  (hGen : letI := B.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))

include hEigen in
theorem scaledWeight_eq_of_section_nonzero
    (z : FixedTwistor Q T) (i : ι) (hi : b i z.1 ≠ 0) :
    k • fixedPointWeight Q hR3 hCircle T z = μ i := by
  apply weight_eq_of_character_eq
  intro t
  apply Subtype.ext
  rw [weightCharacter_nsmul]
  change (weightCharacter (fixedPointWeight Q hR3 hCircle T z) t : ℂ) ^ k = _
  have hc : contactScalar Q D C.line (T.representation t) z.1 =
      (weightCharacter (fixedPointWeight Q hR3 hCircle T z) t : ℂ) := by
    rw [contactScalar_eq_verticalScalar Q D C.line z.1 (T.representation t) (z.2 t)]
    exact congrArg (fun c : Circle => (c : ℂ))
      (fixedPointWeight_spec Q hR3 hCircle T z t)
  rw [← hc]
  exact fixedPoint_powerScalar_eq_eigencharacter Q T D B C k
    (b i) (μ i) (fun t => hEigen t i) z.1 z.2 hi t

include hEigen hGen in
theorem fixedPointWeight_isLocallyConstant (hk : k ≠ 0) :
    IsLocallyConstant (fixedPointWeight Q hR3 hCircle T) := by
  letI := B.charts
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  obtain ⟨i,hi⟩ := exists_basis_section_nonzero Q D B C k b hGen z.1
  let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k
  let U : Set (FixedTwistor Q T) := {w | b i w.1 ≠ 0}
  have hU : IsOpen U :=
    (HolomorphicLineSectionRatios.isOpen_nonzeroSet
      𝓘(ℂ,ComplexTwistorModel n) L (b i)).preimage continuous_subtype_val
  refine ⟨U,hU,hi,?_⟩
  intro w hw
  apply nsmul_right_injective hk
  exact (scaledWeight_eq_of_section_nonzero Q hR3 hCircle T D B C k b μ hEigen w i hw).trans
    (scaledWeight_eq_of_section_nonzero Q hR3 hCircle T D B C k b μ hEigen z i hi).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedWeightLocalConstancy
