import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFixedWeights
import QuaternionicSymmetry.ManifoldQuaternionicContactIsotropyScalar
import QuaternionicSymmetry.ManifoldQuaternionicActualWeightHull
import QuaternionicSymmetry.TorusWeightSeparation

/-! A generating contact power identifies every actual fixed-point weight
with a scaled weight of its complete section representation. Consequently
the set of geometric weights is finite whenever that eigenbasis is finite.
Full affine span and existence of fixed points remain separate obligations. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerGeometricWeights

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerWeights ManifoldQuaternionicContactPowerFixedWeights
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactIsotropyScalar
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicTorusAction TorusWeightSeparation
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreProjectiveEvaluation
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
  {r : ℕ} (T : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
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

include hEigen hGen

theorem actualWeight_scaled_mem_sectionWeights {ν : Fin r → ℤ}
    (hν : ν ∈ actualIntegralWeights Q hR3 T) :
    k • ν ∈ Set.range μ := by
  obtain ⟨z,hz,hchar⟩ := hν
  obtain ⟨i,_,hi⟩ := exists_eigencharacter_at_fixedPoint Q T D B C k b μ hEigen hGen z hz
  refine ⟨i, weight_eq_of_character_eq ?_⟩
  intro t
  apply Subtype.ext
  have hc : contactScalar Q D C.line (T.representation t) z =
      (weightCharacter ν t : ℂ) := by
    rw [contactScalar_eq_verticalScalar Q D C.line z (T.representation t) (hz t)]
    exact congrArg (fun c : Circle => (c : ℂ)) (hchar t)
  rw [weightCharacter_nsmul]
  change (weightCharacter (μ i) t : ℂ) = (weightCharacter ν t : ℂ) ^ k
  rw [← hc]
  exact (hi t).symm

theorem actualIntegralWeights_finite [Finite ι] (hk : k ≠ 0) :
    (actualIntegralWeights Q hR3 T).Finite := by
  have himage : ((fun ν : Fin r → ℤ => k • ν) ''
      actualIntegralWeights Q hR3 T).Finite :=
    (Set.finite_range μ).subset (by
      rintro _ ⟨ν,hν,rfl⟩
      exact actualWeight_scaled_mem_sectionWeights Q hR3 T D B C k b μ hEigen hGen hν)
  exact himage.of_finite_image (nsmul_right_injective hk).injOn

theorem actualRealWeights_finite [Finite ι] (hk : k ≠ 0) :
    (actualRealWeights Q hR3 T).Finite :=
  (actualIntegralWeights_finite Q hR3 T D B C k b μ hEigen hGen hk).image _

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerGeometricWeights
