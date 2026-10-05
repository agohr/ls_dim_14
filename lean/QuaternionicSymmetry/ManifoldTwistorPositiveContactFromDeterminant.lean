import QuaternionicSymmetry.ManifoldTwistorSquaredCanonical
import QuaternionicSymmetry.HolomorphicLineHermitianGaugeCurvature

/-! Positivity of the contact line follows from the internally proved squared
canonical relation and the existing Hermitian positive-root construction. -/
namespace QuaternionicSymmetry.ManifoldTwistorPositiveContactFromDeterminant
open ManifoldTwistorSquaredCanonical ManifoldTwistorLeBrunComplexAtlas
  ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
  ManifoldQuaternionicMetric ManifoldQuaternionicConnection
  HolomorphicLineCoreClasses HolomorphicLineTensorPowerClasses
  HolomorphicLineHermitianMetric HolomorphicLineHermitianPositiveRoot
  HolomorphicLineHermitianGauge HolomorphicLineHermitianGaugeCurvature
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem exists_positive_contact_metric {n : ℕ} {A : CompatibleComplexAtlas Q D n}
    (C : NondegenerateHolomorphicContactData Q D n A)
    (mK : letI := A.charts; HermitianLineMetric (anticanonicalLineCore Q D A))
    (hmK : letI := A.charts; mK.PositiveChernCurvature) :
    letI := A.charts
    ∃ mL : HermitianLineMetric (contactLineCore Q D C.contact.line),
      mL.PositiveChernCurvature := by
  letI := A.charts
  letI := A.complexManifold
  let K := anticanonicalLineCore Q D A
  let L := contactLineCore Q D C.contact.line
  let K₂ := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) K 2
  let Lp := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) L (2*(n+1))
  letI := K₂.holomorphic
  letI := Lp.holomorphic
  have hIso : Isomorphic 𝓘(ℂ,ComplexTwistorModel n) Lp K₂ := by
    obtain ⟨e⟩ := squaredCanonical_isomorphic Q D C
    exact ⟨e.symm⟩
  let m₂ := mK.powerMetric K 2
  have hm₂ : m₂.PositiveChernCurvature K₂ := mK.powerMetric_positive K 2 (by decide) hmK
  let p := gaugePullbackMetric Lp K₂ hIso m₂
  have hp : p.PositiveChernCurvature Lp := gaugePullbackMetric_positive Lp K₂ hIso m₂ hm₂
  exact ⟨rootMetric L (2*(n+1)) (by omega) p,
    rootMetric_positive L (2*(n+1)) (by omega) p hp⟩

end
end QuaternionicSymmetry.ManifoldTwistorPositiveContactFromDeterminant
