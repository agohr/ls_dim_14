import QuaternionicSymmetry.ManifoldTwistorContactFullLieAlgebraEquiv
import QuaternionicSymmetry.LieCentralRadicalEquiv

/-! Direct radical transfer in one *supplied full-automorphism atlas*.
Unlike an existential contact-group package, this theorem retains the
full chart and its literally transported contact chart for later
Hamiltonian and weight calculations. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactFullSelectedRadical

open ManifoldTwistorContactFullLieAlgebraEquiv
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open LieCentralRadicalEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)
  (hPreserve : FullPreservesContact Q D B L)

/-- Full reductivity and contact reductivity use the very same selected
full Lie atlas and its explicit contact pullback. -/
theorem contact_hasCentralRadical_of_full_atlas
    [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)]
    (hRad :
      letI : ENat.LEInfty (minSmoothness ℂ 3) := by
        simpa only [minSmoothness_of_isRCLikeNormedField] using
          (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
      letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
          (TwistorHolomorphicAutomorphisms Q D B) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.HasCentralRadical ℂ
        (GroupLieAlgebra 𝓘(ℂ,V)
          (TwistorHolomorphicAutomorphisms Q D B))) :
    letI := contactCharts (V := V) Q D B L hPreserve
    letI := contactLieGroup (V := V) Q D B L hPreserve
    letI : ENat.LEInfty (minSmoothness ℂ 3) := by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
    letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
        (ContactAutomorphisms Q D B L) :=
      LieGroup.of_le (ENat.LEInfty.out)
    LieAlgebra.HasCentralRadical ℂ
      (GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L)) := by
  letI := contactCharts (V := V) Q D B L hPreserve
  letI := contactManifold (V := V) Q D B L hPreserve
  letI := contactLieGroup (V := V) Q D B L hPreserve
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
      (TwistorHolomorphicAutomorphisms Q D B) :=
    LieGroup.of_le (ENat.LEInfty.out)
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
      (ContactAutomorphisms Q D B L) :=
    LieGroup.of_le (ENat.LEInfty.out)
  letI : FiniteDimensional ℂ
      (GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L)) := by
    unfold GroupLieAlgebra TangentSpace
    infer_instance
  exact hasCentralRadical_of_lieEquiv
    (contactFullLieEquiv (V := V) Q D B L hPreserve) hRad

end
end QuaternionicSymmetry.ManifoldTwistorContactFullSelectedRadical
