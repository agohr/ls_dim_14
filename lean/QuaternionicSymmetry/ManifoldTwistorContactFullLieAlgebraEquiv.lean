import QuaternionicSymmetry.SmoothLieGroupEquivLieAlgebra
import QuaternionicSymmetry.ManifoldTwistorContactFullLieDerivative

/-! The literal contact/full group isomorphism, using the transported
complex Lie atlas on the contact group, induces an actual complex
Lie-algebra equivalence. This does not identify arbitrary other contact
group atlases. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactFullLieAlgebraEquiv

open SmoothLieGroupEquivLieAlgebra
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)
  (hPreserve : FullPreservesContact Q D B L)

/-- In the transported atlas, the differential of the genuine
contact-to-full group isomorphism preserves the full Lie bracket. -/
def contactFullLieEquiv
    [ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)]
    [LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B)] :
    letI := contactCharts (V := V) Q D B L hPreserve
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
    GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L) ≃ₗ⁅ℂ⁆
      GroupLieAlgebra 𝓘(ℂ,V) (TwistorHolomorphicAutomorphisms Q D B) := by
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
  let e := contactFullHomeomorph Q D B L hPreserve
  let Φ : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V)
      (ContactAutomorphisms Q D B L)
      (TwistorHolomorphicAutomorphisms Q D B) ∞ := {
    toEquiv := e.toEquiv
    contMDiff_toFun := ComplexHomeomorphLieAtlasTransfer.holomorphic_toFun e
    contMDiff_invFun := ComplexHomeomorphLieAtlasTransfer.holomorphic_invFun e }
  apply mfderiv_one_lieEquiv Φ
  · rfl
  · intro g x
    rfl

end
end QuaternionicSymmetry.ManifoldTwistorContactFullLieAlgebraEquiv
