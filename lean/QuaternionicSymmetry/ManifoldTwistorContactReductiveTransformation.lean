import QuaternionicSymmetry.ManifoldTwistorFullAutReductiveTransformationTarget
import QuaternionicSymmetry.ManifoldTwistorContactFullLieAlgebraEquiv
import QuaternionicSymmetry.LieCentralRadicalEquiv

/-! Under actual full preservation of the selected contact distribution,
the full-automorphism reductive transformation atlas transfers to the
literal contact automorphism group. Joint holomorphic evaluation and a
central Lie radical are proved in the same transported contact atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactReductiveTransformation

open ManifoldTwistorFullAutReductiveTransformationTarget
open ManifoldTwistorContactFullLieAlgebraEquiv
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open LieCentralRadicalEquiv
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

/-- A single genuine contact-group complex Lie structure with both joint
holomorphic action on the twistor and a central complex Lie radical. -/
def ContactReductiveTransformationConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  let G := ContactAutomorphisms Q D B L
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
      (hChart : ChartedSpace V G),
      letI : NormedSpace ℂ V := hSpace
      letI : FiniteDimensional ℂ V := hFinite
      letI : ChartedSpace V G := hChart
      ∃ hManifold : IsManifold 𝓘(ℂ,V) ∞ G,
        letI : IsManifold 𝓘(ℂ,V) ∞ G := hManifold
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ G,
          letI : LieGroup 𝓘(ℂ,V) ∞ G := hLie
          ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun p : G × SphereBundleTotal Q => p.1.1 p.2) ∧
          (letI : CompleteSpace V := FiniteDimensional.complete ℂ V
           letI : ENat.LEInfty (minSmoothness ℂ 3) := by
             simpa only [minSmoothness_of_isRCLikeNormedField] using
               (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
           letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) G :=
             LieGroup.of_le (ENat.LEInfty.out)
           LieAlgebra.HasCentralRadical ℂ (GroupLieAlgebra 𝓘(ℂ,V) G))

/-- BKK uniqueness yields the `hPreserve` premise on the Picard branch.
The Lie-algebra radical is then transported internally through the actual
contact/full group diffeomorphism and its proved LieEquiv. -/
theorem contactReductiveTransformation_of_full
    (hPreserve : FullPreservesContact Q D B L)
    (hFull : FullAutReductiveTransformationConclusion Q D B) :
    ContactReductiveTransformationConclusion Q D B L := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,hRad⟩ := hFull
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  letI : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms Q D B) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms Q D B) := hLie
  let hContactChart := contactCharts (V := V) Q D B L hPreserve
  letI : ChartedSpace V (ContactAutomorphisms Q D B L) := hContactChart
  let hContactManifold := contactManifold (V := V) Q D B L hPreserve
  letI : IsManifold 𝓘(ℂ,V) ∞
      (ContactAutomorphisms Q D B L) := hContactManifold
  let hContactLie := contactLieGroup (V := V) Q D B L hPreserve
  letI : LieGroup 𝓘(ℂ,V) ∞
      (ContactAutomorphisms Q D B L) := hContactLie
  have hContactJoint := contact_joint_holomorphic_of_full (V := V)
    Q D B L hPreserve hJoint
  have hContactRad :
      letI : ENat.LEInfty (minSmoothness ℂ 3) := by
        simpa only [minSmoothness_of_isRCLikeNormedField] using
          (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
      letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
          (ContactAutomorphisms Q D B L) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.HasCentralRadical ℂ
        (GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B L)) := by
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
  exact ⟨V,hNorm,hSpace,hFinite,hContactChart,hContactManifold,
    hContactLie,hContactJoint,hContactRad⟩

end
end QuaternionicSymmetry.ManifoldTwistorContactReductiveTransformation
