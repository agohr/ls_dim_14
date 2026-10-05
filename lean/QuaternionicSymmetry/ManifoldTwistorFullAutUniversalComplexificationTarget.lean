import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismIdentityLie
import QuaternionicSymmetry.CompactRealFormUniversalComplexification

/-! A literal group-level complexification target for BWW 6.5 on the
actual full twistor biholomorphism identity component. Unlike an
infinitesimal dimension condition, it asks for unique holomorphic
extensions of all continuous homomorphisms out of the compact isometry
identity component. No source application is claimed here. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutUniversalComplexificationTarget

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutomorphismIdentityComponent
open ManifoldTwistorFullAutomorphismLieTarget
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicSpanSymmetry
open IdentityComponentLie
open CompactRealFormUniversalComplexification
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})

def FullAutUniversalComplexificationConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V),
      letI : NormedSpace ℂ V := hSpace
      ∃ (hFinite : FiniteDimensional ℂ V)
        (hChart : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B)),
        letI : FiniteDimensional ℂ V := hFinite
        letI : ChartedSpace V (TwistorHolomorphicAutomorphisms Q D B) := hChart
        IsManifold 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B) ∧
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ (TwistorHolomorphicAutomorphisms Q D B),
          letI : LieGroup 𝓘(ℂ,V) ∞
              (TwistorHolomorphicAutomorphisms Q D B) := hLie
          letI : ChartedSpace V
              (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
            ComplexIdentityComponentLie.charts V
              (TwistorHolomorphicAutomorphisms Q D B)
          letI : LieGroup 𝓘(ℂ,V) ∞
              (Component (TwistorHolomorphicAutomorphisms Q D B)) :=
            ComplexIdentityComponentLie.lieGroup V
              (TwistorHolomorphicAutomorphisms Q D B)
          IsUniversalComplexification (VC := V)
            (isometryIdentityLift Q D B L hR3)

theorem fullAutComplexLie_of_universal
    (h : FullAutUniversalComplexificationConclusion Q D B L hR3) :
    FullAutComplexLieConclusion Q D B := by
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,_⟩ := h
  exact ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie⟩

end
end QuaternionicSymmetry.ManifoldTwistorFullAutUniversalComplexificationTarget
