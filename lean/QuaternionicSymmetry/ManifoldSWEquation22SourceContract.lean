import QuaternionicSymmetry.ManifoldSWEquation22PQK

/-! Universal source-facing form of Semmelmann--Weingart §2 Eq. (2.2).
Only actual positive quaternionic-Kähler geometry and individual symmetric
powers occur in the source statement. Categorical Ext/sheafification
infrastructure is kept as typeclass context, not asserted by the source. -/
namespace QuaternionicSymmetry.ManifoldSWEquation22SourceContract
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldSWEquation22PQK ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe w

def SWEquation22Source : Prop :=
  ∀ {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M]
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (A : CompatibleComplexAtlas P.tangent P.connection S.quaternionicDimension)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection
      S.quaternionicDimension A)
    [HasSheafify (Opens.grothendieckTopology
      (TopCat.of (SphereBundleTotal P.tangent))) (ModuleCat ℂ)]
    [HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
      (TopCat.of (SphereBundleTotal P.tangent)))],
    SWEquation22OnPQK S P A C

end
end QuaternionicSymmetry.ManifoldSWEquation22SourceContract
