import QuaternionicSymmetry.QuaternionicDensityQuarterBounds
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerPositiveNumbers

/-! Canonical C12 density bounds on natural compact connected PQK geometry,
in the paper's quarter-class normalization and at any correction parameter. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuarterBounds
open QuaternionicDensityQuarterBounds QuaternionicClosedSourceNumbers
open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicCanonicalIntegration
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem density11_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) (s : ℝ) :
    288 * integral P.tangent (quarterTop P.tangent P.connection 11
      (by have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection s 10
        (by have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  exact density11_sourceNumber_quarter_bound S P.tangent P.connection hsource
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2) hd hn t htpos
      (fun p y hy => (ht p y hy).symm) s

theorem density12_quarter_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) (s : ℝ) :
    336 * integral P.tangent (quarterTop P.tangent P.connection 12
      (by have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection s 11
        (by have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  exact density12_sourceNumber_quarter_bound S P.tangent P.connection hsource
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2) hd hn t htpos
      (fun p y hy => (ht p y hy).symm) s

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuarterBounds
