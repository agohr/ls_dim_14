import QuaternionicSymmetry.QuaternionicClosedDensityNumbers
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Source-relative integral certificates for natural compact connected positive
quaternionic Kähler geometry. Scalar constancy is derived internally by Schur. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerDensityNumbers
open Module QuaternionicClosedDensityNumbers QuaternionicClosedSourceNumbers
open ManifoldQuaternionicDensityIntegrals ManifoldQuaternionicIntegralLowerBound
open ManifoldQuaternionicCanonicalIntegration
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem exists_density11_sourceNumber_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (288 * (t ^ 2 / Real.pi) ^ 22) * integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 10
        (show 4*(10+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  rw [density11_sourceNumber_eq_integral S P.tangent P.connection hn t]
  exact density11_integral_lower_bound S P.tangent P.connection hsource
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm)

theorem exists_density12_sourceNumber_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (336 * (t ^ 2 / Real.pi) ^ 24) * integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 11
        (show 4*(11+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  rw [density12_sourceNumber_eq_integral S P.tangent P.connection hn t]
  exact density12_integral_lower_bound S P.tangent P.connection hsource
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm)

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerDensityNumbers
