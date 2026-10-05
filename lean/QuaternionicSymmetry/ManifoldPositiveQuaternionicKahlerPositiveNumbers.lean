import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerDensityNumbers

/-! Strict positivity of the resulting parameter-independent canonical numbers. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerPositiveNumbers
open Module QuaternionicClosedSourceNumbers
open ManifoldPositiveQuaternionicKahlerDensityNumbers
open ManifoldQuaternionicCanonicalIntegration ManifoldQuaternionicIntegralLowerBound
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : ManifoldPositiveQuaternionicKahlerGeometry.CompactConnectedPositiveQuaternionicKahlerGeometry
    (E := E) (M := M))

theorem density11_sourceNumber_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (s : ℝ) :
    0 < sourcePolynomialNumber S P.tangent P.connection s 10
      (show 4*(10+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) := by
  obtain ⟨t, htpos, hbound⟩ :=
    exists_density11_sourceNumber_bound S P hsource hsp heq38 hn b
  have hc : 0 < 288 * (t ^ 2 / Real.pi) ^ 22 := by positivity
  have hp : 0 < sourcePolynomialNumber S P.tangent P.connection t 10
      (show 4*(10+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density11) :=
    lt_of_lt_of_le (mul_pos hc (integral_topForm_pos P.tangent)) hbound
  rw [← sourcePolynomialNumber_parameter_independent S P.tangent P.connection s t 10]
  exact hp

theorem density12_sourceNumber_positive
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (s : ℝ) :
    0 < sourcePolynomialNumber S P.tangent P.connection s 11
      (show 4*(11+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) := by
  obtain ⟨t, htpos, hbound⟩ :=
    exists_density12_sourceNumber_bound S P hsource hsp heq38 hn b
  have hc : 0 < 336 * (t ^ 2 / Real.pi) ^ 24 := by positivity
  have hp : 0 < sourcePolynomialNumber S P.tangent P.connection t 11
      (show 4*(11+1) = Module.finrank ℝ E by
        have h := S.real_finrank; omega)
      (DimensionThirteenFourteenDensity.lift DimensionElevenTwelveDensity.density12) :=
    lt_of_lt_of_le (mul_pos hc (integral_topForm_pos P.tangent)) hbound
  rw [← sourcePolynomialNumber_parameter_independent S P.tangent P.connection s t 11]
  exact hp

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerPositiveNumbers
