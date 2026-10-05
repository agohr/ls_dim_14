import QuaternionicSymmetry.QuaternionicSevenTenActualDensity
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Source-relative canonical characteristic-number reserves in quaternionic
dimensions seven through ten. Their positivity uses only the checked finite
matrix polynomial signs; the literal orbital source premise is unnecessary. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerSevenTenNumbers
open Module QuaternionicSevenTenActualDensity QuaternionicSourceIntegralBound
open QuaternionicClosedSourceNumbers ManifoldQuaternionicIntegralLowerBound
open ManifoldQuaternionicCanonicalIntegration
open ManifoldQuaternionicVolumeCoefficient
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open PrintedCertificatesSevenTen LowerCertificateWeights
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem exists_density7_sourceNumber_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 7) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (128 * (t ^ 2 / Real.pi) ^ 14) *
        integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 6
        (show 4*(6+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift rhs7) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_lower_bound S P.tangent P.connection t 6
    (show 4*(6+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift rhs7) rhs7_weighted _
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density7_scalarDensity_bound S P.tangent P.connection
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h


theorem exists_density8_sourceNumber_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 8) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (160 * (t ^ 2 / Real.pi) ^ 16) *
        integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 7
        (show 4*(7+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift rhs8) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_lower_bound S P.tangent P.connection t 7
    (show 4*(7+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift rhs8) rhs8_weighted _
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density8_scalarDensity_bound S P.tangent P.connection
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

theorem exists_density9_sourceNumber_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 9) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (200 * (t ^ 2 / Real.pi) ^ 18) *
        integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 8
        (show 4*(8+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift rhs9) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_lower_bound S P.tangent P.connection t 8
    (show 4*(8+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift rhs9) rhs9_weighted _
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density9_scalarDensity_bound S P.tangent P.connection
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

theorem exists_density10_sourceNumber_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 10) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      (240 * (t ^ 2 / Real.pi) ^ 20) *
        integral P.tangent (volumeForm P.tangent) ≤
      sourcePolynomialNumber S P.tangent P.connection t 9
        (show 4*(9+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift rhs10) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_lower_bound S P.tangent P.connection t 9
    (show 4*(9+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift rhs10) rhs10_weighted _
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density10_scalarDensity_bound S P.tangent P.connection
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerSevenTenNumbers
