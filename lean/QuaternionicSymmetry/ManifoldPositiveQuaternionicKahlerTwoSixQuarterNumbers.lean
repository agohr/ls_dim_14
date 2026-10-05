import QuaternionicSymmetry.QuaternionicTwoSixClosedDensityForms
import QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient
import QuaternionicSymmetry.QuaternionicDensityCoefficient
import QuaternionicSymmetry.QuaternionicSourceQuarterBound
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Canonical actual characteristic-number reserves in quaternionic dimensions
two through six. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerTwoSixQuarterNumbers
open Module QuaternionicTwoSixClosedDensityForms
open ManifoldEvenClosedEvaluation ManifoldQuaternionicGradeDensityCoefficient
open ManifoldQuaternionicVolumeCoefficient QuaternionicSourceIntegralBound
open QuaternionicSourceQuarterBound QuaternionicClosedSourceNumbers
open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicCanonicalIntegration
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open QuaternionicFundamental LowerCertificateWeights
open PrintedTwoSixLinearAssembly ReconstructionExamples
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem density2_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S P.tangent P.connection)
    (hdecomp : KSWEq38Decomposition S P.tangent P.connection)
    (hn : S.quaternionicDimension = 2) (b : Basis ι ℝ E)
    (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S P.tangent P.connection p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    16 * (t ^ 2 / Real.pi) ^ 4 ≤
      scalarDensity P.tangent
        (sourceTopForm S P.tangent P.connection t 1
          (show 4*(1+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift density2) density2_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 2
      (density2Form S P.tangent P.connection t)) 16 (t ^ 2 / Real.pi)
      (fun F hF => by
        simpa only [hn] using
          density2Form_pointwise_bound S P.tangent P.connection
            hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(1+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 2
      (density2Form S P.tangent P.connection t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S P.tangent b 1 hdim
    (density2Form S P.tangent P.connection t) p y hy r).mp he'
  simpa only [sourceTopForm, density2Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

theorem exists_density2_sourceNumber_quarter_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 2) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      16 * integral P.tangent
        (quarterTop P.tangent P.connection 2
          (show 4*2 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection t 1
        (show 4*(1+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift density2) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_quarter_lower_bound S P.tangent P.connection t 1
    (show 4*(1+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift density2) density2_weighted 16
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    (fun p y hy => (ht p y hy).symm)
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density2_scalarDensity_bound S P
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem density3_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S P.tangent P.connection)
    (hdecomp : KSWEq38Decomposition S P.tangent P.connection)
    (hn : S.quaternionicDimension = 3) (b : Basis ι ℝ E)
    (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S P.tangent P.connection p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    32 * (t ^ 2 / Real.pi) ^ 6 ≤
      scalarDensity P.tangent
        (sourceTopForm S P.tangent P.connection t 2
          (show 4*(2+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift density3) density3_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 3
      (density3Form S P.tangent P.connection t)) 32 (t ^ 2 / Real.pi)
      (fun F hF => by
        simpa only [hn] using
          density3Form_pointwise_bound S P.tangent P.connection
            hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(2+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 3
      (density3Form S P.tangent P.connection t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S P.tangent b 2 hdim
    (density3Form S P.tangent P.connection t) p y hy r).mp he'
  simpa only [sourceTopForm, density3Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

theorem exists_density3_sourceNumber_quarter_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 3) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      32 * integral P.tangent
        (quarterTop P.tangent P.connection 3
          (show 4*3 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection t 2
        (show 4*(2+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift density3) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_quarter_lower_bound S P.tangent P.connection t 2
    (show 4*(2+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift density3) density3_weighted 32
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    (fun p y hy => (ht p y hy).symm)
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density3_scalarDensity_bound S P
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem density4_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S P.tangent P.connection)
    (hdecomp : KSWEq38Decomposition S P.tangent P.connection)
    (hn : S.quaternionicDimension = 4) (b : Basis ι ℝ E)
    (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S P.tangent P.connection p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    48 * (t ^ 2 / Real.pi) ^ 8 ≤
      scalarDensity P.tangent
        (sourceTopForm S P.tangent P.connection t 3
          (show 4*(3+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift density4) density4_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 4
      (density4Form S P.tangent P.connection t)) 48 (t ^ 2 / Real.pi)
      (fun F hF => by
        simpa only [hn] using
          density4Form_pointwise_bound S P.tangent P.connection
            hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(3+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 4
      (density4Form S P.tangent P.connection t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S P.tangent b 3 hdim
    (density4Form S P.tangent P.connection t) p y hy r).mp he'
  simpa only [sourceTopForm, density4Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

theorem exists_density4_sourceNumber_quarter_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 4) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      48 * integral P.tangent
        (quarterTop P.tangent P.connection 4
          (show 4*4 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection t 3
        (show 4*(3+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift density4) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_quarter_lower_bound S P.tangent P.connection t 3
    (show 4*(3+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift density4) density4_weighted 48
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    (fun p y hy => (ht p y hy).symm)
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density4_scalarDensity_bound S P
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem density5_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S P.tangent P.connection)
    (hdecomp : KSWEq38Decomposition S P.tangent P.connection)
    (hn : S.quaternionicDimension = 5) (b : Basis ι ℝ E)
    (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S P.tangent P.connection p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    72 * (t ^ 2 / Real.pi) ^ 10 ≤
      scalarDensity P.tangent
        (sourceTopForm S P.tangent P.connection t 4
          (show 4*(4+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift k5) density5_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 5
      (density5Form S P.tangent P.connection t)) 72 (t ^ 2 / Real.pi)
      (fun F hF => by
        simpa only [hn] using
          density5Form_pointwise_bound S P.tangent P.connection
            hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(4+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 5
      (density5Form S P.tangent P.connection t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S P.tangent b 4 hdim
    (density5Form S P.tangent P.connection t) p y hy r).mp he'
  simpa only [sourceTopForm, density5Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

theorem exists_density5_sourceNumber_quarter_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 5) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      72 * integral P.tangent
        (quarterTop P.tangent P.connection 5
          (show 4*5 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection t 4
        (show 4*(4+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift k5) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_quarter_lower_bound S P.tangent P.connection t 4
    (show 4*(4+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift k5) density5_weighted 72
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    (fun p y hy => (ht p y hy).symm)
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density5_scalarDensity_bound S P
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem density6_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S P.tangent P.connection)
    (hdecomp : KSWEq38Decomposition S P.tangent P.connection)
    (hn : S.quaternionicDimension = 6) (b : Basis ι ℝ E)
    (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S P.tangent P.connection p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    96 * (t ^ 2 / Real.pi) ^ 12 ≤
      scalarDensity P.tangent
        (sourceTopForm S P.tangent P.connection t 5
          (show 4*(5+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift k6) density6_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 6
      (density6Form S P.tangent P.connection t)) 96 (t ^ 2 / Real.pi)
      (fun F hF => by
        simpa only [hn] using
          density6Form_pointwise_bound S P.tangent P.connection
            hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(5+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S P.tangent p y hy).symm.toContinuousLinearMap 6
      (density6Form S P.tangent P.connection t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S P.tangent b 5 hdim
    (density6Form S P.tangent P.connection t) p y hy r).mp he'
  simpa only [sourceTopForm, density6Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

theorem exists_density6_sourceNumber_quarter_bound
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : S.quaternionicDimension = 6) (b : Basis ι ℝ E) :
    ∃ t : ℝ, 0 < t ∧
      96 * integral P.tangent
        (quarterTop P.tangent P.connection 6
          (show 4*6 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)) ≤
      sourcePolynomialNumber S P.tangent P.connection t 5
        (show 4*(5+1) = Module.finrank ℝ E by
          have h := S.real_finrank; omega)
        (DimensionThirteenFourteenDensity.lift k6) := by
  have hn2 : 2 ≤ S.quaternionicDimension := by omega
  let hd := decomposition_of_KSWEq38OnModel S P.tangent heq38
    P.toPositiveScalarTangentGeometry hn2
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter_of_eq38 S P.tangent
    P.toPositiveScalarTangentGeometry hd hn2 P.connected
  refine ⟨t, htpos, ?_⟩
  apply sourcePolynomialNumber_quarter_lower_bound S P.tangent P.connection t 5
    (show 4*(5+1) = Module.finrank ℝ E by
      have h := S.real_finrank; omega)
    (DimensionThirteenFourteenDensity.lift k6) density6_weighted 96
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    (fun p y hy => (ht p y hy).symm)
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  have h := density6_scalarDensity_bound S P
    (formula_of_KSWLemma310OnModel S P.tangent hsp
      P.toPositiveScalarTangentGeometry hn2)
    hd hn b t htpos (fun p y hy => (ht p y hy).symm) x y hy
  simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using h

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerTwoSixQuarterNumbers
