import QuaternionicSymmetry.QuaternionicSevenTenClosedDensityForms
import QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient
import QuaternionicSymmetry.QuaternionicDensityCoefficient
import QuaternionicSymmetry.QuaternionicSourceIntegralBound

/-! The n=7–10 closed source representatives have intrinsic scalar-density
lower bounds relative to the actual quaternionic Riemannian volume form. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenActualDensity
open Module QuaternionicSevenTenClosedDensityForms
open ManifoldEvenClosedEvaluation ManifoldQuaternionicGradeDensityCoefficient
open ManifoldQuaternionicVolumeCoefficient QuaternionicSourceIntegralBound
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicFundamental
open PrintedCertificatesSevenTen LowerCertificateWeights
open scoped Manifold ContDiff
noncomputable section

variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density7_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 7) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    128 * (t ^ 2 / Real.pi) ^ 14 ≤
      scalarDensity Q
        (sourceTopForm S Q D t 6
          (show 4*(6+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift rhs7) rhs7_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 7
      (density7Form S Q D t)) 128 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density7Form_pointwise_bound S Q D hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(6+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 7
      (density7Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 6 hdim
    (density7Form S Q D t) p y hy r).mp he'
  simpa only [sourceTopForm, density7Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm


omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density8_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 8) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    160 * (t ^ 2 / Real.pi) ^ 16 ≤
      scalarDensity Q
        (sourceTopForm S Q D t 7
          (show 4*(7+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift rhs8) rhs8_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 8
      (density8Form S Q D t)) 160 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density8Form_pointwise_bound S Q D hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(7+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 8
      (density8Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 7 hdim
    (density8Form S Q D t) p y hy r).mp he'
  simpa only [sourceTopForm, density8Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density9_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 9) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    200 * (t ^ 2 / Real.pi) ^ 18 ≤
      scalarDensity Q
        (sourceTopForm S Q D t 8
          (show 4*(8+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift rhs9) rhs9_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 9
      (density9Form S Q D t)) 200 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density9Form_pointwise_bound S Q D hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(8+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 9
      (density9Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 8 hdim
    (density9Form S Q D t) p y hy r).mp he'
  simpa only [sourceTopForm, density9Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem density10_scalarDensity_bound
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 10) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    240 * (t ^ 2 / Real.pi) ^ 20 ≤
      scalarDensity Q
        (sourceTopForm S Q D t 9
          (show 4*(9+1) = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (DimensionThirteenFourteenDensity.lift rhs10) rhs10_weighted).val
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue p y (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 10
      (density10Form S Q D t)) 240 (t ^ 2 / Real.pi) (fun F hF => by
        simpa only [hn] using
          density10Form_pointwise_bound S Q D hsp hdecomp hn b t htpos ht p y hy F hF)
  have hdim : 4*(9+1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 10
      (density10Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 9 hdim
    (density10Form S Q D t) p y hy r).mp he'
  simpa only [sourceTopForm, density10Form, hn, Nat.reduceMul] using hr.trans_eq hd.symm

end
end QuaternionicSymmetry.QuaternionicSevenTenActualDensity
