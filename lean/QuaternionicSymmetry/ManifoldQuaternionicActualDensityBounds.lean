import QuaternionicSymmetry.QuaternionicClosedDensityCoefficients
import QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient

/-! The printed closed density estimates in actual intrinsic tangent volume coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualDensityBounds
open Module ManifoldDeRhamWedge QuaternionicClosedDensityForms QuaternionicClosedDensityCoefficients
open ManifoldEvenClosedEvaluation ManifoldQuaternionicGradeDensityCoefficient
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicVolumeCoefficient
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem density11_scalarDensity_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 11) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    288 * (t ^ 2 / Real.pi) ^ 22 ≤
      scalarDensity Q
        (castForm
          (show 4 * 10 + 3 + 1 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (density11Form S Q D t).val.val)
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := density11_coefficient S Q D hsource hsp hdecomp hn b t htpos ht p y hy
  have hdim : 4 * (10 + 1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 11
      (density11Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 10 hdim
    (density11Form S Q D t) p y hy r).mp he'
  simpa only using hr.trans_eq hd.symm

theorem density12_scalarDensity_bound
    (hsource : OrbitalInterleavedBridge.LiteralInterleavedFormula)
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (hn : S.quaternionicDimension = 12) (b : Basis ι ℝ E) (t : ℝ) (htpos : 0 < t)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    336 * (t ^ 2 / Real.pi) ^ 24 ≤
      scalarDensity Q
        (castForm
          (show 4 * 11 + 3 + 1 = Module.finrank ℝ E by
            have h := S.real_finrank; omega)
          (density12Form S Q D t).val.val)
        ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  obtain ⟨r, hr, he⟩ := density12_coefficient S Q D hsource hsp hdecomp hn b t htpos ht p y hy
  have hdim : 4 * (11 + 1) = Module.finrank ℝ E := by
    have h := S.real_finrank
    omega
  have he' : (gradeValue p y
      (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap 12
      (density12Form S Q D t)).val =
      r • (QuaternionicFundamental.form S b).val ^ S.quaternionicDimension := by
    simpa only [hn] using congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b 11 hdim
    (density12Form S Q D t) p y hy r).mp he'
  simpa only using hr.trans_eq hd.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicActualDensityBounds
