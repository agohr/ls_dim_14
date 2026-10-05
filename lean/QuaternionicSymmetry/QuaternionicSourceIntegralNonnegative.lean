import QuaternionicSymmetry.QuaternionicSourceIntegralBound
import QuaternionicSymmetry.QuaternionicDensityCoefficient
import QuaternionicSymmetry.ManifoldQuaternionicGradeDensityCoefficient

/-! Transfer a genuine quaternionic pointwise cone sign to the canonical
integral of an actual closed characteristic representative. -/
namespace QuaternionicSymmetry.QuaternionicSourceIntegralNonnegative
open Module QuaternionicSourceIntegralBound QuaternionicClosedSourceNumbers
open QuaternionicClosedSourceGenerators ManifoldClosedPolynomialRepresentative
open ManifoldEvenClosedEvaluation ManifoldQuaternionicGradeDensityCoefficient
open ManifoldQuaternionicKSWEq38Input QuaternionicTracePositivity
open ManifoldQuaternionicVolumeCoefficient
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem sourcePolynomialNumber_nonnegative
    (b : Basis ι ℝ E) (t : ℝ) (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P (k+1))
    (hpointwise : ∀ (p : M) (y : E)
      (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
      (F : CE E →ₗ[ℝ] ℝ),
      0 ≤ F (embed (V := E) (QuaternionicFundamental.topForm S b)) →
      0 ≤ F (embed (V := E) (gradeValue p y
        (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap (k+1)
        (closedRepresentative (generators S Q D t) P hP)))) :
    0 ≤ sourcePolynomialNumber S Q D t k hdim P := by
  have hb := sourcePolynomialNumber_lower_bound S Q D t k hdim P hP 0
  simp only [zero_mul] at hb
  apply hb
  intro x
  let y := extChartAt 𝓘(ℝ,E) x x
  have hy : y ∈ (extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (by simp)
  obtain ⟨r, hr, he⟩ := QuaternionicDensityCoefficient.exists_coefficient_ge S b
    (gradeValue x y (fixedSolderEquiv S Q x y hy).symm.toContinuousLinearMap (k+1)
      (closedRepresentative (generators S Q D t) P hP)) 0 1
    (fun F hF => by simpa only [zero_mul] using hpointwise x y hy F hF)
  have he' := congrArg Subtype.val he
  have hd := (gradeValue_density_coefficient_iff S Q b k hdim
    (closedRepresentative (generators S Q D t) P hP) x y hy r).mp he'
  simp only [zero_mul] at hr
  simpa only [sourceTopForm, y,
    (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using hr.trans_eq hd.symm

end
end QuaternionicSymmetry.QuaternionicSourceIntegralNonnegative
