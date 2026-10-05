import QuaternionicSymmetry.QuaternionicManifoldWeylTraceForms
import QuaternionicSymmetry.QuaternionicWeylRankReduction

/-! Actual standard source trace forms have rank-n Weyl representatives. -/
namespace QuaternionicSymmetry.QuaternionicManifoldWeylRankTraceForms
open Module ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicManifoldWeylTraceForms QuaternionicWeylMatrixCoefficients
open QuaternionicCorrectedSourceTraceForms ExteriorContinuousPairing
open LocalChernWeilTracePowers ManifoldDifferentialForms
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem closedSourceTrace_eq_rank_weyl
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      ∀ (j : ℕ) (_hj : 0 < j) (v : Fin (powerDegree (2 * j - 1)) → E),
        inChartModel p (closedSourceEvenTrace S Q D t j).val.val y
          (fun i => (fixedSolderEquiv S Q p y hy).symm (v i)) =
        toContinuous (powerDegree (2 * j - 1))
          (tangentTraceRepresentative S W (HyperWeylFiber.mem_skewCentralizer S hW) b j) v := by
  obtain ⟨W, hW, htrace⟩ := closedSourceTrace_eq_weyl S Q D hsp hdecomp b t p y hy ht
  refine ⟨W, hW, ?_⟩
  intro j hj v
  rw [htrace j hj v, QuaternionicWeylRankReduction.traceRepresentative_eq S W _ b j hj]

end
end QuaternionicSymmetry.QuaternionicManifoldWeylRankTraceForms
