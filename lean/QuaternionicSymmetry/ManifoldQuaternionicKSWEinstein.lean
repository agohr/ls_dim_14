import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
import QuaternionicSymmetry.QuaternionicKSWModelRicci

/-! The pointwise Einstein equation from the registered KSW Eq. (3.8).
The scalar-model Ricci trace is proved directly from the four real wedges;
the source Weyl term is trace-free by its Sym⁴ representation property. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWEinstein
open ManifoldQuaternionicConnection
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open QuaternionicKSWModelRicci
open QuaternionicKSWUpperModel
open QuaternionicManifoldFixedSolder
open QuaternionicManifoldProjectiveStandardConnection
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def fixedCurvature (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (u v : E) : E →L[ℝ] E :=
  fixedTangentConjugation S Q p
    (D.curvature Q p y
      ((fixedSolderEquiv S Q p y hy).symm u)
      ((fixedSolderEquiv S Q p y hy).symm v))

theorem fixedCurvature_eq_scalarModel_add_hyper
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
      HyperWeylFiber S W ∧
      ∀ u v : E,
        fixedCurvature S Q D p y hy u v =
          scalarRatio S Q D p y hy • scalarModelR0 S u v + W u v := by
  obtain ⟨W, hW, hR⟩ := hdecomp p y hy
  refine ⟨W, hW, ?_⟩
  intro u v
  let e := fixedSolderEquiv S Q p y hy
  have h := hR (e.symm u) (e.symm v)
  rw [← fixedSolderEquiv_apply S Q p y hy,
    ← fixedSolderEquiv_apply S Q p y hy,
    e.apply_symm_apply, e.apply_symm_apply] at h
  have hcoeff : kahlerCoefficients S Q p y (e.symm u) (e.symm v) =
      (fun t => inner ℝ (VectorBundleFrameTransitions.quaternionicGenerator S t u) v) := by
    ext t
    change inner ℝ (VectorBundleFrameTransitions.quaternionicGenerator S t
      (e (e.symm u))) (e (e.symm v)) = _
    rw [e.apply_symm_apply, e.apply_symm_apply]
  simp only [sourceRH] at h
  rw [hcoeff] at h
  change fixedCurvature S Q D p y hy u v = _ at h
  change fixedCurvature S Q D p y hy u v = _
  simp only [sourceREOperator] at h
  rw [h]
  simp only [scalarModelR0]
  module

/-- The source decomposition implies the pointwise Einstein equation in
fixed orthonormal quaternionic coordinates. Its coefficient is
`κ/(4n)`, written without division as
`(dim_ℝ E + 8) * κ/(16n(n+2))`. -/
theorem fixedCurvature_ricci_einstein
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (fixedCurvature S Q D p y hy
        (stdOrthonormalBasis ℝ E a) v w)
        (stdOrthonormalBasis ℝ E a)) =
      (scalarRatio S Q D p y hy *
        ((Module.finrank ℝ E : ℝ) + 8)) * inner ℝ v w := by
  obtain ⟨W, hW, hR⟩ :=
    fixedCurvature_eq_scalarModel_add_hyper S Q D hdecomp p y hy
  have hWricci := hW.2.2.2.2.2
  simp_rw [hR]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, real_inner_smul_left, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [scalarModelR0_ricci S, hWricci v w]
  ring

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWEinstein
