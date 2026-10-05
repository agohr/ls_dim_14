import QuaternionicSymmetry.ManifoldQuaternionicKSWEinstein
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature

/-! Transport the fixed-model Einstein equation to the actual adapted
orthonormal tangent coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWEinsteinAdapted
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEinstein
open QuaternionicManifoldFixedNormalizer
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

omit [Nontrivial E] in
theorem fixedSolderEquiv_symm_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u : E) :
    (fixedSolderEquiv S Q p y hy).symm u =
      (solderEquiv Q p y hy).symm
        (modelGauge S (Q.reduction.Q (achart E p)) u) := by
  rfl

omit [Nontrivial E] in
theorem fixedTangentConjugation_apply (p : M) (A : E →L[ℝ] E) (w : E) :
    fixedTangentConjugation S Q p A w =
      (modelGauge S (Q.reduction.Q (achart E p))).symm
        (A (modelGauge S (Q.reduction.Q (achart E p)) w)) := by
  rfl

omit [Nontrivial E] in
theorem fixedCurvature_apply_adapted (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w : E) :
    fixedCurvature S Q D p y hy u v w =
      (modelGauge S (Q.reduction.Q (achart E p))).symm
        (adaptedCurvature Q D p y hy
          (modelGauge S (Q.reduction.Q (achart E p)) u)
          (modelGauge S (Q.reduction.Q (achart E p)) v)
          (modelGauge S (Q.reduction.Q (achart E p)) w)) := by
  simp only [fixedCurvature, fixedTangentConjugation_apply,
    fixedSolderEquiv_symm_apply, adaptedCurvature]

/-- The pointwise Einstein equation in the actual adapted tangent frame. -/
theorem localRicci_einstein
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    localRicci Q D p y hy v w =
      (scalarRatio S Q D p y hy *
        ((Module.finrank ℝ E : ℝ) + 8)) * inner ℝ v w := by
  let g := modelGauge S (Q.reduction.Q (achart E p))
  let b := stdOrthonormalBasis ℝ E
  have hfixed := fixedCurvature_ricci_einstein S Q D hdecomp p y hy
    (g.symm v) (g.symm w)
  have hframe : localRicci Q D p y hy v w =
      ∑ a : Fin (Module.finrank ℝ E),
        inner ℝ (adaptedCurvature Q D p y hy
          (g (b a)) v w) (g (b a)) := by
    rw [localRicci_eq_trace Q D p y hy v w, ricciTrace,
      LinearMap.trace_eq_sum_inner _ (b.map g)]
    apply Finset.sum_congr rfl
    intro a _
    simp only [ricciEndomorphism, OrthonormalBasis.map_apply]
    exact real_inner_comm _ _
  rw [hframe]
  have hsum : (∑ a : Fin (Module.finrank ℝ E),
      inner ℝ (adaptedCurvature Q D p y hy
        (g (b a)) v w) (g (b a))) =
      ∑ a : Fin (Module.finrank ℝ E),
        inner ℝ (fixedCurvature S Q D p y hy
          (b a) (g.symm v) (g.symm w)) (b a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [fixedCurvature_apply_adapted]
    have hi := g.symm.inner_map_map
      (adaptedCurvature Q D p y hy
        (g (b a)) v w) (g (b a))
    change inner ℝ (adaptedCurvature Q D p y hy (g (b a)) v w)
      (g (b a)) = inner ℝ (g.symm
      (adaptedCurvature Q D p y hy (g (b a))
        (g (g.symm v)) (g (g.symm w)))) (b a)
    rw [g.apply_symm_apply, g.apply_symm_apply]
    simpa only [g.symm_apply_apply] using hi.symm
  rw [hsum, hfixed]
  simp [g]

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWEinsteinAdapted
