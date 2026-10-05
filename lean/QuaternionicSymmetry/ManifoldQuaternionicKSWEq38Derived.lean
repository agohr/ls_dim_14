import QuaternionicSymmetry.QuaternionicAlgebraicKSWDecomposition
import QuaternionicSymmetry.ManifoldQuaternionicFixedCurvatureAlgebra

/-! KSW's pointwise scalar/Weyl decomposition is proved from the genuine
metric-compatible torsion-free quaternionic tangent connection. The scalar
coefficient is identified by its actual Ricci and scalar contractions. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Derived
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEinstein ManifoldQuaternionicKSWEinsteinAdapted
open ManifoldQuaternionicFixedCurvatureAlgebra
open QuaternionicManifoldFixedNormalizer QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldFixedSolder QuaternionicAlgebraicKSWDecomposition
open QuaternionicKSWModelRicci QuaternionicKSWUpperModel QuaternionicStandardSolderSquare
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem localRicci_of_decomposition (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (lam : ℝ) (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hW : HyperWeylFiber S W)
    (he : ∀ u v, curvatureBilinear S Q D p y hy u v =
      lam • scalarModelR0 S u v + W u v) (v w : E) :
    localRicci Q D p y hy v w =
      (lam * ((Module.finrank ℝ E : ℝ) + 8)) * inner ℝ v w := by
  let g := modelGauge S (Q.reduction.Q (achart E p))
  let b := stdOrthonormalBasis ℝ E
  have hfixed := QuaternionicAlgebraicKSWDecomposition.ricci_of_decomposition S
    (curvatureBilinear S Q D p y hy) W lam hW he (g.symm v) (g.symm w)
  change (∑ a : Fin (Module.finrank ℝ E),
    inner ℝ (fixedCurvature S Q D p y hy (b a) (g.symm v) (g.symm w)) (b a)) =
      (lam * ((Module.finrank ℝ E : ℝ) + 8)) * inner ℝ (g.symm v) (g.symm w) at hfixed
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


theorem scalarRatio_eq_of_decomposition (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (lam : ℝ) (W : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hW : HyperWeylFiber S W)
    (he : ∀ u v, curvatureBilinear S Q D p y hy u v =
      lam • scalarModelR0 S u v + W u v) :
    scalarRatio S Q D p y hy = lam := by
  have hsc : localScalarCurvature Q D p y hy =
      lam * ((Module.finrank ℝ E : ℝ) + 8) * (Module.finrank ℝ E : ℝ) := by
    unfold localScalarCurvature
    simp_rw [localRicci_of_decomposition S Q D p y hy lam W hW he]
    simp
    ring
  rw [scalarRatio, hsc]
  have hd : (Module.finrank ℝ E : ℝ) = 4 * (S.quaternionicDimension : ℝ) :=
    by exact_mod_cast S.real_finrank
  rw [hd]
  have hn : (0 : ℝ) < (S.quaternionicDimension : ℝ) :=
    by
      have hdim : 0 < Module.finrank ℝ E := Module.finrank_pos
      have hn' : 0 < S.quaternionicDimension := by rw [S.real_finrank] at hdim; omega
      exact_mod_cast hn'
  have hn2 : (S.quaternionicDimension : ℝ) + 2 ≠ 0 := by linarith
  field_simp [ne_of_gt hn, hn2]
  <;> ring

theorem decomposition (hn : 2 ≤ S.quaternionicDimension) :
    KSWEq38Decomposition S Q D := by
  intro p y hy
  obtain ⟨lam,W,hW,he⟩ := QuaternionicAlgebraicKSWDecomposition.decomposition S
    (curvatureBilinear S Q D p y hy) hn
    (skew_first S Q D p y hy) (skew_last S Q D p y hy)
    (first_bianchi S Q D p y hy) (symplectic_commutes S Q D p y hy)
  have hlam := scalarRatio_eq_of_decomposition S Q D p y hy lam W hW he
  refine ⟨W,hW,?_⟩
  intro u v
  let e := fixedSolderEquiv S Q p y hy
  have hr := he (e u) (e v)
  rw [curvatureBilinear_apply] at hr
  simp only [fixedCurvature, show fixedSolderEquiv S Q p y hy = e from rfl,
    e.symm_apply_apply] at hr
  rw [← hlam] at hr
  change fixedTangentConjugation S Q p (D.curvature Q p y u v) =
    scalarRatio S Q D p y hy • scalarModelR0 S (e u) (e v) + W (e u) (e v) at hr
  change fixedTangentConjugation S Q p (D.curvature Q p y u v) = _
  rw [hr]
  change scalarRatio S Q D p y hy • scalarModelR0 S (e u) (e v) + W (e u) (e v) =
    -(2 * scalarRatio S Q D p y hy) •
      (sourceRH S Q p y u v + sourceREOperator S (e u) (e v)) + W (e u) (e v)
  have hH : VectorBundleFrameTransitions.QuaternionicFrameReduction.synth S
      (fun t => inner ℝ (VectorBundleFrameTransitions.quaternionicGenerator S t (e u)) (e v)) =
      sourceRH S Q p y u v := rfl
  rw [scalarModelR0, hH, sourceREOperator]
  module

theorem onModel : KSWEq38OnModel (E := E) (M := M) := by
  intro S Q G hn
  exact decomposition S Q G.connection hn

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Derived
