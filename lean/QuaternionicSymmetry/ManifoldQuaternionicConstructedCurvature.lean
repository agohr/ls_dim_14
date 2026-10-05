import QuaternionicSymmetry.ManifoldQuaternionicConstructedTotalGeodesy
import QuaternionicSymmetry.LocalConnectionMapPullback

/-! The genuine curvature of the constructed connection is the restriction
of the ambient curvature through the isometric immersion frames. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConstructedCurvature
open ManifoldQuaternionicInducedConnectionConstruction ManifoldQuaternionicConstructedTotalGeodesy
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicImmersionCharts ManifoldQuaternionicInducedTotalGeodesy
open ManifoldPositiveQuaternionicKahlerGeometry Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)}
  {Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,F)) (M := N) (n := ∞)} {ι : N → M}
  (L : LocalFrames P Q ι) (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)

theorem curvature_embedding (p : N) (y u v w : F)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    P.connection.curvature P.tangent (L.ambientPoint p)
      (localBaseMap ι p (L.ambientPoint p) y)
      (fderiv ℝ (localBaseMap ι p (L.ambientPoint p)) y u)
      (fderiv ℝ (localBaseMap ι p (L.ambientPoint p)) y v) (L.embedding p y w) =
    L.embedding p y ((connection L hι).curvature Q p y u v w) := by
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have hΓ := ((P.connection.smooth_form (L.ambientPoint p)).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) (L.ambientPoint p)).mem_nhds hfy)).differentiableAt (by simp)
  have hf := (localBaseMap_contDiffAt ι hι p (L.ambientPoint p) y ⟨hy,L.target p y hy⟩).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
  have h := LocalConnectionImmersionCurvature.curvature_intertwines (L.embedding p)
    (ambientForm L p) (form L p) y
    (((L.smooth_embedding p).contDiffAt hn).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast))
    (((ambientForm_smooth L hι p).contDiffAt hn).differentiableAt (by simp))
    (((form_smooth L hι p).contDiffAt hn).differentiableAt (by simp))
    (Filter.Eventually.mono hn (fun z hz a b => parallel_embedding L hι p z a b hz)) u v w
  change LocalConnection.curvature
    (LocalConnectionMapPullback.pullback (P.connection.form (L.ambientPoint p))
      (localBaseMap ι p (L.ambientPoint p))) y u v _ = _ at h
  rw [LocalConnectionMapPullback.curvature_pullback _ _ y hΓ hf] at h
  exact h

theorem adaptedCurvature_embedding (p : N) (y u v w : F)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    let f := localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)
    let hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
    adaptedCurvature P.tangent P.connection (L.ambientPoint p) (f y) hfy
      (L.embedding p y u) (L.embedding p y v) (L.embedding p y w) =
    L.embedding p y (adaptedCurvature Q (connection L hι) p y hy u v w) := by
  dsimp only
  let f := localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have hs (a : F) : (solderEquiv P.tangent (L.ambientPoint p) (f y) hfy).symm
      (L.embedding p y a) = fderiv ℝ f y ((solderEquiv Q p y hy).symm a) := by
    apply (solderEquiv P.tangent (L.ambientPoint p) (f y) hfy).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have he := congrArg (fun A : F →L[ℝ] E => A ((solderEquiv Q p y hy).symm a)) (L.solder_eq p y hy)
    simpa only [ContinuousLinearMap.comp_apply,
      show solder Q p y ((solderEquiv Q p y hy).symm a) = a from
        (solderEquiv Q p y hy).apply_symm_apply a] using he
  unfold adaptedCurvature
  rw [hs,hs]
  exact curvature_embedding L hι p y _ _ w hy

end
end QuaternionicSymmetry.ManifoldQuaternionicConstructedCurvature
