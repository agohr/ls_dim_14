import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionConstruction

/-! The constructed orthonormal immersion frames are parallel for the
projected connection, by the quaternionic second fundamental form argument. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConstructedTotalGeodesy
open ManifoldQuaternionicInducedConnectionConstruction
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicCoordinateConnection ManifoldQuaternionicImmersionCharts
open ManifoldQuaternionicInducedTotalGeodesy QuaternionicProjectedSecondFundamental
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

include hι

theorem normalPart_zero (p : N) (y u v : F)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    normalPart (ambientForm L p) (L.embedding p) y u v = 0 := by
  let f := localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)
  let A := LocalSolderPullback.solder (solder P.tangent (L.ambientPoint p)) f
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy
  have hf := (localBaseMap_contDiffAt ι hι p (L.ambientPoint p) y ⟨hy,L.target p y hy⟩).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have ht := (solder_contDiffAt P.tangent (L.ambientPoint p) (f y) hfy).differentiableAt (by simp)
  have hb := ((L.smooth_embedding p).contDiffAt hn).differentiableAt (by simp)
  have hA : A =ᶠ[𝓝 y] fun z => (L.embedding p z).comp (solder Q p z) :=
    Filter.Eventually.mono hn (fun z hz => (L.solder_eq p z hz).symm)
  apply normalPart_zero_of_symmetric (Q.reduction.Q (achart F p))
    (P.tangent.reduction.Q (achart E (L.ambientPoint p)))
    (ambientForm L p) (L.embedding p) y (solderEquiv Q p y hy) hb
    (L.inner_embedding p y hy)
    (Filter.Eventually.mono hn (fun z hz => L.intertwines_I p z hz))
    (Filter.Eventually.mono hn (fun z hz => L.intertwines_J p z hz))
  · intro a t
    exact P.connection.quaternionic (L.ambientPoint p) _ _ t hfy
  · intro a b
    exact normalPart_symmetric (ambientForm L p) (L.embedding p)
      (solder Q p) A y hb ((solder_contDiffAt Q p y hy).differentiableAt (by simp))
      (L.inner_embedding p y hy) hA
      (LocalSolderPullback.torsion (solder P.tangent (L.ambientPoint p)) f y
        (P.connection.form (L.ambientPoint p) (f y)) ht hf
        (fun a b => P.connection.torsion (L.ambientPoint p) (f y) a b hfy)) a b

theorem parallel_embedding (p : N) (y u v : F)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    fderiv ℝ (L.embedding p) y u v =
      L.embedding p y (form L p y u v) - ambientForm L p y u (L.embedding p y v) := by
  have h := normalPart_zero L hι p y u v hy
  unfold normalPart at h
  change _ + _ - L.embedding p y (form L p y u v) = 0 at h
  linear_combination (norm := module) h

end
end QuaternionicSymmetry.ManifoldQuaternionicConstructedTotalGeodesy
