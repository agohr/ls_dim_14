import QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance

/-! Orthogonality of the genuine manifold derivative in adapted metric frames. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryAdaptedOrthogonal

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- In adapted orthonormal frames at a point and its image, a genuine
quaternionic isometry has an orthogonal derivative matrix. -/
theorem localAdaptedDerivative_center_inner
    (f : QuaternionicIsometries Q) (p : M) (u v : E) :
    inner ℝ (localAdaptedDerivative Q f p p u)
        (localAdaptedDerivative Q f p p v) = inner ℝ u v := by
  let i := achart E p
  let j := achart E (f • p)
  let U := Q.frames.fromFrame i p u
  let V := Q.frames.fromFrame i p v
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p
  have hj := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • p)
  have h := f.2.1 p U V
  rw [Q.tangentMetricForm_apply, Q.tangentMetricForm_apply] at h
  change inner ℝ
      (Q.frames.toFrame j (f • p)
        (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f p U))
      (Q.frames.toFrame j (f • p)
        (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f p V)) =
      inner ℝ (Q.frames.toFrame i p U)
        (Q.frames.toFrame i p V) at h
  rw [Q.frames.to_from i p hi, Q.frames.to_from i p hi] at h
  simpa only [U, V, localAdaptedDerivative_center_apply] using h

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Fixed-chart adapted derivatives differ from the point-centered adapted
derivative by the two actual orthogonal frame-transition matrices. -/
theorem localAdaptedDerivative_fixed_center
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source) :
    localAdaptedDerivative Q f p x =
      (Q.frames.coordChange (achart E (f • x)) (achart E (f • p)) (f • x)).comp
        ((localAdaptedDerivative Q f x x).comp
          (Q.frames.coordChange (achart E p) (achart E x) x)) := by
  let i := achart E p
  let k := achart E x
  let l := achart E (f • x)
  let j := achart E (f • p)
  let Cik := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k x
  let Clj := (tangentBundleCore 𝓘(ℝ,E) M).coordChange l j (f • x)
  let Ti := Q.frames.toFrame i x
  let Tk := Q.frames.toFrame k x
  let Fl := Q.frames.fromFrame l (f • x)
  let Fj := Q.frames.fromFrame j (f • x)
  have hi : x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet i := hx
  have hk := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hl := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • x)
  have hj : f • x ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet j := hy
  rw [localAdaptedDerivative_eq_on_overlap Q f p x hx hy]
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [localAdaptedDerivative_center_apply Q f x]
  change Q.frames.toFrame j (f • x)
      (Clj ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x)
        (Cik (Q.frames.fromFrame i x v)))) =
    Q.frames.coordChange l j (f • x)
      (Q.frames.toFrame l (f • x)
        (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f x
          (Q.frames.fromFrame k x
            (Q.frames.coordChange i k x v))))
  rw [Q.frames.coordChange_apply, Q.frames.from_to l (f • x) hl]
  have hsrc : Q.frames.fromFrame k x (Q.frames.coordChange i k x v) =
      Cik (Q.frames.fromFrame i x v) := by
    rw [Q.frames.coordChange_apply]
    rw [Q.frames.from_to k x hk]
  rw [hsrc]
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The fixed-chart matrix remains orthogonal at every point in the source
and target chart overlap. This is the metric identity needed to pull back
the Levi-Civita connection form. -/
theorem localAdaptedDerivative_inner_on_overlap
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (u v : E) :
    inner ℝ (localAdaptedDerivative Q f p x u)
      (localAdaptedDerivative Q f p x v) = inner ℝ u v := by
  let i := achart E p
  let k := achart E x
  let l := achart E (f • x)
  let j := achart E (f • p)
  have hi : x ∈ Q.frames.adaptedCore.baseSet i := hx
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hl : f • x ∈ Q.frames.adaptedCore.baseSet l :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • x)
  have hj : f • x ∈ Q.frames.adaptedCore.baseSet j := hy
  rw [localAdaptedDerivative_fixed_center Q f p x hx hy]
  change inner ℝ
      (Q.frames.coordChange l j (f • x)
        (localAdaptedDerivative Q f x x (Q.frames.coordChange i k x u)))
      (Q.frames.coordChange l j (f • x)
        (localAdaptedDerivative Q f x x (Q.frames.coordChange i k x v))) = _
  rw [Q.transition_inner l j (f • x) hl hj,
    localAdaptedDerivative_center_inner Q f x,
    Q.transition_inner i k x hi hk]

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryAdaptedOrthogonal
