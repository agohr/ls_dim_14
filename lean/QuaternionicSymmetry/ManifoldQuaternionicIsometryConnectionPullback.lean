import QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields

/-! The actual connection form pulled back by a smooth metric-quaternionic
isometry, in adapted frames and fixed source/target manifold charts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionPullback

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicIsometryAdaptedOrthogonal
open ManifoldQuaternionicIsometryChartFields
open QuaternionicSymmetry.LocalConnectionCoordinatePullback
open QuaternionicSymmetry.LocalConnectionGauge
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Forward adapted-frame matrix as a function of source chart coordinates. -/
def forwardFrameField (f : QuaternionicIsometries Q) (p : M) :
    E → (E →L[ℝ] E) :=
  fun y => localAdaptedDerivative Q f p ((extChartAt 𝓘(ℝ,E) p).symm y)

/-- Reverse adapted-frame matrix as a function of source chart coordinates. -/
def reverseFrameField (f : QuaternionicIsometries Q) (p : M) :
    E → (E →L[ℝ] E) :=
  fun y => localAdaptedInverseDerivative Q f p ((extChartAt 𝓘(ℝ,E) p).symm y)

/-- Genuine coordinate-and-frame pullback of the actual Levi-Civita form.
The equality with the source form is to follow from metricity and torsion,
not from the definition. -/
def pulledConnectionForm (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) : ConnectionForm (E := E) :=
  LocalConnectionGauge.transform
    (LocalConnectionCoordinatePullback.pullback
      (D.form (f • p)) (localIsometryChartMap Q f p))
    (forwardFrameField Q f p) (reverseFrameField Q f p)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Explicit local transformation rule for the pulled-back connection;
all factors are actual geometric derivatives or adapted frame maps. -/
theorem pulledConnectionForm_apply (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (y u v : E) :
    pulledConnectionForm Q D f p y u v =
      reverseFrameField Q f p y
        (D.form (f • p) (localIsometryChartMap Q f p y)
          (fderiv ℝ (localIsometryChartMap Q f p) y u)
            (forwardFrameField Q f p y v) +
          fderiv ℝ (forwardFrameField Q f p) y u v) := by
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The elementary metric calculation for a connection transformed by
an orthogonal frame field and its derivative. -/
private theorem transformed_metric_of_orthogonal
    (A B : E →L[ℝ] E)
    (C : E →L[ℝ] (E →L[ℝ] E))
    (dA : E →L[ℝ] (E →L[ℝ] E))
    (hAB : ∀ z, A (B z) = z)
    (horth : ∀ v w, inner ℝ (A v) (A w) = inner ℝ v w)
    (hC : ∀ u v w,
      inner ℝ (C u v) w + inner ℝ v (C u w) = 0)
    (hdA : ∀ u v w,
      inner ℝ (dA u v) (A w) + inner ℝ (A v) (dA u w) = 0)
    (u v w : E) :
    inner ℝ (B (C u (A v) + dA u v)) w +
      inner ℝ v (B (C u (A w) + dA u w)) = 0 := by
  have hBleft (z t : E) : inner ℝ (B z) t = inner ℝ z (A t) := by
    rw [← horth (B z) t, hAB]
  have hBright (t z : E) : inner ℝ t (B z) = inner ℝ (A t) z := by
    rw [← horth t (B z), hAB]
  rw [hBleft, hBright, inner_add_left, inner_add_right]
  have h₁ := hC u (A v) (A w)
  have h₂ := hdA u v w
  linear_combination h₁ + h₂

/-- The genuine isometry pullback is metric at the center of every source
chart. No connection-invariance premise is used. -/
theorem pulledConnectionForm_metric_center
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (p : M) (u v w : E) :
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    inner ℝ ((pulledConnectionForm Q D f p y₀ u) v) w +
      inner ℝ v ((pulledConnectionForm Q D f p y₀ u) w) = 0 := by
  dsimp only
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let F := localIsometryChartMap Q f p
  let A := forwardFrameField Q f p y₀
  let B := reverseFrameField Q f p y₀
  let C : E →L[ℝ] (E →L[ℝ] E) :=
    (D.form (f • p) (F y₀)).comp (fderiv ℝ F y₀)
  let dA := fderiv ℝ (forwardFrameField Q f p) y₀
  have hsrc : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hF : F y₀ = extChartAt 𝓘(ℝ,E) (f • p) (f • p) := by
    simp only [F, localIsometryChartMap, hsrc]
  have hmem : F y₀ ∈ (extChartAt 𝓘(ℝ,E) (f • p)).target := by
    rw [hF]
    exact (extChartAt 𝓘(ℝ,E) (f • p)).map_source (by simp)
  have hAB (z : E) : A (B z) = z := by
    simpa only [A, B, forwardFrameField, reverseFrameField, hsrc] using
      localAdaptedDerivative_inverse_center Q f p z
  have horth (a b : E) : inner ℝ (A a) (A b) = inner ℝ a b := by
    simpa only [A, forwardFrameField, hsrc] using
      localAdaptedDerivative_center_inner Q f p a b
  have hC (a b c : E) :
      inner ℝ (C a b) c + inner ℝ b (C a c) = 0 := by
    exact D.metric (f • p) (F y₀) (fderiv ℝ F y₀ a) b c hmem
  have hdA (a b c : E) :
      inner ℝ (dA a b) (A c) + inner ℝ (A b) (dA a c) = 0 := by
    simpa only [dA, A, forwardFrameField] using
      localAdaptedDerivative_coordinate_skew_center Q f p a b c
  have h := transformed_metric_of_orthogonal A B C dA hAB horth hC hdA u v w
  simpa only [pulledConnectionForm_apply, C, A, B, dA,
    ContinuousLinearMap.comp_apply] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryConnectionPullback
