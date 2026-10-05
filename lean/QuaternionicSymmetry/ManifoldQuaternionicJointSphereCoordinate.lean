import QuaternionicSymmetry.ManifoldQuaternionicJointMovingAdaptedDerivative
import QuaternionicSymmetry.ManifoldQuaternionicLocalCoefficientComparison
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalAction

/-! Comparison of the jointly continuous two-chart derivative rotation with
the actual quaternionic-isometry action in sphere coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicJointSphereCoordinate

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicJointMovingAdaptedDerivative
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalCoefficientComparison
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicTwistorLocalAction
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldQuaternionicTwistorIsometryAction
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem movingAdaptedDerivative_center
    (f : QuaternionicIsometries Q) (x : M) :
    movingAdaptedDerivative Q f x (f,x) = localAdaptedDerivative Q f x x := by
  apply ContinuousLinearMap.ext
  intro v
  change Q.frames.toFrame (achart E (f • x)) (f • x)
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E (f • x)) (achart E (f • x)) (f • x)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x
          ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
            (achart E x) (achart E x) x
            (Q.frames.fromFrame (achart E x) x v)))) = _
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
    (achart E x) x (mem_chart_source E x),
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E (f • x)) (f • x) (mem_chart_source E (f • x))]
  simp only [localAdaptedDerivative, inTangentCoordinates_isometry_center,
    ContinuousLinearMap.comp_apply]
  rfl

theorem movingAdaptedInverseDerivative_center
    (f : QuaternionicIsometries Q) (x : M) :
    movingAdaptedInverseDerivative Q f x (f,x) =
      localAdaptedInverseDerivative Q f x x := by
  change movingAdaptedDerivative Q f⁻¹ (f • x) (f⁻¹, f • x) =
    localAdaptedDerivative Q f⁻¹ (f • x) (f • x)
  exact movingAdaptedDerivative_center Q f⁻¹ (f • x)

theorem movingCoefficientRotation_center
    (f : QuaternionicIsometries Q) (x : M) (a : Fin 3 → ℝ) :
    movingCoefficientRotation Q f x a (f,x) = coefficientAction Q f x a := by
  change coeff (Q.reduction.Q (achart E (f • x)))
    ((movingAdaptedDerivative Q f x (f,x)).comp
      ((synth (Q.reduction.Q (achart E x)) a).comp
        (movingAdaptedInverseDerivative Q f x (f,x)))) = _
  rw [movingAdaptedDerivative_center Q f x,
    movingAdaptedInverseDerivative_center Q f x]
  exact localCoefficientRotation_center Q f x a

/-- The actual derivative rotation written in the two fixed sphere charts
centered at `(x₀, f₀ x₀)`. -/
def movingTrueCoefficientAction (f₀ : QuaternionicIsometries Q) (x₀ : M)
    (a : Fin 3 → ℝ) (p : QuaternionicIsometries Q × M) : Fin 3 → ℝ :=
  Q.reduction.rankThreeCoordChange (achart E (p.1 • p.2))
    (achart E (f₀ • x₀)) (p.1 • p.2)
      (coefficientAction Q p.1 p.2
        (Q.reduction.rankThreeCoordChange (achart E x₀)
          (achart E p.2) p.2 a))

/-- On a two-fixed-chart overlap, the moving adapted derivative intertwines
the quaternionic generators with the actual derivative-induced coefficient
rotation. This does not assume any point is fixed by the isometry. -/
theorem movingAdaptedDerivative_intertwines_synth
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source)
    (a : Fin 3 → ℝ) (w : E) :
    movingAdaptedDerivative Q f₀ x₀ (f,x)
      ((synth (Q.reduction.Q (achart E x₀)) a) w) =
    (synth (Q.reduction.Q (achart E (f₀ • x₀)))
      (movingTrueCoefficientAction Q f₀ x₀ a (f,x)))
        (movingAdaptedDerivative Q f₀ x₀ (f,x) w) := by
  let i := achart E x₀
  let j := achart E (f₀ • x₀)
  let k := achart E x
  let l := achart E (f • x)
  let C := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k x
  let D := (tangentBundleCore 𝓘(ℝ,E) M).coordChange l j (f • x)
  let T := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x
  let R := D.comp (T.comp C)
  let Fi := Q.frames.fromFrame i x
  let Ti := Q.frames.toFrame i x
  let Fj := Q.frames.fromFrame j (f • x)
  let Tj := Q.frames.toFrame j (f • x)
  let b := Q.reduction.rankThreeCoordChange i k x a
  let c := coefficientAction Q f x b
  let d := Q.reduction.rankThreeCoordChange l j (f • x) c
  have hk := Q.frames.adaptedCore.mem_baseSet_at x
  have hl := Q.frames.adaptedCore.mem_baseSet_at (f • x)
  have hsrc := localTangentSynth_coordChange Q i k x hx hk a
  have htgt := localTangentSynth_coordChange Q l j (f • x) hl hy c
  have hdf (v : E) : T (localTangentSynth Q k x b v) =
      localTangentSynth Q l (f • x) c (T v) := by
    have h := congrArg
      (fun A : TangentSpace 𝓘(ℝ,E) (f • x) →L[ℝ]
        TangentSpace 𝓘(ℝ,E) (f • x) => A (tangentEquiv Q f x v))
      (tangentSynth_coefficientAction Q f x b)
    change tangentSynth Q (f • x) c (tangentEquiv Q f x v) =
      tangentConjugation Q f x (tangentSynth Q x b)
        (tangentEquiv Q f x v) at h
    rw [tangentConjugation_apply_tangentEquiv] at h
    exact h.symm
  have hraw (v : E) : R (localTangentSynth Q i x a v) =
      localTangentSynth Q j (f • x) d (R v) := by
    change D (T (C (localTangentSynth Q i x a v))) =
      localTangentSynth Q j (f • x) d (D (T (C v)))
    rw [← hsrc, hdf, htgt]
  have hU (v : E) : movingAdaptedDerivative Q f₀ x₀ (f,x) v =
      Tj (R (Fi v)) := rfl
  have hFi : Fi ((synth (Q.reduction.Q i) a) w) =
      localTangentSynth Q i x a (Fi w) := by
    change Fi ((synth (Q.reduction.Q i) a) w) =
      Fi ((synth (Q.reduction.Q i) a) (Ti (Fi w)))
    rw [Q.frames.to_from i x hx]
  have hTj (v : E) : Tj (localTangentSynth Q j (f • x) d v) =
      (synth (Q.reduction.Q j) d) (Tj v) := by
    change Tj (Fj ((synth (Q.reduction.Q j) d) (Tj v))) = _
    rw [Q.frames.to_from j (f • x) hy]
  change movingAdaptedDerivative Q f₀ x₀ (f,x)
      ((synth (Q.reduction.Q i) a) w) =
    (synth (Q.reduction.Q j) d)
      (movingAdaptedDerivative Q f₀ x₀ (f,x) w)
  calc
    _ = Tj (R (Fi ((synth (Q.reduction.Q i) a) w))) := hU _
    _ = Tj (R (localTangentSynth Q i x a (Fi w))) := by rw [hFi]
    _ = Tj (localTangentSynth Q j (f • x) d (R (Fi w))) := by rw [hraw]
    _ = (synth (Q.reduction.Q j) d) (Tj (R (Fi w))) := hTj _
    _ = _ := by rw [← hU]

theorem movingAdaptedDerivative_inverse_on_overlap
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source)
    (w : E) :
    movingAdaptedDerivative Q f₀ x₀ (f,x)
      (movingAdaptedInverseDerivative Q f₀ x₀ (f,x) w) = w := by
  let i := achart E x₀
  let j := achart E (f₀ • x₀)
  let k := achart E x
  let l := achart E (f • x)
  let Cik := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k x
  let Cki := (tangentBundleCore 𝓘(ℝ,E) M).coordChange k i x
  let Clj := (tangentBundleCore 𝓘(ℝ,E) M).coordChange l j (f • x)
  let Cjl := (tangentBundleCore 𝓘(ℝ,E) M).coordChange j l (f • x)
  let T := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x
  let S := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((f⁻¹).1 : M → M) (f • x)
  let Fi := Q.frames.fromFrame i x
  let Ti := Q.frames.toFrame i x
  let Fj := Q.frames.fromFrame j (f • x)
  let Tj := Q.frames.toFrame j (f • x)
  have hk := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hl := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • x)
  have hsource (v : E) : Cik (Cki v) = v := by
    calc
      _ = (tangentBundleCore 𝓘(ℝ,E) M).coordChange k k x v :=
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp k i k x
          ⟨⟨hk, hx⟩, hk⟩ v
      _ = v := (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self k x hk v
  have htarget (v : E) : Clj (Cjl v) = v := by
    calc
      _ = (tangentBundleCore 𝓘(ℝ,E) M).coordChange j j (f • x) v :=
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp j l j (f • x)
          ⟨⟨hy, hl⟩, hy⟩ v
      _ = v := (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self j (f • x) hy v
  have hderiv (v : E) : T (S v) = v :=
    tangentEquiv_inverse_after_forward Q f x v
  simp only [movingAdaptedInverseDerivative, movingAdaptedDerivative,
    ContinuousLinearMap.comp_apply, inv_smul_smul]
  change Tj (Clj (T (Cik (Fi
      (Ti (Cki (S (Cjl (Fj w))))))))) = w
  rw [Q.frames.from_to i x hx, hsource, hderiv, htarget,
    Q.frames.to_from j (f • x) hy]

/-- The jointly continuous frozen-frame coefficient is exactly the actual
quaternionic derivative rotation throughout the two-chart overlap. -/
theorem movingCoefficientRotation_eq_true_on_overlap
    (f₀ f : QuaternionicIsometries Q) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source)
    (hy : f • x ∈ (chartAt E (f₀ • x₀)).source)
    (a : Fin 3 → ℝ) :
    movingCoefficientRotation Q f₀ x₀ a (f,x) =
      movingTrueCoefficientAction Q f₀ x₀ a (f,x) := by
  let i := achart E x₀
  let j := achart E (f₀ • x₀)
  let U := movingAdaptedDerivative Q f₀ x₀ (f,x)
  let V := movingAdaptedInverseDerivative Q f₀ x₀ (f,x)
  let b := movingTrueCoefficientAction Q f₀ x₀ a (f,x)
  have hoperator : U.comp ((synth (Q.reduction.Q i) a).comp V) =
      synth (Q.reduction.Q j) b := by
    ext w
    change U ((synth (Q.reduction.Q i) a) (V w)) =
      (synth (Q.reduction.Q j) b) w
    rw [movingAdaptedDerivative_intertwines_synth Q f₀ f x₀ x hx hy a (V w),
      movingAdaptedDerivative_inverse_on_overlap Q f₀ f x₀ x hx hy]
  change coeff (Q.reduction.Q j)
    (U.comp ((synth (Q.reduction.Q i) a).comp V)) = b
  rw [hoperator]
  exact coeff_synth _ _

end
end QuaternionicSymmetry.ManifoldQuaternionicJointSphereCoordinate
