import QuaternionicSymmetry.ManifoldQuaternionicLocalGaugeTransport
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients

/-! Fixed-chart derivative equivariance for the actual quaternionic
three-plane, throughout a source/target chart overlap. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicDerivativeAction
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalGaugeTransport
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual derivative, expressed between fixed source and target tangent
charts but before adapted frame gauges. -/
def localRawDerivative (f : QuaternionicIsometries Q) (p x : M) : E →L[ℝ] E :=
  ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E (f • x)) (achart E (f • p)) (f • x)).comp
    ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x).comp
      ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
        (achart E p) (achart E x) x))

/-- Coefficients in fixed charts are obtained from the preferred intrinsic
derivative rotation by the actual rank-three frame transitions. -/
def localTrueCoefficientAction (f : QuaternionicIsometries Q)
    (p x : M) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Q.reduction.rankThreeCoordChange (achart E (f • x))
    (achart E (f • p)) (f • x)
      (coefficientAction Q f x
        (Q.reduction.rankThreeCoordChange (achart E p) (achart E x) x a))

/-- On the overlap, the chart-level derivative intertwines the locally
represented quaternionic endomorphisms. -/
theorem localRawDerivative_intertwines
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (a : Fin 3 → ℝ) (v : E) :
    localRawDerivative Q f p x (localTangentSynth Q (achart E p) x a v) =
      localTangentSynth Q (achart E (f • p)) (f • x)
        (localTrueCoefficientAction Q f p x a)
        (localRawDerivative Q f p x v) := by
  let i := achart E p
  let k := achart E x
  let l := achart E (f • x)
  let j := achart E (f • p)
  let C := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k x
  let D := (tangentBundleCore 𝓘(ℝ,E) M).coordChange l j (f • x)
  let F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x
  let b := Q.reduction.rankThreeCoordChange i k x a
  let c := coefficientAction Q f x b
  have hk := Q.frames.adaptedCore.mem_baseSet_at x
  have hl := Q.frames.adaptedCore.mem_baseSet_at (f • x)
  have hsrc := localTangentSynth_coordChange Q i k x hx hk a v
  have htgt := localTangentSynth_coordChange Q l j (f • x) hl hy c (F (C v))
  have hdf : F (localTangentSynth Q k x b (C v)) =
      localTangentSynth Q l (f • x) c (F (C v)) := by
    have h := congrArg (fun A : TangentSpace 𝓘(ℝ,E) (f • x) →L[ℝ]
      TangentSpace 𝓘(ℝ,E) (f • x) => A (tangentEquiv Q f x (C v)))
      (tangentSynth_coefficientAction Q f x b)
    change tangentSynth Q (f • x) c (tangentEquiv Q f x (C v)) =
      tangentConjugation Q f x (tangentSynth Q x b)
        (tangentEquiv Q f x (C v)) at h
    rw [tangentConjugation_apply_tangentEquiv] at h
    exact h.symm
  change D (F (C (localTangentSynth Q i x a v))) =
    localTangentSynth Q j (f • x)
      (Q.reduction.rankThreeCoordChange l j (f • x) c)
        (D (F (C v)))
  rw [← hsrc, hdf, htgt]

/-- The same equivariance after the source and target adapted-frame gauges;
this is the precise neighborhood relation needed to identify the smooth
three-by-three coefficient matrix with the geometric twistor lift. -/
theorem localAdaptedDerivative_intertwines_synth
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (a : Fin 3 → ℝ) (w : E) :
    localAdaptedDerivative Q f p x
      ((synth (Q.reduction.Q (achart E p)) a) w) =
    (synth (Q.reduction.Q (achart E (f • p)))
      (localTrueCoefficientAction Q f p x a))
        (localAdaptedDerivative Q f p x w) := by
  let i := achart E p
  let j := achart E (f • p)
  let R := localRawDerivative Q f p x
  let Fi := Q.frames.fromFrame i x
  let Ti := Q.frames.toFrame i x
  let Fj := Q.frames.fromFrame j (f • x)
  let Tj := Q.frames.toFrame j (f • x)
  have hi : x ∈ Q.frames.adaptedCore.baseSet i := hx
  have hj : f • x ∈ Q.frames.adaptedCore.baseSet j := hy
  have hU (v : E) : localAdaptedDerivative Q f p x v = Tj (R (Fi v)) := by
    rw [localAdaptedDerivative_eq_on_overlap Q f p x hx hy]
    rfl
  have hFi : Fi ((synth (Q.reduction.Q i) a) w) =
      localTangentSynth Q i x a (Fi w) := by
    change Fi ((synth (Q.reduction.Q i) a) w) =
      Fi ((synth (Q.reduction.Q i) a) (Ti (Fi w)))
    rw [Q.frames.to_from i x hi]
  have hTj (v : E) : Tj (localTangentSynth Q j (f • x)
      (localTrueCoefficientAction Q f p x a) v) =
      (synth (Q.reduction.Q j) (localTrueCoefficientAction Q f p x a))
        (Tj v) := by
    change Tj (Fj ((synth (Q.reduction.Q j)
      (localTrueCoefficientAction Q f p x a)) (Tj v))) = _
    rw [Q.frames.to_from j (f • x) hj]
  calc
    localAdaptedDerivative Q f p x ((synth (Q.reduction.Q i) a) w) =
        Tj (R (Fi ((synth (Q.reduction.Q i) a) w))) := hU _
    _ = Tj (R (localTangentSynth Q i x a (Fi w))) := by rw [hFi]
    _ = Tj (localTangentSynth Q j (f • x)
        (localTrueCoefficientAction Q f p x a) (R (Fi w))) := by
      rw [localRawDerivative_intertwines Q f p x hx hy a (Fi w)]
    _ = (synth (Q.reduction.Q j) (localTrueCoefficientAction Q f p x a))
        (Tj (R (Fi w))) := hTj _
    _ = _ := by rw [← hU]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The raw fixed-chart derivative and that of the inverse diffeomorphism
cancel on the chart overlap. -/
theorem localRawDerivative_inverse
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (w : E) :
    localRawDerivative Q f p x
      (localRawDerivative Q f⁻¹ (f • p) (f • x) w) = w := by
  let k := achart E x
  let i := achart E p
  let l := achart E (f • x)
  let j := achart E (f • p)
  let Cki := (tangentBundleCore 𝓘(ℝ,E) M).coordChange k i x
  let Cik := (tangentBundleCore 𝓘(ℝ,E) M).coordChange i k x
  let Clj := (tangentBundleCore 𝓘(ℝ,E) M).coordChange l j (f • x)
  let Cjl := (tangentBundleCore 𝓘(ℝ,E) M).coordChange j l (f • x)
  have hk := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have hl := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • x)
  have hsource (v : E) : Cik (Cki v) = v := by
    calc
      _ = (tangentBundleCore 𝓘(ℝ,E) M).coordChange k k x v :=
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp k i k x
          ⟨⟨hk, hx⟩, hk⟩ v
      _ = v := (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self k x hk v
  have htarget : Clj (Cjl w) = w := by
    calc
      _ = (tangentBundleCore 𝓘(ℝ,E) M).coordChange j j (f • x) w :=
        (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp j l j (f • x)
          ⟨⟨hy, hl⟩, hy⟩ w
      _ = w := (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self j (f • x) hy w
  have hderiv (v : E) :
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((f⁻¹).1 : M → M) (f • x) v) = v :=
    tangentEquiv_inverse_after_forward Q f x v
  have hbase : f⁻¹ • (f • x) = x := inv_smul_smul f x
  have hbasep : f⁻¹ • (f • p) = p := inv_smul_smul f p
  simp only [localRawDerivative, ContinuousLinearMap.comp_apply]
  rw [hbase, hbasep]
  change Clj ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x)
    (Cik (Cki ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ((f⁻¹).1 : M → M)
      (f • x)) (Cjl w))))) = w
  rw [hsource, hderiv, htarget]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Inverse cancellation persists after the adapted frame gauges. -/
theorem localAdaptedDerivative_inverse_on_overlap
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (w : E) :
    localAdaptedDerivative Q f p x
      (localAdaptedInverseDerivative Q f p x w) = w := by
  let i := achart E p
  let j := achart E (f • p)
  let Fi := Q.frames.fromFrame i x
  let Ti := Q.frames.toFrame i x
  let Fj := Q.frames.fromFrame j (f • x)
  let Tj := Q.frames.toFrame j (f • x)
  let R := localRawDerivative Q f p x
  let S := localRawDerivative Q f⁻¹ (f • p) (f • x)
  have hi : x ∈ Q.frames.adaptedCore.baseSet i := hx
  have hj : f • x ∈ Q.frames.adaptedCore.baseSet j := hy
  have hbase : f⁻¹ • (f • x) = x := inv_smul_smul f x
  have hbasep : f⁻¹ • (f • p) = p := inv_smul_smul f p
  have hx' : f⁻¹ • (f • x) ∈
      (chartAt E (f⁻¹ • (f • p))).source := by
    simpa only [hbase, hbasep] using hx
  have hU (v : E) : localAdaptedDerivative Q f p x v = Tj (R (Fi v)) := by
    rw [localAdaptedDerivative_eq_on_overlap Q f p x hx hy]
    rfl
  have hV (v : E) : localAdaptedInverseDerivative Q f p x v =
      Ti (S (Fj v)) := by
    change localAdaptedDerivative Q f⁻¹ (f • p) (f • x) v = _
    rw [localAdaptedDerivative_eq_on_overlap Q f⁻¹ (f • p) (f • x) hy hx']
    rw [hbase, hbasep]
    simp only [Ti, S, Fj, localRawDerivative,
      ContinuousLinearMap.comp_apply]
    rw [hbase, hbasep]
    rfl
  calc
    localAdaptedDerivative Q f p x
        (localAdaptedInverseDerivative Q f p x w) =
      Tj (R (Fi (Ti (S (Fj w))))) := by rw [hU, hV]
    _ = Tj (R (S (Fj w))) := by
      rw [Q.frames.from_to i x hi]
    _ = Tj (Fj w) := by rw [localRawDerivative_inverse Q f p x hx hy]
    _ = w := Q.frames.to_from j (f • x) hj w

/-- On the whole fixed-chart overlap, the smooth coefficient formula is
exactly the derivative-induced quaternionic rotation, expressed in the two
fixed adapted frames. -/
theorem localCoefficientRotation_eq_true_on_overlap
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (a : Fin 3 → ℝ) :
    localCoefficientRotation Q f p x a =
      localTrueCoefficientAction Q f p x a := by
  let i := achart E p
  let j := achart E (f • p)
  let U := localAdaptedDerivative Q f p x
  let V := localAdaptedInverseDerivative Q f p x
  have hoperator : U.comp ((synth (Q.reduction.Q i) a).comp V) =
      synth (Q.reduction.Q j) (localTrueCoefficientAction Q f p x a) := by
    ext w
    change U ((synth (Q.reduction.Q i) a) (V w)) =
      (synth (Q.reduction.Q j)
        (localTrueCoefficientAction Q f p x a)) w
    rw [localAdaptedDerivative_intertwines_synth Q f p x hx hy a (V w),
      localAdaptedDerivative_inverse_on_overlap Q f p x hx hy]
  change coeff (Q.reduction.Q j)
    (U.comp ((synth (Q.reduction.Q i) a).comp V)) = _
  rw [hoperator]
  exact coeff_synth _ _

/-- The true fixed-chart quaternionic rotation preserves the actual unit
sphere, by the metric derivative and orthogonal frame transitions. -/
theorem localTrueCoefficientAction_squareNorm
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (a : Fin 3 → ℝ) :
    ManifoldTwistorSphereBundle.squareNorm
      (localTrueCoefficientAction Q f p x a) =
        ManifoldTwistorSphereBundle.squareNorm a := by
  let i := achart E p
  let k := achart E x
  let l := achart E (f • x)
  let j := achart E (f • p)
  have hk := Q.frames.adaptedCore.mem_baseSet_at x
  have hl := Q.frames.adaptedCore.mem_baseSet_at (f • x)
  change ManifoldTwistorSphereBundle.squareNorm
    (Q.reduction.rankThreeCoordChange l j (f • x)
      (coefficientAction Q f x (Q.reduction.rankThreeCoordChange i k x a))) =
    ManifoldTwistorSphereBundle.squareNorm a
  rw [ManifoldTwistorSphereBundle.squareNorm_transition Q l j (f • x) hl hy,
    coefficientAction_squareNorm Q f x,
    ManifoldTwistorSphereBundle.squareNorm_transition Q i k x hx hk]

theorem localCoefficientRotation_squareNorm_on_overlap
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (a : Fin 3 → ℝ) :
    ManifoldTwistorSphereBundle.squareNorm
      (localCoefficientRotation Q f p x a) =
        ManifoldTwistorSphereBundle.squareNorm a := by
  rw [localCoefficientRotation_eq_true_on_overlap Q f p x hx hy]
  exact localTrueCoefficientAction_squareNorm Q f p x hx hy a

end
end QuaternionicSymmetry.ManifoldQuaternionicLocalDerivativeEquivariance
