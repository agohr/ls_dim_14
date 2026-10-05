import QuaternionicSymmetry.ManifoldQuaternionicDerivativeAction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The derivative of an actual quaternionic isometry has a smooth matrix in
fixed adapted source and target charts. This is the local differentiability
ingredient for the base-dependent twistor-sphere lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryLocalDerivative

open ManifoldQuaternionicSpanSymmetry
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- In fixed charts centered at `p` and `f p`, take the actual manifold
derivative and convert to the two adapted quaternionic frames. -/
def localAdaptedDerivative (f : QuaternionicIsometries Q) (p x : M) :
    E →L[ℝ] E :=
  (Q.frames.toFrame (achart E (f • p)) (f • x)).comp
    ((inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (f.1 : M → M)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) p x).comp
      (Q.frames.fromFrame (achart E p) x))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- On the overlap of the fixed source and target charts, the smooth local
matrix is exactly the actual derivative, with the two tangent-coordinate
changes and adapted-frame gauges written out. -/
theorem localAdaptedDerivative_eq_on_overlap
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source) :
    localAdaptedDerivative Q f p x =
      (Q.frames.toFrame (achart E (f • p)) (f • x)).comp
        (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E (f • x)) (achart E (f • p)) (f • x)).comp
          ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x).comp
            (((tangentBundleCore 𝓘(ℝ,E) M).coordChange
              (achart E p) (achart E x) x).comp
                (Q.frames.fromFrame (achart E p) x)))) := by
  simp only [localAdaptedDerivative]
  rw [inTangentCoordinates_eq id (f.1 : M → M)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) hx hy]
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem inTangentCoordinates_isometry_center
    (f : QuaternionicIsometries Q) (p : M) :
    inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (f.1 : M → M)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) p p =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) p := by
  rw [inTangentCoordinates_eq id (f.1 : M → M)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M))
    (mem_chart_source E p) (mem_chart_source E (f • p))]
  ext v
  simp only [ContinuousLinearMap.comp_apply, id_eq]
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E p) p (mem_chart_source E p),
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E (f.1 p)) (f.1 p) (mem_chart_source E (f.1 p))]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem localAdaptedDerivative_center_apply
    (f : QuaternionicIsometries Q) (p : M) (v : E) :
    localAdaptedDerivative Q f p p v =
      Q.frames.toFrame (achart E (f • p)) (f • p)
        (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f p
          (Q.frames.fromFrame (achart E p) p v)) := by
  simp only [localAdaptedDerivative, ContinuousLinearMap.comp_apply]
  rw [inTangentCoordinates_isometry_center,
    ManifoldQuaternionicDerivativeAction.tangentEquiv_apply]
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem localAdaptedInverseDerivative_center_apply
    (f : QuaternionicIsometries Q) (p : M) (v : E) :
    localAdaptedDerivative Q f⁻¹ (f • p) (f • p) v =
      Q.frames.toFrame (achart E p) p
        (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f⁻¹ (f • p)
          (Q.frames.fromFrame (achart E (f • p)) (f • p) v)) := by
  simpa only [inv_smul_smul] using
    localAdaptedDerivative_center_apply Q f⁻¹ (f • p) v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem localAdaptedDerivative_smoothAt
    (f : QuaternionicIsometries Q) (p : M) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (localAdaptedDerivative Q f p) p := by
  let i := achart E p
  let j := achart E (f • p)
  have hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (f.1 : M → M) p :=
    f.1.contMDiff p
  have hD : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (f.1 : M → M)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) p) p :=
    hf.mfderiv_const (by simp)
  have hto : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.toFrame j) (f • p) :=
    (Q.frames.smooth_to j).contMDiffAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet j |>.mem_nhds
        ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • p)))
  have hfrom : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (Q.frames.fromFrame i) p :=
    (Q.frames.smooth_from i).contMDiffAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet i |>.mem_nhds
        ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p))
  exact (hto.comp p hf).clm_comp (hD.clm_comp hfrom)

/-- The reverse adapted-frame derivative, evaluated at the image point, is
smooth as a function of the original base point. It supplies the inverse
matrix for the local conjugation formula. -/
def localAdaptedInverseDerivative (f : QuaternionicIsometries Q)
    (p x : M) : E →L[ℝ] E :=
  localAdaptedDerivative Q f⁻¹ (f • p) (f • x)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentEquiv_inverse_after_forward
    (f : QuaternionicIsometries Q) (p : M)
    (v : TangentSpace 𝓘(ℝ,E) (f • p)) :
    ManifoldQuaternionicDerivativeAction.tangentEquiv Q f p
      (ManifoldQuaternionicDerivativeAction.tangentEquiv Q f⁻¹ (f • p) v) = v := by
  have h := ManifoldQuaternionicDerivativeAction.tangentEquiv_mul_apply
    Q f f⁻¹ (f • p) v
  have h₁ : f * f⁻¹ = (1 : QuaternionicIsometries Q) := mul_inv_cancel f
  have h₂ : f⁻¹ • (f • p) = p := inv_smul_smul f p
  rw [h₁, h₂] at h
  exact h.symm.trans
    (ManifoldQuaternionicDerivativeAction.tangentEquiv_one_apply Q (f • p) v)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem localAdaptedDerivative_inverse_center
    (f : QuaternionicIsometries Q) (p : M) (w : E) :
    localAdaptedDerivative Q f p p
      (localAdaptedInverseDerivative Q f p p w) = w := by
  rw [localAdaptedInverseDerivative,
    localAdaptedInverseDerivative_center_apply,
    localAdaptedDerivative_center_apply]
  rw [Q.frames.from_to (achart E p) p
    ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at p)]
  rw [tangentEquiv_inverse_after_forward Q f p]
  exact Q.frames.to_from (achart E (f • p)) (f • p)
    ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (f • p)) w

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem localAdaptedInverseDerivative_smoothAt
    (f : QuaternionicIsometries Q) (p : M) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (localAdaptedInverseDerivative Q f p) p := by
  have hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (f.1 : M → M) p :=
    f.1.contMDiff p
  exact (localAdaptedDerivative_smoothAt Q f⁻¹ (f • p)).comp p hf

/-- Fixed-chart quaternionic coefficient extraction from the smooth forward
and reverse adapted derivative matrices. Outside the overlap neighborhood
this is merely a smooth extension; on that neighborhood it is the true
quaternionic derivative rotation. -/
def localCoefficientRotation (f : QuaternionicIsometries Q)
    (p x : M) (a : Fin 3 → ℝ) : Fin 3 → ℝ :=
  coeff (Q.reduction.Q (achart E (f • p)))
    ((localAdaptedDerivative Q f p x).comp
      ((synth (Q.reduction.Q (achart E p)) a).comp
        (localAdaptedInverseDerivative Q f p x)))

theorem localCoefficientRotation_smoothAt
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun x => localCoefficientRotation Q f p x a) p := by
  let A := synth (Q.reduction.Q (achart E p)) a
  have hA : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun _ : M => A) p := contMDiffAt_const
  have hD := localAdaptedDerivative_smoothAt Q f p
  have hI := localAdaptedInverseDerivative_smoothAt Q f p
  have hC : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun x => (localAdaptedDerivative Q f p x).comp
        (A.comp (localAdaptedInverseDerivative Q f p x))) p :=
    hD.clm_comp (hA.clm_comp hI)
  exact ((coeff (Q.reduction.Q (achart E (f • p)))).contMDiff
    ((localAdaptedDerivative Q f p p).comp
      (A.comp (localAdaptedInverseDerivative Q f p p)))).comp p hC

/-- The fixed-chart quaternionic coefficient formula is jointly smooth in
the base point and all three real sphere coefficients. -/
theorem localCoefficientRotation_jointSmoothAt
    (f : QuaternionicIsometries Q) (p : M) (a : Fin 3 → ℝ) :
    ContMDiffAt ((𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun q : M × (Fin 3 → ℝ) =>
        localCoefficientRotation Q f p q.1 q.2) (p,a) := by
  let P := (𝓘(ℝ,E)).prod 𝓘(ℝ,Fin 3 → ℝ)
  have hfst : ContMDiffAt P 𝓘(ℝ,E) ∞
      (Prod.fst : M × (Fin 3 → ℝ) → M) (p,a) := contMDiffAt_fst
  have hsnd : ContMDiffAt P 𝓘(ℝ,Fin 3 → ℝ) ∞
      (Prod.snd : M × (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p,a) :=
    contMDiffAt_snd
  have hD : ContMDiffAt P 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun q : M × (Fin 3 → ℝ) => localAdaptedDerivative Q f p q.1)
      (p,a) := (localAdaptedDerivative_smoothAt Q f p).comp (p,a) hfst
  have hI0 : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (localAdaptedInverseDerivative Q f p) p :=
    localAdaptedInverseDerivative_smoothAt Q f p
  have hI1 := hI0.comp (p,a) hfst
  have hI : ContMDiffAt P 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun q : M × (Fin 3 → ℝ) =>
        localAdaptedInverseDerivative Q f p q.1) (p,a) :=
    hI1
  have hA : ContMDiffAt P 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun q : M × (Fin 3 → ℝ) =>
        synth (Q.reduction.Q (achart E p)) q.2) (p,a) :=
    ((synth (Q.reduction.Q (achart E p))).contMDiff a).comp (p,a) hsnd
  have hC : ContMDiffAt P 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun q : M × (Fin 3 → ℝ) =>
        (localAdaptedDerivative Q f p q.1).comp
          ((synth (Q.reduction.Q (achart E p)) q.2).comp
            (localAdaptedInverseDerivative Q f p q.1))) (p,a) :=
    hD.clm_comp (hA.clm_comp hI)
  exact ((coeff (Q.reduction.Q (achart E (f • p)))).contMDiff
    ((localAdaptedDerivative Q f p p).comp
      ((synth (Q.reduction.Q (achart E p)) a).comp
        (localAdaptedInverseDerivative Q f p p)))).comp (p,a) hC

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryLocalDerivative
