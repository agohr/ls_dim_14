import QuaternionicSymmetry.ManifoldQuaternionicIsometryAdaptedOrthogonal
import QuaternionicSymmetry.ManifoldQuaternionicConnectionPointwiseUniqueness

/-! Solder-form covariance under an actual metric-quaternionic isometry,
written in fixed source and target adapted charts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- An actual isometry written between two fixed manifold charts. -/
def localIsometryChartMap (f : QuaternionicIsometries Q) (p : M) : E → E :=
  fun y => extChartAt 𝓘(ℝ,E) (f • p)
    (f • ((extChartAt 𝓘(ℝ,E) p).symm y))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The derivative of the fixed-chart isometry is the genuine raw tangent
map already used in the twistor lift. -/
theorem localIsometryChartMap_fderiv
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source) :
    fderiv ℝ (localIsometryChartMap Q f p)
      (extChartAt 𝓘(ℝ,E) p x) = localRawDerivative Q f p x := by
  let y := extChartAt 𝓘(ℝ,E) p x
  have hyt : y ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source
      (by simpa only [extChartAt_source] using hx)
  have hleft : (extChartAt 𝓘(ℝ,E) p).symm y = x :=
    (extChartAt 𝓘(ℝ,E) p).left_inv
      (by simpa only [extChartAt_source] using hx)
  have hsymm : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p y hyt).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hyt)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (f.1 : M → M) x := f.1.contMDiff.mdifferentiable (by simp) x
  have htarget : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) (f • p)) (f • x) :=
    (contMDiffAt_extChartAt' (n := ∞) hy).mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (f.1 : M → M) ((extChartAt 𝓘(ℝ,E) p).symm y) := by
    simpa only [hleft] using hf
  have htarget' : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) (f • p))
      (f • ((extChartAt 𝓘(ℝ,E) p).symm y)) := by
    simpa only [hleft] using htarget
  have hcomp := mfderiv_comp y htarget' (hf'.comp y hsymm)
  rw [mfderiv_comp y hf' hsymm] at hcomp
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      (localIsometryChartMap Q f p) y =
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) (f • p))
        (f • ((extChartAt 𝓘(ℝ,E) p).symm y))).comp
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)
        ((extChartAt 𝓘(ℝ,E) p).symm y)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
          (extChartAt 𝓘(ℝ,E) p).symm y)) at hcomp
  rw [hleft] at hcomp
  have hraw : localRawDerivative Q f p x =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
        (extChartAt 𝓘(ℝ,E) (f • p)) (f • x)).comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
            (extChartAt 𝓘(ℝ,E) p).symm y)) := by
    have h₁ := inTangentCoordinates_eq
      (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
      id (f.1 : M → M)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) hx hy
    have h₂ := inTangentCoordinates_eq_mfderiv_comp
      (f := id) (g := (f.1 : M → M))
      (ϕ := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) hx hy
    calc
      localRawDerivative Q f p x =
          inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id (f.1 : M → M)
            (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M)) p x := h₁.symm
      _ = _ := by
        rw [h₂]
        simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
          id_eq, y, smul_eq_apply]
  rw [mfderiv_eq_fderiv] at hcomp
  exact hcomp.trans hraw.symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The actual adapted derivative transports the soldering form into the
target soldering form applied to the raw chart derivative. This holds at
every point of a fixed-chart overlap, not only at the center. -/
theorem localAdaptedDerivative_solder_covariant
    (f : QuaternionicIsometries Q) (p x : M)
    (hx : x ∈ (chartAt E p).source)
    (hy : f • x ∈ (chartAt E (f • p)).source)
    (u : E) :
    localAdaptedDerivative Q f p x
      (solder Q p (extChartAt 𝓘(ℝ,E) p x) u) =
    solder Q (f • p) (extChartAt 𝓘(ℝ,E) (f • p) (f • x))
      (localRawDerivative Q f p x u) := by
  let i := achart E p
  let j := achart E (f • p)
  let R := localRawDerivative Q f p x
  have hxp : (extChartAt 𝓘(ℝ,E) p x) ∈
      (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simpa only [extChartAt_source] using hx)
  have hfp : (extChartAt 𝓘(ℝ,E) (f • p) (f • x)) ∈
      (extChartAt 𝓘(ℝ,E) (f • p)).target :=
    (extChartAt 𝓘(ℝ,E) (f • p)).map_source
      (by simpa only [extChartAt_source] using hy)
  rw [solder_eq_toFrame Q p _ hxp,
    solder_eq_toFrame Q (f • p) _ hfp]
  rw [(extChartAt 𝓘(ℝ,E) p).left_inv
      (by simpa only [extChartAt_source] using hx),
    (extChartAt 𝓘(ℝ,E) (f • p)).left_inv
      (by simpa only [extChartAt_source] using hy)]
  rw [localAdaptedDerivative_eq_on_overlap Q f p x hx hy]
  change Q.frames.toFrame j (f • x)
      (R (Q.frames.fromFrame i x (Q.frames.toFrame i x u))) =
    Q.frames.toFrame j (f • x) (R u)
  rw [Q.frames.from_to i x (by simpa only [tangentBundleCore_baseSet, coe_achart] using hx)]

end
end QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder
