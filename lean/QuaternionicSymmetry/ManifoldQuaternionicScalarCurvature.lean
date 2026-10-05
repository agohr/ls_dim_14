import QuaternionicSymmetry.ManifoldQuaternionicConnection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
Curvature contractions for the genuine tangent connection. The soldering
form identifies coordinate tangent vectors with orthonormal adapted-frame
coordinates. Ricci and scalar contractions are finite sums in an actual
orthonormal basis; they are not free numerical fields.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature

open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped ContDiff Manifold Topology

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := I) (M := M) (n := n))

/-- Inverse of the p-chart soldering form at a valid chart coordinate. -/
def unsolder (p : M) (y : E) : E →L[ℝ] E :=
  let x := (extChartAt I p).symm y
  (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x).comp
    (((tangentBundleCore I M).coordChange (achart H p)
      ((tangentBundleCore I M).indexAt x) x).comp
      (Q.frames.fromFrame (achart H p) x))

/-- The soldering form is a continuous linear equivalence at every chart
point. The proof uses the actual inverse-chart derivative identities. -/
def solderEquiv (p : M) (y : E) (hy : y ∈ (extChartAt I p).target) : E ≃L[ℝ] E where
  toFun := solder Q p y
  invFun := unsolder Q p y
  map_add' := by intros; simp
  map_smul' := by intros; simp
  left_inv v := by
    let x := (extChartAt I p).symm y
    let Z := tangentBundleCore I M
    have hx : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
      simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
        (extChartAt I p).map_target hy
    have hidx := Z.mem_baseSet_at x
    change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x)
      (Z.coordChange (achart H p) (Z.indexAt x) x
        (Q.frames.fromFrame (achart H p) x
          (Q.frames.toFrame (achart H p) x
            (Z.coordChange (Z.indexAt x) (achart H p) x
              ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y) v))))) = v
    rw [Q.frames.from_to (achart H p) x hx]
    rw [Z.coordChange_comp (Z.indexAt x) (achart H p) (Z.indexAt x)
      x ⟨⟨hidx, hx⟩, hidx⟩]
    rw [Z.coordChange_self (Z.indexAt x) x hidx]
    have hd := congrArg (fun L : E →L[ℝ] E => L v)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hd
  right_inv v := by
    let x := (extChartAt I p).symm y
    let Z := tangentBundleCore I M
    have hx : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
      simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
        (extChartAt I p).map_target hy
    have hidx := Z.mem_baseSet_at x
    change Q.frames.toFrame (achart H p) x
      (Z.coordChange (Z.indexAt x) (achart H p) x
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y)
          ((mfderiv I 𝓘(ℝ, E) (extChartAt I p) x)
            (Z.coordChange (achart H p) (Z.indexAt x) x
              (Q.frames.fromFrame (achart H p) x v))))) = v
    have hd := congrArg (fun L : E →L[ℝ] E =>
      L (Z.coordChange (achart H p) (Z.indexAt x) x
        (Q.frames.fromFrame (achart H p) x v)))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    change (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y)
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I p) x)
        (Z.coordChange (achart H p) (Z.indexAt x) x
          (Q.frames.fromFrame (achart H p) x v))) =
      Z.coordChange (achart H p) (Z.indexAt x) x
        (Q.frames.fromFrame (achart H p) x v) at hd
    rw [hd]
    rw [Z.coordChange_comp (achart H p) (Z.indexAt x) (achart H p)
      x ⟨⟨hx, hidx⟩, hx⟩]
    rw [Z.coordChange_self (achart H p) x hx]
    exact Q.frames.to_from (achart H p) x hx v
  continuous_toFun := (solder Q p y).continuous
  continuous_invFun := (unsolder Q p y).continuous

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem solderEquiv_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) (v : E) :
    solderEquiv Q p y hy v =
      Q.frames.toFrame (achart H p) ((extChartAt I p).symm y) v := by
  simpa only [solderEquiv] using
    congrArg (fun T : E →L[ℝ] E => T v) (solder_eq_toFrame Q p y hy)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem unsolder_eq_fromFrame (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) :
    unsolder Q p y =
      Q.frames.fromFrame (achart H p) ((extChartAt I p).symm y) := by
  let x := (extChartAt I p).symm y
  have hx : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy
  ext v
  calc
    unsolder Q p y v =
        unsolder Q p y (Q.frames.toFrame (achart H p) x
          (Q.frames.fromFrame (achart H p) x v)) := by
            rw [Q.frames.to_from (achart H p) x hx]
    _ = Q.frames.fromFrame (achart H p) x v := by
      have h := (solderEquiv Q p y hy).left_inv
        (Q.frames.fromFrame (achart H p) x v)
      simpa only [solderEquiv, solder_eq_toFrame Q p y hy] using h

omit [FiniteDimensional ℝ E] in
theorem unsolder_chartTransition (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) (u : E) :
    fderiv ℝ (chartTransition (I := I) p q) y
        ((solderEquiv Q p y hy.1).symm u) =
      (solderEquiv Q q (chartTransition (I := I) p q y)
        ((extChartAt I q).map_source hy.2)).symm (adaptedGauge Q p q y u) := by
  let z := chartTransition (I := I) p q y
  let hz : z ∈ (extChartAt I q).target := (extChartAt I q).map_source hy.2
  apply (solderEquiv Q q z hz).injective
  have h := congrArg (fun L : E →L[ℝ] E =>
      L ((solderEquiv Q p y hy.1).symm u))
    (solder_chartTransition Q p q y hy)
  have hp : solder Q p y ((solderEquiv Q p y hy.1).symm u) = u :=
    (solderEquiv Q p y hy.1).apply_symm_apply u
  have hq : solder Q q z ((solderEquiv Q q z hz).symm (adaptedGauge Q p q y u)) =
      adaptedGauge Q p q y u :=
    (solderEquiv Q q z hz).apply_symm_apply _
  change (solder Q q z)
    ((fderiv ℝ (chartTransition (I := I) p q) y)
      ((solderEquiv Q p y hy.1).symm u)) =
    solder Q q z ((solderEquiv Q q z hz).symm (adaptedGauge Q p q y u))
  simpa only [ContinuousLinearMap.comp_apply, hp, hq] using h

variable (D : CompatibleTangentConnection Q)

/-- Curvature expressed entirely in orthonormal adapted tangent vectors. -/
def adaptedCurvature (p : M) (y : E) (hy : y ∈ (extChartAt I p).target)
    (u v w : E) : E :=
  CompatibleTangentConnection.curvature Q D p y ((solderEquiv Q p y hy).symm u)
    ((solderEquiv Q p y hy).symm v) w

omit [FiniteDimensional ℝ E] in
/-- The curvature tensor in adapted orthonormal tangent coordinates obeys
the actual frame gauge law on chart overlaps. -/
theorem adaptedCurvature_chartTransition [IsManifold I 2 M]
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) (u v w : E) :
    adaptedCurvature Q D q (chartTransition (I := I) p q y)
      ((extChartAt I q).map_source hy.2)
      (adaptedGauge Q p q y u) (adaptedGauge Q p q y v)
      (adaptedGauge Q p q y w) =
    adaptedGauge Q p q y (adaptedCurvature Q D p y hy.1 u v w) := by
  let g := adaptedGauge Q p q y
  let h := adaptedGaugeInv Q p q y
  have hcurv := CompatibleTangentConnection.curvature_overlap_of_smooth
    Q D p q y ((solderEquiv Q p y hy.1).symm u)
      ((solderEquiv Q p y hy.1).symm v) hy hn
  have hinv := (adaptedGauge_inverse Q p q y hy).2
  have htransport_u := unsolder_chartTransition Q p q y hy u
  have htransport_v := unsolder_chartTransition Q p q y hy v
  change CompatibleTangentConnection.curvature Q D p y
      ((solderEquiv Q p y hy.1).symm u)
      ((solderEquiv Q p y hy.1).symm v) =
    h * (CompatibleTangentConnection.curvature Q D q
      (chartTransition (I := I) p q y)
      (fderiv ℝ (chartTransition (I := I) p q) y
        ((solderEquiv Q p y hy.1).symm u))
      (fderiv ℝ (chartTransition (I := I) p q) y
        ((solderEquiv Q p y hy.1).symm v))) * g at hcurv
  rw [htransport_u, htransport_v] at hcurv
  have happ := congrArg (fun T : E →L[ℝ] E => T w) hcurv
  have happ' := congrArg (fun a : E => g a) happ
  have hstep : g (adaptedCurvature Q D p y hy.1 u v w) =
      g (h (adaptedCurvature Q D q (chartTransition (I := I) p q y)
        ((extChartAt I q).map_source hy.2) (g u) (g v) (g w))) := by
    simpa only [adaptedCurvature, ContinuousLinearMap.mul_apply] using happ'
  calc
    adaptedCurvature Q D q (chartTransition (I := I) p q y)
        ((extChartAt I q).map_source hy.2) (g u) (g v) (g w) =
      (g * h) (adaptedCurvature Q D q (chartTransition (I := I) p q y)
        ((extChartAt I q).map_source hy.2) (g u) (g v) (g w)) := by
          rw [hinv]; rfl
    _ = g (adaptedCurvature Q D p y hy.1 u v w) := hstep.symm

/-- The linear map whose trace is Ricci curvature in the last two arguments. -/
def ricciEndomorphism (p : M) (y : E) (hy : y ∈ (extChartAt I p).target)
    (v w : E) : E →ₗ[ℝ] E where
  toFun u := adaptedCurvature Q D p y hy u v w
  map_add' u u' := by
    simp only [adaptedCurvature, map_add, ContinuousLinearMap.add_apply]
  map_smul' r u := by
    simp only [adaptedCurvature, map_smul, ContinuousLinearMap.smul_apply,
      RingHom.id_apply]

/-- Basis-free Ricci curvature as the trace of the curvature endomorphism. -/
def ricciTrace (p : M) (y : E) (hy : y ∈ (extChartAt I p).target)
    (v w : E) : ℝ :=
  LinearMap.trace ℝ E (ricciEndomorphism Q D p y hy v w)

omit [FiniteDimensional ℝ E] in
/-- Ricci trace is independent of the adapted tangent frame. This follows
from the curvature gauge law and invariance of linear trace under conjugacy. -/
theorem ricciTrace_chartTransition [IsManifold I 2 M]
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) (v w : E) :
    ricciTrace Q D q (chartTransition (I := I) p q y)
      ((extChartAt I q).map_source hy.2)
      (adaptedGauge Q p q y v) (adaptedGauge Q p q y w) =
    ricciTrace Q D p y hy.1 v w := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart H p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart H q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  let e : E ≃ₗ[ℝ] E :=
    (Q.frameTransition (achart H p) (achart H q) x hp hq).toLinearEquiv
  have he (a : E) : e a = adaptedGauge Q p q y a := rfl
  have hendo : ricciEndomorphism Q D q (chartTransition (I := I) p q y)
      ((extChartAt I q).map_source hy.2)
      (adaptedGauge Q p q y v) (adaptedGauge Q p q y w) =
      e.conj (ricciEndomorphism Q D p y hy.1 v w) := by
    ext a
    have h := adaptedCurvature_chartTransition Q D p q y hy hn
      (e.symm a) v w
    rw [← he, e.apply_symm_apply] at h
    simpa only [ricciEndomorphism, LinearEquiv.conj_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using h
  rw [ricciTrace, ricciTrace, hendo, LinearMap.trace_conj']

/-- Ricci contraction of the actual local curvature in an orthonormal
adapted frame. -/
def localRicci (p : M) (y : E) (hy : y ∈ (extChartAt I p).target)
    (v w : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E),
    inner ℝ (adaptedCurvature Q D p y hy
      (stdOrthonormalBasis ℝ E a) v w) (stdOrthonormalBasis ℝ E a)

omit [I.Boundaryless] in
theorem localRicci_eq_trace (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) (v w : E) :
    localRicci Q D p y hy v w = ricciTrace Q D p y hy v w := by
  rw [ricciTrace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  simp only [localRicci, ricciEndomorphism]
  apply Finset.sum_congr rfl
  intro a _
  exact real_inner_comm _ _

/-- The Ricci contraction is a bilinear form on the adapted tangent model. -/
def ricciBilinear (p : M) (y : E) (hy : y ∈ (extChartAt I p).target) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => localRicci Q D p y hy v w
    map_add' := by
      intro w w'
      simp [localRicci, adaptedCurvature, inner_add_left, Finset.sum_add_distrib]
    map_smul' := by
      intro r w
      simp [localRicci, adaptedCurvature, inner_smul_left, Finset.mul_sum]
  }
  map_add' := by
    intro v v'
    ext w
    change localRicci Q D p y hy (v + v') w =
      localRicci Q D p y hy v w + localRicci Q D p y hy v' w
    simp [localRicci, adaptedCurvature, inner_add_left, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    ext w
    change localRicci Q D p y hy (r • v) w = r • localRicci Q D p y hy v w
    simp [localRicci, adaptedCurvature, inner_smul_left, Finset.mul_sum]

/-- Riesz representative of the Ricci bilinear form in the adapted model. -/
def ricciOperator (p : M) (y : E) (hy : y ∈ (extChartAt I p).target) :
    E →ₗ[ℝ] E where
  toFun v := ∑ a : Fin (Module.finrank ℝ E),
    ricciBilinear Q D p y hy v (stdOrthonormalBasis ℝ E a) •
      stdOrthonormalBasis ℝ E a
  map_add' := by
    intro v v'
    simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp [map_smul, smul_smul, Finset.smul_sum]

omit [I.Boundaryless] in
theorem ricciOperator_inner (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) (v w : E) :
    inner ℝ (ricciOperator Q D p y hy v) w = ricciBilinear Q D p y hy v w := by
  let b := stdOrthonormalBasis ℝ E
  have hsum := congrArg (fun z : E => ricciBilinear Q D p y hy v z)
    (b.sum_repr' w)
  simp only [map_sum, map_smul] at hsum
  calc
    inner ℝ (ricciOperator Q D p y hy v) w =
      ∑ a : Fin (Module.finrank ℝ E),
        (inner ℝ (b a) w) * ricciBilinear Q D p y hy v (b a) := by
          simp [ricciOperator, b, sum_inner, real_inner_smul_left, mul_comm]
    _ = ricciBilinear Q D p y hy v w := by
      simpa only [smul_eq_mul, mul_comm] using hsum

omit [I.Boundaryless] in
theorem ricciOperator_trace_eq_diagonal (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    LinearMap.trace ℝ E (ricciOperator Q D p y hy) =
      ∑ a, ricciBilinear Q D p y hy (b a) (b a) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro a _
  rw [real_inner_comm, ricciOperator_inner]

/-- Scalar curvature is the trace of the Ricci contraction. This is a
computed curvature contraction, with no sign or positivity assumption. -/
def localScalarCurvature (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E),
    localRicci Q D p y hy (stdOrthonormalBasis ℝ E a) (stdOrthonormalBasis ℝ E a)

/-- On a chart overlap, the actual adapted tangent frame transition is a
linear isometry of the Euclidean tangent model. -/
def adaptedGaugeIsometry (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) : E ≃ₗᵢ[ℝ] E := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart H p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart H q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  refine { (Q.frameTransition (achart H p) (achart H q) x hp hq).toLinearEquiv with
    norm_map' := ?_ }
  intro v
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (Q.frameTransition_inner (achart H p) (achart H q)
    x hp hq v v)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem adaptedGaugeIsometry_apply (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) (v : E) :
    adaptedGaugeIsometry Q p q y hy v = adaptedGauge Q p q y v := rfl

/-- The computed scalar curvature has the same value in every adapted
tangent chart containing a point. -/
theorem localScalarCurvature_chartTransition [IsManifold I 2 M]
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    localScalarCurvature Q D q (chartTransition (I := I) p q y)
      ((extChartAt I q).map_source hy.2) =
    localScalarCurvature Q D p y hy.1 := by
  let b := stdOrthonormalBasis ℝ E
  let e := adaptedGaugeIsometry Q p q y hy
  let z := chartTransition (I := I) p q y
  let hz : z ∈ (extChartAt I q).target := (extChartAt I q).map_source hy.2
  calc
    localScalarCurvature Q D q z hz =
        LinearMap.trace ℝ E (ricciOperator Q D q z hz) := by
          simpa only [localScalarCurvature, ricciBilinear] using
            (ricciOperator_trace_eq_diagonal Q D q z hz b).symm
    _ = ∑ a : Fin (Module.finrank ℝ E),
        ricciBilinear Q D q z hz ((b.map e) a) ((b.map e) a) :=
          ricciOperator_trace_eq_diagonal Q D q z hz (b.map e)
    _ = ∑ a : Fin (Module.finrank ℝ E),
        ricciBilinear Q D p y hy.1 (b a) (b a) := by
          apply Finset.sum_congr rfl
          intro a _
          change localRicci Q D q z hz (e (b a)) (e (b a)) =
            localRicci Q D p y hy.1 (b a) (b a)
          rw [localRicci_eq_trace Q D q z hz,
            localRicci_eq_trace Q D p y hy.1]
          change ricciTrace Q D q (chartTransition (I := I) p q y)
              ((extChartAt I q).map_source hy.2)
              (adaptedGauge Q p q y (b a)) (adaptedGauge Q p q y (b a)) =
            ricciTrace Q D p y hy.1 (b a) (b a)
          exact ricciTrace_chartTransition Q D p q y hy hn (b a) (b a)
    _ = localScalarCurvature Q D p y hy.1 := by
          rfl

/-- A scalar curvature value at a manifold point using its preferred chart. -/
def preferredScalarCurvature (x : M) : ℝ :=
  localScalarCurvature Q D x (extChartAt I x x) (by
    exact (extChartAt I x).map_source (by simp))

/-- The preferred value is the contraction computed in any chart containing
the point. -/
theorem localScalarCurvature_eq_preferred [IsManifold I 2 M]
    (p x : M) (hx : x ∈ (extChartAt I p).source)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    localScalarCurvature Q D p (extChartAt I p x)
      ((extChartAt I p).map_source hx) = preferredScalarCurvature Q D x := by
  let y := extChartAt I p x
  have hy : y ∈ chartOverlap (I := I) p x := by
    refine ⟨(extChartAt I p).map_source hx, ?_⟩
    simpa only [y, (extChartAt I p).left_inv hx] using
      (show x ∈ (extChartAt I x).source by simp)
  have h := localScalarCurvature_chartTransition Q D p x y hy hn
  simpa only [preferredScalarCurvature, chartTransition, y,
    (extChartAt I p).left_inv hx] using h.symm

/-- Natural positive scalar curvature data for a compatible
almost-quaternionic tangent connection. Positivity refers to the contraction
of its actual curvature, in every adapted chart. -/
structure PositiveScalarTangentGeometry where
  connection : CompatibleTangentConnection Q
  scalar_pos : ∀ p y (hy : y ∈ (extChartAt I p).target),
    0 < localScalarCurvature Q connection p y hy

omit [I.Boundaryless] in
theorem PositiveScalarTangentGeometry.preferredScalarCurvature_pos
    (G : PositiveScalarTangentGeometry Q) (x : M) :
    0 < preferredScalarCurvature Q G.connection x :=
  G.scalar_pos x (extChartAt I x x) (by
    exact (extChartAt I x).map_source (by simp))

end
end QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
