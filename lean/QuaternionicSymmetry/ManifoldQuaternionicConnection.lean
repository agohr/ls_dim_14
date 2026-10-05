import QuaternionicSymmetry.ManifoldQuaternionicMetric
import QuaternionicSymmetry.LocalConnectionCoordinatePullback
import QuaternionicSymmetry.LocalConnectionGauge
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
Local Christoffel forms for a connection on an actual almost-quaternionic
tangent bundle. The forms are written in the orthonormal tangent gauges from
`ManifoldQuaternionicMetric`; their overlap equation is the usual affine
connection transformation under both chart and frame changes. Curvature is
computed from Fréchet derivatives of these forms.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicConnection

open Bundle
open scoped Manifold Topology ContDiff

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

abbrev Endomorphism := E →L[ℝ] E
abbrev ConnectionForm := LocalConnection.Form (E := E) (A := Endomorphism (E := E))

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))

/-- The change of model-space coordinates between two manifold charts. -/
def chartTransition (p q : M) (y : E) : E :=
  extChartAt I q ((extChartAt I p).symm y)

/-- The change from the p-adapted tangent frame to the q-adapted tangent
frame, evaluated at a point given in p-chart coordinates. -/
def adaptedGauge (p q : M) (y : E) : Endomorphism (E := E) :=
  Q.frames.coordChange (achart H p) (achart H q) ((extChartAt I p).symm y)

def adaptedGaugeInv (p q : M) (y : E) : Endomorphism (E := E) :=
  Q.frames.coordChange (achart H q) (achart H p) ((extChartAt I p).symm y)

/-- The locus on which both preferred charts and their adapted frames are
valid, expressed in p-chart coordinates. -/
def chartOverlap (p q : M) : Set E :=
  {y | y ∈ (extChartAt I p).target ∧
    (extChartAt I p).symm y ∈ (extChartAt I q).source}

omit [IsManifold I 1 M] in
theorem chartOverlap_isOpen (p q : M) : IsOpen (chartOverlap (I := I) p q) := by
  change IsOpen ((extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (extChartAt I q).source)
  exact (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := I) p) (isOpen_extChartAt_source (I := I) q)

omit [IsManifold I 1 M] in
theorem chartTransition_contDiffAt [IsManifold I 2 M] (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    ContDiffAt ℝ 2 (chartTransition (I := I) p q) y := by
  have h₁ : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy.1)
  have h₂ : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I q)
      ((extChartAt I p).symm y) := by
    exact contMDiffAt_extChartAt' (by
      simpa only [← extChartAt_source I] using hy.2)
  exact (h₂.comp y h₁).contDiffAt

theorem chartTransition_derivative_eq_core (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    fderiv ℝ (chartTransition (I := I) p q) y =
      (tangentBundleCore I M).coordChange (achart H p) (achart H q)
        ((extChartAt I p).symm y) := by
  have hy' : extChartAt I p ((extChartAt I p).symm y) = y :=
    (extChartAt I p).right_inv hy.1
  change fderiv ℝ ((extChartAt I q) ∘ (extChartAt I p).symm) y =
    fderivWithin ℝ ((extChartAt I q) ∘ (extChartAt I p).symm)
      (Set.range I) (extChartAt I p ((extChartAt I p).symm y))
  rw [I.range_eq_univ, fderivWithin_univ, hy']

omit [I.Boundaryless] in
theorem adaptedGauge_inverse (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    adaptedGaugeInv Q p q y * adaptedGauge Q p q y = 1 ∧
      adaptedGauge Q p q y * adaptedGaugeInv Q p q y = 1 := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart H p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart H q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  constructor
  · ext v
    change Q.frames.coordChange (achart H q) (achart H p) x
      (Q.frames.coordChange (achart H p) (achart H q) x v) = v
    rw [Q.frames.coordChange_comp (achart H p) (achart H q) (achart H p)
      x hp hq hp v, Q.frames.coordChange_self (achart H p) x hp]
  · ext v
    change Q.frames.coordChange (achart H p) (achart H q) x
      (Q.frames.coordChange (achart H q) (achart H p) x v) = v
    rw [Q.frames.coordChange_comp (achart H q) (achart H p) (achart H q)
      x hq hp hq v, Q.frames.coordChange_self (achart H q) x hq]

theorem adaptedGauge_inverse_eventually (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    (fun z => adaptedGaugeInv Q p q z * adaptedGauge Q p q z) =ᶠ[𝓝 y]
      fun _ => 1 := by
  filter_upwards [(chartOverlap_isOpen (I := I) p q).mem_nhds hy] with z hz
  exact (adaptedGauge_inverse Q p q z hz).1

theorem adaptedGauge_contDiffAt [IsManifold I 2 M] (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    ContDiffAt ℝ 2 (adaptedGauge Q p q) y := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ (tangentBundleCore I M).baseSet (achart H q) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  have hopen : IsOpen ((tangentBundleCore I M).baseSet (achart H p) ∩
      (tangentBundleCore I M).baseSet (achart H q)) :=
    ((tangentBundleCore I M).isOpen_baseSet _).inter
      ((tangentBundleCore I M).isOpen_baseSet _)
  have hframe : ContMDiffAt I 𝓘(ℝ, Endomorphism (E := E)) 2
      (Q.frames.coordChange (achart H p) (achart H q)) x :=
    ((Q.frames.smooth_coordChange (achart H p) (achart H q) x ⟨hp, hq⟩).of_le hn).contMDiffAt
      (hopen.mem_nhds ⟨hp, hq⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

theorem adaptedGaugeInv_contDiffAt [IsManifold I 2 M] (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    ContDiffAt ℝ 2 (adaptedGaugeInv Q p q) y := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ (tangentBundleCore I M).baseSet (achart H q) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  have hopen : IsOpen ((tangentBundleCore I M).baseSet (achart H q) ∩
      (tangentBundleCore I M).baseSet (achart H p)) :=
    ((tangentBundleCore I M).isOpen_baseSet _).inter
      ((tangentBundleCore I M).isOpen_baseSet _)
  have hframe : ContMDiffAt I 𝓘(ℝ, Endomorphism (E := E)) 2
      (Q.frames.coordChange (achart H q) (achart H p)) x :=
    ((Q.frames.smooth_coordChange (achart H q) (achart H p) x ⟨hq, hp⟩).of_le hn).contMDiffAt
      (hopen.mem_nhds ⟨hq, hp⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

/-- The p-chart soldering one-form carries coordinate tangent vectors to
their coordinates in the adapted orthonormal tangent frame. -/
def solder (p : M) (y : E) : E →L[ℝ] E :=
  let x := (extChartAt I p).symm y
  (Q.frames.toFrame (achart H p) x).comp
    (((tangentBundleCore I M).coordChange
      ((tangentBundleCore I M).indexAt x) (achart H p) x).comp
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y))

omit [I.Boundaryless] in
theorem tangentCoordChange_toChart_eq_mfderiv (p x : M)
    (hx : x ∈ (extChartAt I p).source) :
    (tangentBundleCore I M).coordChange
      ((tangentBundleCore I M).indexAt x) (achart H p) x =
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
  simp only [mfderiv, tangentBundleCore_coordChange, tangentBundleCore_indexAt,
    (mdifferentiableAt_extChartAt (I := I) (by
      simpa only [← extChartAt_source I] using hx)), ite_true]
  rfl

omit [I.Boundaryless] in
/-- At a valid p-chart coordinate, the corrected soldering form is exactly
the p-adapted frame map on that coordinate vector. -/
theorem solder_eq_toFrame (p : M) (y : E)
    (hy : y ∈ (extChartAt I p).target) :
    solder Q p y = Q.frames.toFrame (achart H p) ((extChartAt I p).symm y) := by
  let x := (extChartAt I p).symm y
  have hx : x ∈ (extChartAt I p).source := (extChartAt I p).map_target hy
  ext v
  change Q.frames.toFrame (achart H p) x
    (((tangentBundleCore I M).coordChange
      ((tangentBundleCore I M).indexAt x) (achart H p) x)
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y) v)) = _
  rw [tangentCoordChange_toChart_eq_mfderiv (I := I) p x hx]
  have hd := congrArg (fun L : E →L[ℝ] E => L v)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)
  have hd' : (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x)
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y) v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hd
  exact congrArg (Q.frames.toFrame (achart H p) x) hd'

/-- The adapted soldering forms transform by the actual tangent chart
derivative and the actual adapted frame transition. -/
theorem solder_chartTransition (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    (solder Q q (chartTransition (I := I) p q y)).comp
        (fderiv ℝ (chartTransition (I := I) p q) y) =
      (adaptedGauge Q p q y).comp (solder Q p y) := by
  let x := (extChartAt I p).symm y
  have hq : chartTransition (I := I) p q y ∈ (extChartAt I q).target :=
    (extChartAt I q).map_source hy.2
  have hqx : (extChartAt I q).symm (chartTransition (I := I) p q y) = x :=
    (extChartAt I q).left_inv hy.2
  have hp : x ∈ (tangentBundleCore I M).baseSet (achart H p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [solder_eq_toFrame Q q _ hq, solder_eq_toFrame Q p y hy.1,
    chartTransition_derivative_eq_core (I := I) p q y hy]
  change Q.frames.toFrame (achart H q) ((extChartAt I q).symm
      (chartTransition (I := I) p q y))
      ((tangentBundleCore I M).coordChange (achart H p) (achart H q) x v) =
    Q.frames.toFrame (achart H q) x
      ((tangentBundleCore I M).coordChange (achart H p) (achart H q) x
        (Q.frames.fromFrame (achart H p) x
          (Q.frames.toFrame (achart H p) x v)))
  rw [hqx, Q.frames.from_to (achart H p) x hp]

/-- A connection on the tangent bundle, described in the actual adapted
charts. The overlap equation is the standard affine transformation of a
connection; skew-adjointness, preservation of the quaternionic rank-three
span, and vanishing torsion are natural geometric conditions. -/
structure CompatibleTangentConnection where
  form : M → ConnectionForm (E := E)
  smooth_form : ∀ p, ContDiffOn ℝ ∞ (form p) (extChartAt I p).target
  overlap : ∀ p q y, y ∈ chartOverlap (I := I) p q →
    form p y = LocalConnectionGauge.transform
      (LocalConnectionCoordinatePullback.pullback (form q) (chartTransition (I := I) p q))
      (adaptedGauge Q p q) (adaptedGaugeInv Q p q) y
  metric : ∀ p y u v w, y ∈ (extChartAt I p).target →
    inner ℝ ((form p y u) v) w + inner ℝ v ((form p y u) w) = 0
  quaternionic : ∀ p y u t, y ∈ (extChartAt I p).target →
    (form p y u).comp
      (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart H p)) t) -
    (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart H p)) t).comp
      (form p y u) ∈
      VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q (achart H p))
  torsion : ∀ p y u v, y ∈ (extChartAt I p).target →
    fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
      form p y u (solder Q p y v) - form p y v (solder Q p y u) = 0

namespace CompatibleTangentConnection

variable (D : CompatibleTangentConnection Q)

/-- The curvature of the actual local tangent connection. -/
def curvature (p : M) (y : E) :
    LocalConnection.Bilinear (E := E) (A := Endomorphism (E := E)) :=
  LocalConnection.curvature (D.form p) y

omit [I.Boundaryless] in
theorem curvature_antisymm (p : M) (y u v : E) :
    curvature Q D p y u v = -curvature Q D p y v u :=
  LocalConnection.curvature_antisymm (CompatibleTangentConnection.form D p) y u v

omit [I.Boundaryless] in
theorem curvature_self (p : M) (y u : E) : curvature Q D p y u u = 0 :=
  LocalConnection.curvature_self (CompatibleTangentConnection.form D p) y u

/-- Curvature covariance is a consequence of the affine connection overlap
law, the actual adapted frame cocycle, and the chart derivative. The
regularity hypotheses concern only the chart and frame transition maps. -/
theorem curvature_overlap (p q : M) (y u v : E)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hφ : ContDiffAt ℝ 2 (chartTransition (I := I) p q) y)
    (hg : ContDiffAt ℝ 2 (adaptedGauge Q p q) y)
    (hh : DifferentiableAt ℝ (adaptedGaugeInv Q p q) y)
    (hΓ : DifferentiableAt ℝ (D.form q) (chartTransition (I := I) p q y)) :
    curvature Q D p y u v =
      adaptedGaugeInv Q p q y *
        (curvature Q D q (chartTransition (I := I) p q y)
          (fderiv ℝ (chartTransition (I := I) p q) y u)
          (fderiv ℝ (chartTransition (I := I) p q) y v)) *
        adaptedGauge Q p q y := by
  let φ := chartTransition (I := I) p q
  let g := adaptedGauge Q p q
  let h := adaptedGaugeInv Q p q
  let Γ := LocalConnectionCoordinatePullback.pullback (D.form q) φ
  have hEq : D.form p =ᶠ[𝓝 y] LocalConnectionGauge.transform Γ g h := by
    filter_upwards [(chartOverlap_isOpen (I := I) p q).mem_nhds hy] with z hz
    exact D.overlap p q z hz
  have hAt : D.form p y = LocalConnectionGauge.transform Γ g h y :=
    hEq.eq_of_nhds
  have hDeriv : fderiv ℝ (D.form p) y =
      fderiv ℝ (LocalConnectionGauge.transform Γ g h) y := hEq.fderiv_eq
  have hCurv : curvature Q D p y u v =
      LocalConnection.curvature (LocalConnectionGauge.transform Γ g h) y u v := by
    simp only [curvature, LocalConnection.curvature_apply, hAt, hDeriv]
  rw [hCurv]
  have hΓpull : DifferentiableAt ℝ Γ y :=
    LocalConnectionCoordinatePullback.differentiableAt_pullback (D.form q) φ y hΓ hφ
  rw [LocalConnectionGauge.curvature_transform Γ g h y hΓpull hg hh
    (adaptedGauge_inverse_eventually Q p q y hy)
    (adaptedGauge_inverse Q p q y hy).2 u v]
  congr 1
  congr 1
  have hCoord := congrArg (fun F => F ![u, v])
    (LocalConnectionCoordinatePullback.curvatureForm_pullback (D.form q) φ y hΓ hφ)
  simpa only [LocalConnectionForms.curvatureForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hCoord

/-- On a C² boundaryless manifold, the chart and adapted gauge regularity
needed for curvature covariance follows from the smooth tangent reduction
and the connection's local regularity. -/
theorem curvature_overlap_of_smooth [IsManifold I 2 M]
    (p q : M) (y u v : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    curvature Q D p y u v =
      adaptedGaugeInv Q p q y *
        (curvature Q D q (chartTransition (I := I) p q y)
          (fderiv ℝ (chartTransition (I := I) p q) y u)
          (fderiv ℝ (chartTransition (I := I) p q) y v)) *
        adaptedGauge Q p q y := by
  have hq : chartTransition (I := I) p q y ∈ (extChartAt I q).target :=
    (extChartAt I q).map_source hy.2
  have hΓ : DifferentiableAt ℝ (D.form q) (chartTransition (I := I) p q y) :=
    ((D.smooth_form q _ hq).contDiffAt
      ((isOpen_extChartAt_target (I := I) q).mem_nhds hq)).differentiableAt
        (by norm_num)
  exact curvature_overlap Q D p q y u v hy
    (chartTransition_contDiffAt (I := I) p q y hy)
    (adaptedGauge_contDiffAt Q p q y hy hn)
    ((adaptedGaugeInv_contDiffAt Q p q y hy hn).differentiableAt (by norm_num))
    hΓ

end CompatibleTangentConnection

end
end QuaternionicSymmetry.ManifoldQuaternionicConnection
