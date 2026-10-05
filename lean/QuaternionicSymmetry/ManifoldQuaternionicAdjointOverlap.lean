import QuaternionicSymmetry.ManifoldQuaternionicAdjointCurvature

/-! The rank-three gauge associated to a change of adapted tangent charts,
and its induced connection overlap. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap

open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicRankThreeOrthogonal
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))

/-- The three-plane gauge is evaluated at the manifold point represented
by a coordinate in the first chart. -/
def rankThreeGauge (p q : M) (y : E) : R3 →L[ℝ] R3 :=
  Q.reduction.rankThreeCoordChange (achart H p) (achart H q)
    ((extChartAt I p).symm y)

def rankThreeGaugeInv (p q : M) (y : E) : R3 →L[ℝ] R3 :=
  Q.reduction.rankThreeCoordChange (achart H q) (achart H p)
    ((extChartAt I p).symm y)

omit [I.Boundaryless] in
theorem rankThreeGauge_apply (p q : M) (y : E) (a : R3) :
    rankThreeGauge Q p q y a =
      coeff (Q.reduction.Q (achart H q))
        (adaptedGauge Q p q y * synth (Q.reduction.Q (achart H p)) a *
          adaptedGaugeInv Q p q y) := by
  rw [rankThreeGauge, QuaternionicFrameReduction.rankThreeCoordChange_apply,
    adjointCoordChange_apply]
  rfl

omit [I.Boundaryless] in
theorem synth_rankThreeGauge (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) (a : R3) :
    synth (Q.reduction.Q (achart H q)) (rankThreeGauge Q p q y a) =
      adaptedGauge Q p q y * synth (Q.reduction.Q (achart H p)) a *
        adaptedGaugeInv Q p q y := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart H p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart H q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  rw [rankThreeGauge, synth_rankThreeCoordChange Q _ _ x hp hq a,
    adjointCoordChange_apply]
  rfl

omit [I.Boundaryless] in
theorem rankThreeGauge_inverse (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    rankThreeGaugeInv Q p q y * rankThreeGauge Q p q y = 1 ∧
      rankThreeGauge Q p q y * rankThreeGaugeInv Q p q y = 1 := by
  let x := (extChartAt I p).symm y
  have hp : x ∈ Q.frames.adaptedCore.baseSet (achart H p) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using
      (extChartAt I p).map_target hy.1
  have hq : x ∈ Q.frames.adaptedCore.baseSet (achart H q) := by
    simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I] using hy.2
  constructor <;> apply ContinuousLinearMap.ext <;> intro a
  · change Q.reduction.rankThreeCoordChange (achart H q) (achart H p) x
      (Q.reduction.rankThreeCoordChange (achart H p) (achart H q) x a) = a
    rw [Q.reduction.rankThreeCoordChange_comp (achart H p) (achart H q)
      (achart H p) x hp hq hp,
      Q.reduction.rankThreeCoordChange_self (achart H p) x hp]
  · change Q.reduction.rankThreeCoordChange (achart H p) (achart H q) x
      (Q.reduction.rankThreeCoordChange (achart H q) (achart H p) x a) = a
    rw [Q.reduction.rankThreeCoordChange_comp (achart H q) (achart H p)
      (achart H q) x hq hp hq,
      Q.reduction.rankThreeCoordChange_self (achart H q) x hq]

theorem rankThreeGauge_contDiffAt [IsManifold I 2 M]
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    ContDiffAt ℝ 2 (rankThreeGauge Q p q) y := by
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
  have hframe : ContMDiffAt I 𝓘(ℝ, R3 →L[ℝ] R3) 2
      (Q.reduction.rankThreeCoordChange (achart H p) (achart H q)) x :=
    ((Q.smooth_rankThreeCoordChange (achart H p) (achart H q) x ⟨hp, hq⟩).of_le hn).contMDiffAt
      (hopen.mem_nhds ⟨hp, hq⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

theorem rankThreeGaugeInv_contDiffAt [IsManifold I 2 M]
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    ContDiffAt ℝ 2 (rankThreeGaugeInv Q p q) y := by
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
  have hframe : ContMDiffAt I 𝓘(ℝ, R3 →L[ℝ] R3) 2
      (Q.reduction.rankThreeCoordChange (achart H q) (achart H p)) x :=
    ((Q.smooth_rankThreeCoordChange (achart H q) (achart H p) x ⟨hq, hp⟩).of_le hn).contMDiffAt
      (hopen.mem_nhds ⟨hq, hp⟩)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy.1).contMDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hy.1)
  exact (hframe.comp y hsymm).contDiffAt

theorem rankThreeGauge_inverse_eventually (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q) :
    (fun z => rankThreeGaugeInv Q p q z * rankThreeGauge Q p q z) =ᶠ[𝓝 y]
      fun _ => 1 := by
  filter_upwards [(chartOverlap_isOpen (I := I) p q).mem_nhds hy] with z hz
  exact (rankThreeGauge_inverse Q p q z hz).1

omit [Nontrivial E] [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem fderiv_conjugate_const (g h : E → E →L[ℝ] E)
    (T : E →L[ℝ] E) (y u : E)
    (hg : DifferentiableAt ℝ g y) (hh : DifferentiableAt ℝ h y) :
    fderiv ℝ (fun z => g z * T * h z) y u =
      fderiv ℝ g y u * T * h y + g y * T * fderiv ℝ h y u := by
  rw [fderiv_fun_mul' (a := fun z => g z * T) (b := h)
      (hg.mul (differentiableAt_const T)) hh,
    fderiv_mul_const' hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  noncomm_ring

theorem fderiv_rankThreeGauge [IsManifold I 2 M]
    (p q : M) (y u : E) (a : R3)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    fderiv ℝ (rankThreeGauge Q p q) y u a =
      coeff (Q.reduction.Q (achart H q))
        (fderiv ℝ (adaptedGauge Q p q) y u *
            synth (Q.reduction.Q (achart H p)) a * adaptedGaugeInv Q p q y +
          adaptedGauge Q p q y * synth (Q.reduction.Q (achart H p)) a *
            fderiv ℝ (adaptedGaugeInv Q p q) y u) := by
  let g := adaptedGauge Q p q
  let h := adaptedGaugeInv Q p q
  let T := synth (Q.reduction.Q (achart H p)) a
  let c := coeff (Q.reduction.Q (achart H q))
  have hg : DifferentiableAt ℝ g y :=
    (adaptedGauge_contDiffAt Q p q y hy hn).differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ h y :=
    (adaptedGaugeInv_contDiffAt Q p q y hy hn).differentiableAt (by norm_num)
  have hR : DifferentiableAt ℝ (rankThreeGauge Q p q) y :=
    (rankThreeGauge_contDiffAt Q p q y hy hn).differentiableAt (by norm_num)
  rw [← LocalConnectionBianchi.fderiv_eval_const hR a u]
  have hfun : (fun z => rankThreeGauge Q p q z a) =
      fun z => c (g z * T * h z) := by
    funext z
    exact rankThreeGauge_apply Q p q z a
  rw [hfun]
  have hprod : DifferentiableAt ℝ (fun z => g z * T * h z) y :=
    (hg.mul (differentiableAt_const T)).mul hh
  have hcomp := fderiv_comp y c.differentiableAt hprod
  change fderiv ℝ (c ∘ fun z => g z * T * h z) y = _ at hcomp
  change (fderiv ℝ (c ∘ fun z => g z * T * h z) y) u = _
  rw [hcomp, c.fderiv]
  exact congrArg c (fderiv_conjugate_const g h T y u hg hh)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem affine_adjoint_identity (g h Λ dg Γ T dh : E →L[ℝ] E)
    (hgh : g * h = 1)
    (hΓ : Γ = h * (Λ * g + dg))
    (hdh : dh = -(h * dg * h)) :
    g * (Γ * T - T * Γ) * h =
      Λ * (g * T * h) - (g * T * h) * Λ +
        (dg * T * h + g * T * dh) := by
  subst Γ
  subst dh
  simp only [mul_add, add_mul, mul_sub, sub_mul,
    mul_neg, mul_assoc]
  simp only [← mul_assoc g h, hgh, one_mul]
  noncomm_ring

variable (D : CompatibleTangentConnection Q)

/-- Affine overlap of the rank-three connection is derived from the
tangent connection law and the derivative of the frame-induced gauge. -/
theorem inducedForm_overlap [IsManifold I 2 M]
    (p q : M) (y u : E) (a : R3)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    rankThreeGauge Q p q y (inducedForm Q D p y u a) =
      inducedForm Q D q (chartTransition (I := I) p q y)
        (fderiv ℝ (chartTransition (I := I) p q) y u)
        (rankThreeGauge Q p q y a) +
      fderiv ℝ (rankThreeGauge Q p q) y u a := by
  let g := adaptedGauge Q p q
  let h := adaptedGaugeInv Q p q
  let c := coeff (Q.reduction.Q (achart H q))
  let T := synth (Q.reduction.Q (achart H p)) a
  let Γ := D.form p y u
  let Λ := D.form q (chartTransition (I := I) p q y)
    (fderiv ℝ (chartTransition (I := I) p q) y u)
  have hgh : g y * h y = 1 := (adaptedGauge_inverse Q p q y hy).2
  have hg : DifferentiableAt ℝ g y :=
    (adaptedGauge_contDiffAt Q p q y hy hn).differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ h y :=
    (adaptedGaugeInv_contDiffAt Q p q y hy hn).differentiableAt (by norm_num)
  have hdh : fderiv ℝ h y u = -(h y * fderiv ℝ g y u * h y) :=
    LocalConnectionGauge.fderiv_inverse_pair g h y hg hh
      (adaptedGauge_inverse_eventually Q p q y hy) hgh u
  have hΓ : Γ = h y * (Λ * g y + fderiv ℝ g y u) := by
    have hd := congrArg (fun F : E →L[ℝ] E →L[ℝ] E => F u)
      (D.overlap p q y hy)
    change Γ = LocalConnectionGauge.transform
      (LocalConnectionCoordinatePullback.pullback (D.form q)
        (chartTransition (I := I) p q)) g h y u at hd
    simpa only [LocalConnectionGauge.transform_apply,
      LocalConnectionCoordinatePullback.pullback,
      ContinuousLinearMap.comp_apply] using hd
  calc
    _ = c (g y * synth (Q.reduction.Q (achart H p))
          (inducedForm Q D p y u a) * h y) := rankThreeGauge_apply Q p q y _
    _ = c (g y * (Γ * T - T * Γ) * h y) := by
      rw [synth_inducedForm Q D p y u hy.1 a]
      rfl
    _ = c (Λ * (g y * T * h y) - (g y * T * h y) * Λ +
          (fderiv ℝ g y u * T * h y + g y * T * fderiv ℝ h y u)) := by
      exact congrArg c (affine_adjoint_identity (g y) (h y) Λ
        (fderiv ℝ g y u) Γ T (fderiv ℝ h y u) hgh hΓ hdh)
    _ = _ := by
      rw [inducedForm_apply, synth_rankThreeGauge Q p q y hy a,
        fderiv_rankThreeGauge Q p q y u a hy hn]
      simp only [← ContinuousLinearMap.mul_def, map_sub, map_add]
      abel

/-- The usual affine gauge law for the induced rank-three connection. -/
theorem inducedForm_affine_overlap [IsManifold I 2 M]
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    inducedForm Q D p y = LocalConnectionGauge.transform
      (LocalConnectionCoordinatePullback.pullback (inducedForm Q D q)
        (chartTransition (I := I) p q))
      (rankThreeGauge Q p q) (rankThreeGaugeInv Q p q) y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro a
  let R := rankThreeGauge Q p q y
  let S := rankThreeGaugeInv Q p q y
  have hSR : S * R = 1 := (rankThreeGauge_inverse Q p q y hy).1
  have heq := inducedForm_overlap Q D p q y u a hy hn
  have hh := congrArg S heq
  change S (R (inducedForm Q D p y u a)) =
    S (inducedForm Q D q (chartTransition (I := I) p q y)
      (fderiv ℝ (chartTransition (I := I) p q) y u) (R a) +
      fderiv ℝ (rankThreeGauge Q p q) y u a) at hh
  rw [← ContinuousLinearMap.mul_apply, hSR, ContinuousLinearMap.one_apply] at hh
  rw [LocalConnectionGauge.transform_apply]
  change inducedForm Q D p y u a = S
    (inducedForm Q D q (chartTransition (I := I) p q y)
      (fderiv ℝ (chartTransition (I := I) p q) y u) (R a) +
      fderiv ℝ (rankThreeGauge Q p q) y u a)
  exact hh

/-- Curvature of the induced rank-three bundle transforms by the derived
orthogonal gauge and the actual chart derivative. -/
theorem inducedCurvature_overlap [IsManifold I 2 M]
    (p q : M) (y u v : E)
    (hy : y ∈ chartOverlap (I := I) p q)
    (hn : (2 : WithTop ℕ∞) ≤ n) :
    inducedCurvature Q D p y u v =
      rankThreeGaugeInv Q p q y *
        (inducedCurvature Q D q (chartTransition (I := I) p q y)
          (fderiv ℝ (chartTransition (I := I) p q) y u)
          (fderiv ℝ (chartTransition (I := I) p q) y v)) *
        rankThreeGauge Q p q y := by
  let φ := chartTransition (I := I) p q
  let g := rankThreeGauge Q p q
  let h := rankThreeGaugeInv Q p q
  let Γ := LocalConnectionCoordinatePullback.pullback (inducedForm Q D q) φ
  have hEq : inducedForm Q D p =ᶠ[𝓝 y]
      LocalConnectionGauge.transform Γ g h := by
    filter_upwards [(chartOverlap_isOpen (I := I) p q).mem_nhds hy] with z hz
    exact inducedForm_affine_overlap Q D p q z hz hn
  have hAt : inducedForm Q D p y =
      LocalConnectionGauge.transform Γ g h y := hEq.eq_of_nhds
  have hDeriv : fderiv ℝ (inducedForm Q D p) y =
      fderiv ℝ (LocalConnectionGauge.transform Γ g h) y := hEq.fderiv_eq
  have hCurv : inducedCurvature Q D p y u v =
      LocalConnection.curvature (LocalConnectionGauge.transform Γ g h) y u v := by
    simp only [inducedCurvature, LocalConnection.curvature_apply, hAt, hDeriv]
  rw [hCurv]
  have hq : φ y ∈ (extChartAt I q).target :=
    (extChartAt I q).map_source hy.2
  have hΓq : DifferentiableAt ℝ (inducedForm Q D q) (φ y) :=
    ((inducedForm_smooth Q D q).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := I) q).mem_nhds hq)
  have hφ : ContDiffAt ℝ 2 φ y := chartTransition_contDiffAt (I := I) p q y hy
  have hΓpull : DifferentiableAt ℝ Γ y :=
    LocalConnectionCoordinatePullback.differentiableAt_pullback
      (inducedForm Q D q) φ y hΓq hφ
  rw [LocalConnectionGauge.curvature_transform Γ g h y hΓpull
    (rankThreeGauge_contDiffAt Q p q y hy hn)
    ((rankThreeGaugeInv_contDiffAt Q p q y hy hn).differentiableAt (by norm_num))
    (rankThreeGauge_inverse_eventually Q p q y hy)
    (rankThreeGauge_inverse Q p q y hy).2 u v]
  congr 1
  congr 1
  have hCoord := congrArg (fun F => F ![u, v])
    (LocalConnectionCoordinatePullback.curvatureForm_pullback
      (inducedForm Q D q) φ y hΓq hφ)
  simpa only [LocalConnectionForms.curvatureForm_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hCoord

end
end QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
