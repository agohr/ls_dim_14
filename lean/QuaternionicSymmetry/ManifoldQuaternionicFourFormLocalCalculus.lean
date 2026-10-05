import QuaternionicSymmetry.ManifoldQuaternionicFourFormConnection

/-! Local solder expression for the quaternionic Kähler forms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus

open QuaternionicSymmetry.ManifoldQuaternionicMetric
  QuaternionicSymmetry.ManifoldQuaternionicConnection
  QuaternionicSymmetry.ManifoldQuaternionicFourForm
  QuaternionicSymmetry.ManifoldQuaternionicFourFormTransitions
  VectorBundleFrameTransitions
open scoped Manifold Topology ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem generator_skew (S : QuaternionicStructure E) (t : Fin 3)
    (v w : E) :
    inner ℝ (quaternionicGenerator S t v) w =
      -inner ℝ v (quaternionicGenerator S t w) := by
  fin_cases t
  · exact S.I_skew v w
  · exact S.J_skew v w
  · exact S.K_skew v w

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem frameKahler_apply (S : QuaternionicStructure E) (t : Fin 3)
    (v : Fin 2 → E) :
    ((1 / 2 : ℝ) • LocalConnectionForms.alternatingPart
      ((innerSL ℝ).comp (quaternionicGenerator S t))) v =
        inner ℝ (quaternionicGenerator S t (v 0)) (v 1) := by
  simp only [ContinuousAlternatingMap.smul_apply,
    LocalConnectionForms.alternatingPart_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [generator_skew S t (v 1) (v 0), real_inner_comm (v 1)
    (quaternionicGenerator S t (v 0))]
  ring

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartKahler_solder (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (v : Fin 2 → E) :
    chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm y) t v =
      inner ℝ
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t
          (solder Q p y (v 0)))
        (solder Q p y (v 1)) := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hx : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    change x ∈ (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p)
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy
  rw [chartKahler_eq_frameKahler Q (achart E p) x hx t]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [solder_eq_toFrame Q p y hy]
  exact frameKahler_apply (Q.reduction.Q (achart E p)) t
    (fun k => Q.frames.toFrame (achart E p) x (v k))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem fderiv_kahler_pair (K : E →L[ℝ] E)
    (θ : E → E →L[ℝ] E) (x u v w : E)
    (hθ : DifferentiableAt ℝ θ x) :
    fderiv ℝ (fun z => inner ℝ (K (θ z v)) (θ z w)) x u =
      inner ℝ (K (fderiv ℝ θ x u v)) (θ x w) +
        inner ℝ (K (θ x v)) (fderiv ℝ θ x u w) := by
  have hv : DifferentiableAt ℝ (fun z => θ z v) x :=
    hθ.clm_apply (differentiableAt_const _)
  have hw : DifferentiableAt ℝ (fun z => θ z w) x :=
    hθ.clm_apply (differentiableAt_const _)
  have hKv : DifferentiableAt ℝ (fun z => K (θ z v)) x :=
    K.differentiableAt.comp x hv
  rw [fderiv_inner_apply ℝ hKv hw u]
  rw [QuaternionicSymmetry.LocalConnectionBianchi.fderiv_eval_const hθ w u]
  have hcomp := fderiv_comp x K.differentiableAt hv
  change fderiv ℝ (fun z => K (θ z v)) x =
    (fderiv ℝ K (θ x v)).comp (fderiv ℝ (fun z => θ z v) x) at hcomp
  rw [hcomp, K.fderiv]
  simp only [ContinuousLinearMap.comp_apply,
    QuaternionicSymmetry.LocalConnectionBianchi.fderiv_eval_const hθ v u]
  abel

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem differentiableAt_solder (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    DifferentiableAt ℝ (solder Q p) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hx : x ∈ (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy
  have hframe : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (Q.frames.toFrame (achart E p)) x :=
    (Q.frames.smooth_to (achart E p) x hx).contMDiffAt
      (((tangentBundleCore 𝓘(ℝ, E) M).isOpen_baseSet _).mem_nhds hx)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (extChartAt 𝓘(ℝ, E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have hcomp : DifferentiableAt ℝ
      (fun z => Q.frames.toFrame (achart E p)
        ((extChartAt 𝓘(ℝ, E) p).symm z)) y :=
    (hframe.comp y hsymm).contDiffAt.differentiableAt (by norm_num)
  have hevent : solder Q p =ᶠ[𝓝 y]
      (fun z => Q.frames.toFrame (achart E p)
        ((extChartAt 𝓘(ℝ, E) p).symm z)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy]
      with z hz
    exact solder_eq_toFrame Q p z hz
  exact hcomp.congr_of_eventuallyEq hevent

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem fderiv_chartKahler_eval (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (u v w : E) :
    fderiv ℝ (fun z =>
      chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm z) t ![v, w]) y u =
      inner ℝ
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t
          (fderiv ℝ (solder Q p) y u v))
        (solder Q p y w) +
      inner ℝ
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t
          (solder Q p y v))
        (fderiv ℝ (solder Q p) y u w) := by
  have hevent : (fun z =>
        chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm z) t ![v, w])
      =ᶠ[𝓝 y] (fun z =>
        inner ℝ (quaternionicGenerator (Q.reduction.Q (achart E p)) t
          (solder Q p z v)) (solder Q p z w)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy]
      with z hz
    exact chartKahler_solder Q p z hz t ![v, w]
  rw [hevent.fderiv_eq]
  exact fderiv_kahler_pair
    (quaternionicGenerator (Q.reduction.Q (achart E p)) t)
    (solder Q p) y u v w (differentiableAt_solder Q p y hy)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem differentiableAt_chartKahler (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (t : Fin 3) :
    DifferentiableAt ℝ (fun z =>
      chartKahler Q (achart E p) ((extChartAt 𝓘(ℝ, E) p).symm z) t) y := by
  let x := (extChartAt 𝓘(ℝ, E) p).symm y
  have hx : x ∈ (tangentBundleCore 𝓘(ℝ, E) M).baseSet (achart E p) := by
    simpa only [tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, E)] using
      (extChartAt 𝓘(ℝ, E) p).map_target hy
  have hform : ContMDiffAt 𝓘(ℝ, E)
      𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞ (chartKahler Q (achart E p) · t) x :=
    (chartKahler_smooth Q (achart E p) t x hx).contMDiffAt
      (((tangentBundleCore 𝓘(ℝ, E) M).isOpen_baseSet _).mem_nhds hx)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (extChartAt 𝓘(ℝ, E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := ∞) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  exact (hform.comp y hsymm).contDiffAt.differentiableAt (by norm_num)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem extDeriv_chartKahler_solder (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (u v w : E) :
    extDeriv
      (fun z => chartKahler Q (achart E p)
        ((extChartAt 𝓘(ℝ, E) p).symm z) t) y ![u, v, w] =
      inner ℝ (quaternionicGenerator (Q.reduction.Q (achart E p)) t
        (fderiv ℝ (solder Q p) y u v -
          fderiv ℝ (solder Q p) y v u)) (solder Q p y w) +
      inner ℝ (quaternionicGenerator (Q.reduction.Q (achart E p)) t
        (fderiv ℝ (solder Q p) y v w -
          fderiv ℝ (solder Q p) y w v)) (solder Q p y u) +
      inner ℝ (quaternionicGenerator (Q.reduction.Q (achart E p)) t
        (fderiv ℝ (solder Q p) y w u -
          fderiv ℝ (solder Q p) y u w)) (solder Q p y v) := by
  let K := quaternionicGenerator (Q.reduction.Q (achart E p)) t
  let θ := solder Q p y
  let dθ := fderiv ℝ (solder Q p) y
  rw [extDeriv_apply
    (differentiableAt_chartKahler Q p y hy t)]
  rw [Fin.sum_univ_three]
  have h0 : (0 : Fin 3).removeNth ![u, v, w] = ![v, w] := by
    ext k
    fin_cases k <;> rfl
  have h1 : (1 : Fin 3).removeNth ![u, v, w] = ![u, w] := by
    ext k
    fin_cases k <;> rfl
  have h2 : (2 : Fin 3).removeNth ![u, v, w] = ![u, v] := by
    ext k
    fin_cases k <;> rfl
  simp only [h0, h1, h2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num only [Matrix.vecHead, Matrix.vecTail]
  simp only [Function.comp_apply]
  have hwvec : ![v, w] (Fin.succ 0) = w := rfl
  rw [hwvec]
  rw [fderiv_chartKahler_eval Q p y hy t u v w,
    fderiv_chartKahler_eval Q p y hy t v u w,
    fderiv_chartKahler_eval Q p y hy t w u v]
  have hskew (a b : E) : inner ℝ (K a) b = -inner ℝ (K b) a := by
    rw [generator_skew (Q.reduction.Q (achart E p)) t a b,
      real_inner_comm a (K b)]
  norm_num
  rw [hskew (θ v) (dθ u w), hskew (θ u) (dθ v w),
    hskew (θ u) (dθ w v)]
  simp only [inner_sub_left]
  abel

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem commutator_pair (K Γ : E →L[ℝ] E)
    (hK : ∀ a b, inner ℝ (K a) b = -inner ℝ (K b) a)
    (hΓ : ∀ a b, inner ℝ (Γ a) b = -inner ℝ a (Γ b))
    (b c : E) :
    -inner ℝ (K (Γ b)) c + inner ℝ (K (Γ c)) b =
      inner ℝ ((Γ.comp K - K.comp Γ) b) c := by
  rw [hK (Γ c) b]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left]
  rw [hΓ (K b) c]
  abel

omit [Nontrivial E] [FiniteDimensional ℝ E] in
private theorem cyclic_torsion_commutator (K Γu Γv Γw : E →L[ℝ] E)
    (hK : ∀ a b, inner ℝ (K a) b = -inner ℝ (K b) a)
    (hΓu : ∀ a b, inner ℝ (Γu a) b = -inner ℝ a (Γu b))
    (hΓv : ∀ a b, inner ℝ (Γv a) b = -inner ℝ a (Γv b))
    (hΓw : ∀ a b, inner ℝ (Γw a) b = -inner ℝ a (Γw b))
    (a b c : E) :
    inner ℝ (K (-Γu b + Γv a)) c +
      inner ℝ (K (-Γv c + Γw b)) a +
      inner ℝ (K (-Γw a + Γu c)) b =
    inner ℝ ((Γu.comp K - K.comp Γu) b) c +
      inner ℝ ((Γv.comp K - K.comp Γv) c) a +
      inner ℝ ((Γw.comp K - K.comp Γw) a) b := by
  simp only [map_add, map_neg, inner_add_left, inner_neg_left]
  have hu := commutator_pair K Γu hK hΓu b c
  have hv := commutator_pair K Γv hK hΓv c a
  have hw := commutator_pair K Γw hK hΓw a b
  linear_combination hu + hv + hw

variable (D : CompatibleTangentConnection Q)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem extDeriv_chartKahler_commutator (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (u v w : E) :
    extDeriv (fun z => chartKahler Q (achart E p)
      ((extChartAt 𝓘(ℝ, E) p).symm z) t) y ![u, v, w] =
      inner ℝ (((D.form p y u).comp
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t) -
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t).comp
          (D.form p y u)) (solder Q p y v)) (solder Q p y w) +
      inner ℝ (((D.form p y v).comp
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t) -
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t).comp
          (D.form p y v)) (solder Q p y w)) (solder Q p y u) +
      inner ℝ (((D.form p y w).comp
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t) -
        (quaternionicGenerator (Q.reduction.Q (achart E p)) t).comp
          (D.form p y w)) (solder Q p y u)) (solder Q p y v) := by
  let K := quaternionicGenerator (Q.reduction.Q (achart E p)) t
  let θ := solder Q p y
  let dθ := fderiv ℝ (solder Q p) y
  let Γu := D.form p y u
  let Γv := D.form p y v
  let Γw := D.form p y w
  have htu : dθ u v - dθ v u = -Γu (θ v) + Γv (θ u) := by
    have h := D.torsion p y u v hy
    dsimp [dθ, θ, Γu, Γv] at h ⊢
    have hh : ((fderiv ℝ (solder Q p) y) u) v -
        ((fderiv ℝ (solder Q p) y) v) u +
        (((D.form p y) u) ((solder Q p y) v) -
          ((D.form p y) v) ((solder Q p y) u)) = 0 := by
      simpa only [sub_eq_add_neg, add_assoc] using h
    calc
      _ = -((((D.form p y) u) ((solder Q p y) v) -
        ((D.form p y) v) ((solder Q p y) u))) :=
          eq_neg_of_add_eq_zero_left hh
      _ = _ := by abel
  have htv : dθ v w - dθ w v = -Γv (θ w) + Γw (θ v) := by
    have h := D.torsion p y v w hy
    dsimp [dθ, θ, Γv, Γw] at h ⊢
    have hh : ((fderiv ℝ (solder Q p) y) v) w -
        ((fderiv ℝ (solder Q p) y) w) v +
        (((D.form p y) v) ((solder Q p y) w) -
          ((D.form p y) w) ((solder Q p y) v)) = 0 := by
      simpa only [sub_eq_add_neg, add_assoc] using h
    calc
      _ = -((((D.form p y) v) ((solder Q p y) w) -
        ((D.form p y) w) ((solder Q p y) v))) :=
          eq_neg_of_add_eq_zero_left hh
      _ = _ := by abel
  have htw : dθ w u - dθ u w = -Γw (θ u) + Γu (θ w) := by
    have h := D.torsion p y w u hy
    dsimp [dθ, θ, Γw, Γu] at h ⊢
    have hh : ((fderiv ℝ (solder Q p) y) w) u -
        ((fderiv ℝ (solder Q p) y) u) w +
        (((D.form p y) w) ((solder Q p y) u) -
          ((D.form p y) u) ((solder Q p y) w)) = 0 := by
      simpa only [sub_eq_add_neg, add_assoc] using h
    calc
      _ = -((((D.form p y) w) ((solder Q p y) u) -
        ((D.form p y) u) ((solder Q p y) w))) :=
          eq_neg_of_add_eq_zero_left hh
      _ = _ := by abel
  rw [extDeriv_chartKahler_solder Q p y hy t u v w]
  change inner ℝ (K (dθ u v - dθ v u)) (θ w) +
      inner ℝ (K (dθ v w - dθ w v)) (θ u) +
      inner ℝ (K (dθ w u - dθ u w)) (θ v) = _
  rw [htu, htv, htw]
  have hK (a b : E) : inner ℝ (K a) b = -inner ℝ (K b) a := by
    rw [generator_skew (Q.reduction.Q (achart E p)) t a b,
      real_inner_comm a (K b)]
  have hΓu (a b : E) : inner ℝ (Γu a) b = -inner ℝ a (Γu b) := by
    have h := D.metric p y u a b hy
    dsimp [Γu] at h ⊢
    linarith
  have hΓv (a b : E) : inner ℝ (Γv a) b = -inner ℝ a (Γv b) := by
    have h := D.metric p y v a b hy
    dsimp [Γv] at h ⊢
    linarith
  have hΓw (a b : E) : inner ℝ (Γw a) b = -inner ℝ a (Γw b) := by
    have h := D.metric p y w a b hy
    dsimp [Γw] at h ⊢
    linarith
  exact cyclic_torsion_commutator K Γu Γv Γw hK hΓu hΓv hΓw
    (θ u) (θ v) (θ w)

theorem commutator_pair_inducedMatrix (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (a b : E) :
    inner ℝ (((D.form p y u).comp
      (quaternionicGenerator (Q.reduction.Q (achart E p)) t) -
      (quaternionicGenerator (Q.reduction.Q (achart E p)) t).comp
        (D.form p y u)) a) b =
      ∑ s : Fin 3,
        ManifoldQuaternionicFourFormConnection.inducedMatrix Q D p y u s t *
          inner ℝ (quaternionicGenerator (Q.reduction.Q (achart E p)) s a) b := by
  have hs := ManifoldQuaternionicAdjointConnection.synth_inducedForm
    Q D p y u hy (Pi.basisFun ℝ (Fin 3) t)
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_apply] at hs
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_basis] at hs
  have h := congrArg (fun T : E →L[ℝ] E => inner ℝ (T a) b) hs
  simp only [ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, sum_inner, real_inner_smul_left] at h
  simpa only [ManifoldQuaternionicFourFormConnection.inducedMatrix] using h.symm

theorem extDeriv_chartKahler_induced (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (t : Fin 3) (u v w : E) :
    extDeriv (fun z => chartKahler Q (achart E p)
      ((extChartAt 𝓘(ℝ, E) p).symm z) t) y ![u, v, w] =
      (∑ s : Fin 3,
        ManifoldQuaternionicFourFormConnection.inducedMatrix Q D p y u s t *
          chartKahler Q (achart E p)
            ((extChartAt 𝓘(ℝ, E) p).symm y) s ![v, w]) +
      (∑ s : Fin 3,
        ManifoldQuaternionicFourFormConnection.inducedMatrix Q D p y v s t *
          chartKahler Q (achart E p)
            ((extChartAt 𝓘(ℝ, E) p).symm y) s ![w, u]) +
      (∑ s : Fin 3,
        ManifoldQuaternionicFourFormConnection.inducedMatrix Q D p y w s t *
          chartKahler Q (achart E p)
            ((extChartAt 𝓘(ℝ, E) p).symm y) s ![u, v]) := by
  rw [extDeriv_chartKahler_commutator Q D p y hy t u v w]
  rw [commutator_pair_inducedMatrix Q D p y u hy t
      (solder Q p y v) (solder Q p y w),
    commutator_pair_inducedMatrix Q D p y v hy t
      (solder Q p y w) (solder Q p y u),
    commutator_pair_inducedMatrix Q D p y w hy t
      (solder Q p y u) (solder Q p y v)]
  simp_rw [chartKahler_solder Q p y hy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
