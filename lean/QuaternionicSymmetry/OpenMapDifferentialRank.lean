import QuaternionicSymmetry.FiniteFiberDifferentialRank
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! An open smooth finite-dimensional map has a surjective derivative on
every nonempty open set. The proof uses a local maximum of derivative rank
and the inverse function theorem, with no Sard theorem premise. -/
namespace QuaternionicSymmetry.OpenMapDifferentialRank
open FiniteFiberDifferentialRank
open scoped ContDiff Topology
open Filter Function Set Module
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Constancy along a segment follows when its fixed direction is killed
by the derivative throughout a convex neighborhood. -/
lemma eq_of_fderiv_kills_direction {H : E → F} {s : Set E}
    (hs : Convex ℝ s) {a b : E} (ha : a ∈ s) (hb : b ∈ s)
    (hH : ∀ x ∈ s, DifferentiableAt ℝ H x)
    (hkill : ∀ x ∈ s, fderiv ℝ H x (b-a) = 0) : H b = H a := by
  let γ : ℝ → E := fun t => a + t • (b-a)
  have hγ (t : ℝ) : HasDerivAt γ (b-a) t := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const (b-a))
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ s := by
    have h := hs ha hb (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
    convert h using 1 <;> dsimp [γ] <;> module
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (H ∘ γ) 0 t := by
    simpa only [hkill (γ t) (hmem t ht)] using
      (hH (γ t) (hmem t ht)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have h := constant_of_has_deriv_right_zero
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    1 (by norm_num)
  simpa [γ] using h

/-- Openness excludes a proper derivative image at a point of locally
maximal rank. -/
theorem surjective_fderiv_of_locally_maximal_rank {f : E → F} {a : E}
    (hf : ContDiffAt ℝ ∞ f a)
    (hRank : ∀ᶠ x in 𝓝 a,
      finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap))
    (hOpen : ∀ U ∈ 𝓝 a, f '' U ∈ 𝓝 (f a)) :
    Function.Surjective (fderiv ℝ f a) := by
  let D := fderiv ℝ f a
  let W := LinearMap.range D.toLinearMap
  obtain ⟨L, hL⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (f := W.subtypeL) Subtype.val_injective
  obtain ⟨R, hR⟩ :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
      (f := D.rangeRestrict) (by rintro ⟨w,v,rfl⟩; exact ⟨v,rfl⟩)
  have hLDR (w : W) : L (D (R w)) = w := by
    have hr : D (R w) = w := congrArg Subtype.val (hR w)
    rw [hr]; exact hL w
  let K : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - R.comp (L.comp D)
  let φ : E → E := fun x => R (L (f x)) + K x
  have hφ : ContDiffAt ℝ ∞ φ a :=
    (R.contDiff.contDiffAt.comp a (L.contDiff.contDiffAt.comp a hf)).add K.contDiff.contDiffAt
  have hdφ : HasFDerivAt φ (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) a := by
    have h := (R.hasFDerivAt.comp a (L.hasFDerivAt.comp a
      (hf.differentiableAt (by simp)).hasFDerivAt)).add K.hasFDerivAt
    convert h using 1
    ext v
    simp [K, D]
  let ψ := hφ.localInverse hdφ (by simp)
  have hψ : ContDiffAt ℝ ∞ ψ (φ a) := hφ.to_localInverse hdφ (by simp)
  have hψa : ψ (φ a) = a := hφ.localInverse_apply_image hdφ (by simp)
  have hleft : ∀ᶠ x in 𝓝 a, ψ (φ x) = x :=
    (hφ.hasStrictFDerivAt' hdφ (by simp)).eventually_left_inverse
  have hright : ∀ᶠ z in 𝓝 (φ a), φ (ψ z) = z :=
    (hφ.hasStrictFDerivAt' hdφ (by simp)).eventually_right_inverse
  have hφL (x : E) : L (D (φ x)) = L (f x) := by
    simp only [φ, K, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_add, map_sub, hLDR]
    change L (f x) + (L (D x) - L (D x)) = L (f x)
    abel
  let H : E → F := f ∘ ψ
  have hH : ContDiffAt ℝ ∞ H (φ a) := by
    exact (hψa ▸ hf).comp (φ a) hψ
  have hLH : (fun z => L (H z)) =ᶠ[𝓝 (φ a)] (fun z => L (D z)) := by
    filter_upwards [hright] with z hz
    change L (f (ψ z)) = _
    rw [← hφL, hz]
  let A : E → W →L[ℝ] W := fun x => L.comp ((fderiv ℝ f x).comp R)
  have hAa : A a = ContinuousLinearMap.id ℝ W := by
    apply ContinuousLinearMap.ext
    intro w
    exact hLDR w
  have hDA := ((contDiffAt_infty.mp hf) 2).fderiv_right (m := 1) (by norm_num)
  have hAc : ContinuousAt A a :=
    (contDiffAt_const.clm_comp (hDA.clm_comp contDiffAt_const)).continuousAt
  have hSurj : ∀ᶠ x in 𝓝 a, Function.Surjective (L.comp (fderiv ℝ f x)) := by
    have hinj : ∀ᶠ x in 𝓝 a, Function.Injective (A x) := by
      have hn : ∀ᶠ B : W →L[ℝ] W in 𝓝 (A a), Function.Injective B := by
        apply ContinuousLinearMap.isOpen_injective.mem_nhds
        rw [hAa]; exact Function.injective_id
      exact hAc.eventually hn
    filter_upwards [hinj] with x hx
    have hax := (LinearMap.injective_iff_surjective (f := (A x).toLinearMap)).mp hx
    intro w
    obtain ⟨v, hv⟩ := hax w
    exact ⟨R v, hv⟩
  have hKer : ∀ᶠ x in 𝓝 a, LinearMap.ker (fderiv ℝ f x).toLinearMap =
      LinearMap.ker (L.comp (fderiv ℝ f x)).toLinearMap := by
    filter_upwards [hSurj, hRank] with x hs hr
    exact ker_eq_ker_comp_of_rank_le _ L hs hr
  have hDf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x := by
    filter_upwards [((contDiffAt_infty.mp hf) 1).eventually (by simp)] with x hx
    exact hx.differentiableAt (by norm_num)
  have hDψ : ∀ᶠ z in 𝓝 (φ a), DifferentiableAt ℝ ψ z := by
    filter_upwards [((contDiffAt_infty.mp hψ) 1).eventually (by simp)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hψt : Tendsto ψ (𝓝 (φ a)) (𝓝 a) := by
    have hc := hψ.continuousAt
    change Tendsto ψ (𝓝 (φ a)) (𝓝 (ψ (φ a))) at hc
    rw [hψa] at hc
    exact hc
  have hkill : ∀ᶠ z in 𝓝 (φ a), DifferentiableAt ℝ H z ∧
      ∀ v, L (D v) = 0 → fderiv ℝ H z v = 0 := by
    filter_upwards [hDψ, hψt.eventually hDf, hψt.eventually hKer,
      hLH.eventually_nhds] with z hz hfz hk hEq
    have hh : DifferentiableAt ℝ H z := hfz.comp z hz
    refine ⟨hh, ?_⟩
    intro v hv
    have hEq' : (fun z => L (H z)) =ᶠ[𝓝 z] (fun z => L (D z)) := hEq
    have heq := congrArg (fun T : E →L[ℝ] W => T v) hEq'.fderiv_eq
    have hdL : fderiv ℝ (fun z => L (H z)) z = L.comp (fderiv ℝ H z) :=
      (L.hasFDerivAt.comp z hh.hasFDerivAt).fderiv
    have hdD : fderiv ℝ (fun z => L (D z)) z = L.comp D := (L.comp D).fderiv
    rw [hdL, hdD] at heq
    change L (fderiv ℝ H z v) = L (D v) at heq
    rw [hv] at heq
    rw [fderiv_comp z hfz hz] at heq ⊢
    change fderiv ℝ ψ z v ∈ LinearMap.ker (fderiv ℝ f (ψ z)).toLinearMap
    rw [hk]
    exact heq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hkill
  have hfiber : ∀ᶠ x in 𝓝 a, L (f x) = L (f a) → f x = f a := by
    filter_upwards [hleft, hφ.continuousAt.eventually (Metric.ball_mem_nhds (φ a) hε)]
      with x hx hxb
    intro hLf
    have hD : L (D (φ x - φ a)) = 0 := by rw [map_sub, map_sub, hφL, hφL, hLf, sub_self]
    have h := eq_of_fderiv_kills_direction (convex_ball (φ a) ε)
      (Metric.mem_ball_self hε) hxb (fun z hz => (hball z hz).1)
      (fun z hz => (hball z hz).2 _ hD)
    change f (ψ (φ x)) = f (ψ (φ a)) at h
    rwa [hx, hψa] at h
  have hIso : ∀ᶠ b in 𝓝 (f a), L b = L (f a) → b = f a := by
    filter_upwards [hOpen {x | L (f x) = L (f a) → f x = f a} hfiber]
      with b hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact hx
  have hLi : Function.Injective L := by
    have h := injective_fderiv_of_locally_maximal_rank (f := (L : F → W)) (a := f a)
      L.contDiff.contDiffAt (Filter.Eventually.of_forall (fun x => by
        rw [L.fderiv, L.fderiv])) hIso
    simpa only [L.fderiv] using h
  intro b
  exact ⟨R (L b), hLi (hLDR (L b))⟩


/-- A smooth map open at all points of an open set has a regular point there. -/
theorem exists_surjective_fderiv_on {f : E → F} {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) (hf : ContDiffOn ℝ ∞ f U)
    (hOpen : ∀ a ∈ U, ∀ s ∈ 𝓝 a, f '' s ∈ 𝓝 (f a)) :
    ∃ a ∈ U, Function.Surjective (fderiv ℝ f a) := by
  let rank : E → ℕ := fun x => finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
  have hFinite : (rank '' U).Finite := (Set.finite_le_nat (finrank ℝ E)).subset (by
    rintro _ ⟨x, _, rfl⟩
    exact (fderiv ℝ f x).toLinearMap.finrank_range_le)
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ :=
    Set.exists_max_image (rank '' U) id hFinite (hne.image rank)
  refine ⟨a, ha, surjective_fderiv_of_locally_maximal_rank
    (hf a ha |>.contDiffAt (hU.mem_nhds ha)) ?_ (hOpen a ha)⟩
  filter_upwards [hU.mem_nhds ha] with x hx
  exact hmax _ ⟨x, hx, rfl⟩

end
end QuaternionicSymmetry.OpenMapDifferentialRank
