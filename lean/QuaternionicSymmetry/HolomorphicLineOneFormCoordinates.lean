import QuaternionicSymmetry.HolomorphicBundleLocalVector
import QuaternionicSymmetry.HolomorphicDeterminantLine
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Holomorphic coordinates of a genuine line-valued tangent one-form. -/
namespace QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
open HolomorphicBundleLocalVector
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)

/-- Local coordinates in an arbitrary tangent chart and line chart. -/
def localForm (i : atlas V M) (a : ι) (x : M) : V →L[ℂ] ℂ :=
  (L.coordChange (L.indexAt x) a x).comp
    ((show V →ₗ[ℂ] ℂ from θ x).toContinuousLinearMap.comp
      ((tangentBundleCore 𝓘(ℂ,V) M).coordChange i (achart V x) x))

local instance tangentTriv_mem (i : atlas V M) :
    MemTrivializationAtlas ((tangentBundleCore 𝓘(ℂ,V) M).localTriv i) := ⟨⟨i,rfl⟩⟩

theorem localForm_apply (i : atlas V M) (a : ι) (x : M) (v : V)
    (hx : x ∈ i.1.source) :
    localForm L θ i a x v =
      ((L.localTriv a) ⟨x, θ x (localVector
        ((tangentBundleCore 𝓘(ℂ,V) M).localTriv i) v x)⟩).2 := by
  rw [localVector_apply_of_mem _ _ hx, Trivialization.linearEquivAt_symm_apply,
    VectorBundleCore.localTriv_symm_apply (tangentBundleCore 𝓘(ℂ,V) M) i hx]
  rfl

/-- Holomorphic total-space evaluation implies holomorphic local
coefficients in each fixed tangent direction. -/
theorem localForm_apply_contMDiffAt
    (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) M =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
    (i : atlas V M) (a : ι) (x : M)
    (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) (v : V) :
    ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (fun y => localForm L θ i a y v) x := by
  letI : IsManifold 𝓘(ℂ,V) (∞ + 1) M := by simpa using (inferInstance : IsManifold 𝓘(ℂ,V) ∞ M)
  let T := tangentBundleCore 𝓘(ℂ,V) M
  letI : T.IsContMDiff 𝓘(ℂ,V) ∞ := tangentBundleCore.isContMDiff
  letI : MemTrivializationAtlas (T.localTriv i) := ⟨⟨i,rfl⟩⟩
  letI : MemTrivializationAtlas (L.localTriv a) := ⟨⟨a,rfl⟩⟩
  have hs := localVector_contMDiffOn 𝓘(ℂ,V) (T.localTriv i) v
  have ht := hθ.comp_contMDiffOn hs
  have ht' := (ht x hi).contMDiffAt (i.1.open_source.mem_nhds hi)
  have hc := ((L.localTriv a).contMDiffAt_section_iff ha).1 ht'
  apply hc.congr_of_eventuallyEq
  filter_upwards [i.1.open_source.mem_nhds hi] with y hy
  exact localForm_apply L θ i a y v hy

/-- A finite-dimensional family of linear functionals is holomorphic
when all fixed-vector evaluations are holomorphic. -/
theorem contMDiffAt_clm_of_apply (F : M → V →L[ℂ] ℂ) (x : M)
    (hF : ∀ v, ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,ℂ) ∞ (fun y => F y v) x) :
    ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,V →L[ℂ] ℂ) ∞ F x := by
  let b := Module.finBasis ℂ V
  have heq : F = fun y => ∑ j, F y (b j) • (b.coord j).toContinuousLinearMap := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (F y) (b.sum_repr v)
    simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap,
      Module.Basis.coord_apply, smul_eq_mul, mul_comm] using h.symm
  rw [heq]
  exact ContMDiffAt.sum (fun j _ => (hF (b j)).smul contMDiffAt_const)

theorem localForm_contMDiffAt
    (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) M =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
    (i : atlas V M) (a : ι) (x : M)
    (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) :
    ContMDiffAt 𝓘(ℂ,V) 𝓘(ℂ,V →L[ℂ] ℂ) ∞ (localForm L θ i a) x :=
  contMDiffAt_clm_of_apply _ x (localForm_apply_contMDiffAt L θ hθ i a x hi ha)

/-- The coefficient one-form in ordinary complex vector-space coordinates. -/
def coordinateForm (i : atlas V M) (a : ι) (y : V) : V →L[ℂ] ℂ :=
  localForm L θ i a (i.1.symm y)

theorem coordinateForm_contDiffAt
    (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) M =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
    (i : atlas V M) (a : ι) (x : M)
    (hi : x ∈ i.1.source) (ha : x ∈ L.baseSet a) :
    ContDiffAt ℂ ∞ (coordinateForm L θ i a) (i.1 x) := by
  have hlocal := localForm_contMDiffAt L θ hθ i a x hi ha
  have hinv := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℂ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) (i.1.map_source hi)
  exact contMDiffAt_iff_contDiffAt.mp
    (hlocal.comp_of_eq hinv (i.1.left_inv hi))

/-- The genuine tangent and line cocycles give the one-form gauge law. -/
theorem localForm_covariance (i j : atlas V M) (a b : ι) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source)
    (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    (localForm L θ j b x).comp ((tangentBundleCore 𝓘(ℂ,V) M).coordChange i j x) =
      HolomorphicLinePowers.transitionScalar L a b x • localForm L θ i a x := by
  let T := tangentBundleCore 𝓘(ℂ,V) M
  apply ContinuousLinearMap.ext
  intro v
  have ht := T.coordChange_comp i j (achart V x) x
    ⟨⟨hi,hj⟩, mem_chart_source V x⟩ v
  have hl := L.coordChange_comp (L.indexAt x) a b x
    ⟨⟨L.mem_baseSet_at x,ha⟩,hb⟩
    (θ x (T.coordChange i (achart V x) x v))
  change L.coordChange (L.indexAt x) b x
      (θ x (T.coordChange j (achart V x) x (T.coordChange i j x v))) = _
  rw [ht, ← hl, HolomorphicLinePowers.linear_apply_one]
  rfl

/-- On ordinary complex manifolds, the tangent transition is the ordinary
Fréchet derivative of the chart transition. -/
theorem tangent_coordChange_eq_fderiv (i j : atlas V M) (x : M) :
    (tangentBundleCore 𝓘(ℂ,V) M).coordChange i j x =
      fderiv ℂ (j.1 ∘ i.1.symm) (i.1 x) := by
  simp only [tangentBundleCore_coordChange, mfld_simps, fderivWithin_univ]

/-- The coordinate form obeys its gauge law on a genuine open neighborhood. -/
theorem coordinateForm_covariance_eventually (i j : atlas V M) (a b : ι) (x : M)
    (hi : x ∈ i.1.source) (hj : x ∈ j.1.source)
    (ha : x ∈ L.baseSet a) (hb : x ∈ L.baseSet b) :
    (fun y => (coordinateForm L θ j b (j.1 (i.1.symm y))).comp
      (fderiv ℂ (j.1 ∘ i.1.symm) y)) =ᶠ[𝓝 (i.1 x)]
    (fun y => HolomorphicLinePowers.transitionScalar L a b (i.1.symm y) •
      coordinateForm L θ i a y) := by
  have hc := i.1.continuousAt_symm (i.1.map_source hi)
  have hj' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ j.1.source :=
    hc.eventually (by simpa [i.1.left_inv hi] using j.1.open_source.mem_nhds hj)
  have ha' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ L.baseSet a :=
    hc.eventually (by simpa [i.1.left_inv hi] using (L.isOpen_baseSet a).mem_nhds ha)
  have hb' : ∀ᶠ y in 𝓝 (i.1 x), i.1.symm y ∈ L.baseSet b :=
    hc.eventually (by simpa [i.1.left_inv hi] using (L.isOpen_baseSet b).mem_nhds hb)
  filter_upwards [i.1.open_target.mem_nhds (i.1.map_source hi), hj', ha', hb']
    with y hy hyj hya hyb
  have h := localForm_covariance L θ i j a b (i.1.symm y)
    (i.1.map_target hy) hyj hya hyb
  rw [tangent_coordChange_eq_fderiv, i.1.right_inv hy] at h
  simpa only [coordinateForm, j.1.left_inv hyj] using h

/-- The inverse chart derivative is exactly the tangent-core change from
the fixed chart to the preferred tangent coordinates. -/
theorem mfderiv_chart_symm_eq_coordChange (i : atlas V M) (y : V)
    (hy : y ∈ i.1.target) :
    mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) i.1.symm y =
      (tangentBundleCore 𝓘(ℂ,V) M).coordChange i (achart V (i.1.symm y)) (i.1.symm y) := by
  have hs := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℂ,V)) (n := ∞) (IsManifold.subset_maximalAtlas i.2) hy
  rw [(hs.mdifferentiableAt (by simp)).mfderiv, tangent_coordChange_eq_fderiv]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, i.1.right_inv hy]

end
end QuaternionicSymmetry.HolomorphicLineOneFormCoordinates
