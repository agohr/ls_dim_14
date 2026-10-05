import QuaternionicSymmetry.CompactVectorFieldCompleteness

/-! The complete integral curves of a continuously differentiable vector field
on a compact manifold form a continuous global flow. -/
namespace QuaternionicSymmetry.CompactVectorFieldFlow
open CompactVectorFieldCompleteness Set Filter Function
open scoped Manifold ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [CompactSpace M] [T2Space M]
variable (v : (x : M) → TangentSpace 𝓘(ℝ,E) x)
  (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
    (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))

def flow (x : M) : ℝ → M := Classical.choose (exists_global v hv x)

@[simp] theorem flow_zero (x : M) : flow v hv x 0 = x :=
  (Classical.choose_spec (exists_global v hv x)).1

theorem integral (x : M) : IsMIntegralCurve (flow v hv x) v :=
  (Classical.choose_spec (exists_global v hv x)).2

theorem flow_add (x : M) (s t : ℝ) :
    flow v hv x (s + t) = flow v hv (flow v hv x t) s := by
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv
    ((integral v hv x).comp_add t) (integral v hv (flow v hv x t))
    (t₀ := 0) (by simp)
  exact congrFun he s

theorem eq_local (U : Set M) (ε : ℝ) (hε : 0 < ε) (β : M × ℝ → M)
    (hβ : ∀ x ∈ U, β (x,0) = x ∧
      IsMIntegralCurveOn (fun t => β (x,t)) v (Ioo (-ε) ε))
    (x : M) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
    flow v hv x t = β (x,t) := by
  have he := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (by constructor <;> linarith) hv
    ((integral v hv x).isMIntegralCurveOn (Ioo (-ε) ε)) (hβ x hx).2
    (by rw [flow_zero, (hβ x hx).1])
  exact he ht

theorem exists_uniform_continuousAt [Nonempty M] :
    ∃ δ > (0 : ℝ), ∀ x : M, ∀ t : ℝ, |t| < δ →
      ContinuousAt (fun p : M × ℝ => flow v hv p.1 p.2) (x,t) := by
  classical
  choose U hU hmem ε hε β hcont hβ using fun x : M => local_manifold_flow v x (hv x)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun y _ => mem_iUnion.mpr ⟨y,hmem y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hs (mem_univ (Classical.choice ‹Nonempty M›)))
    exact ⟨y,hy⟩
  let δ := s.inf' hsne ε
  have hδ : (0 : ℝ) < δ := (Finset.lt_inf'_iff hsne).mpr (fun y _ => hε y)
  refine ⟨δ,hδ,?_⟩
  intro x t ht
  obtain ⟨z,hz,hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hδε : δ ≤ ε z := Finset.inf'_le ε hz
  have htz : t ∈ Ioo (-(ε z)) (ε z) := abs_lt.mp (lt_of_lt_of_le ht hδε)
  have hdom : U z ×ˢ Ioo (-(ε z)) (ε z) ∈ 𝓝 (x,t) :=
    (hU z |>.prod isOpen_Ioo).mem_nhds ⟨hx,htz⟩
  have hc : ContinuousAt (β z) (x,t) := (hcont z).continuousAt hdom
  apply hc.congr_of_eventuallyEq
  filter_upwards [hdom] with p hp
  exact eq_local v hv (U z) (ε z) (hε z) (β z) (hβ z) p.1 hp.1 p.2 hp.2

theorem continuous_time [Nonempty M] (t : ℝ) : Continuous (fun x => flow v hv x t) := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_uniform_continuousAt v hv
  obtain ⟨n,hn⟩ := exists_nat_gt (|t| / δ)
  let N : ℕ := n + 1
  have hN : (0 : ℝ) < (N : ℝ) := by dsimp [N]; positivity
  let d := t / (N : ℝ)
  have hd : |d| < δ := by
    dsimp only [d]
    rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN]
    have hh : |t| < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
    have hNn : (n : ℝ) < (N : ℝ) := by dsimp [N]; push_cast; linarith
    nlinarith
  have hc : Continuous (fun x => flow v hv x d) := continuous_iff_continuousAt.mpr fun x =>
    (hlocal x d hd).comp (f := fun y : M => (y,d)) (x := x)
      (continuousAt_id.prodMk continuousAt_const)
  have hi (k : ℕ) (x : M) : (fun x => flow v hv x d)^[k] x =
      flow v hv x ((k : ℝ) * d) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← flow_add]
      congr 1
      push_cast
      ring
  have hcN := hc.iterate N
  convert hcN using 1
  funext x
  rw [hi]
  congr 1
  dsimp only [d]
  field_simp [ne_of_gt hN]

theorem continuous_flow [Nonempty M] :
    Continuous (fun p : M × ℝ => flow v hv p.1 p.2) := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_uniform_continuousAt v hv
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x,t⟩
  have hc : ContinuousAt (fun p : M × ℝ => (flow v hv p.1 t,p.2-t)) (x,t) :=
    ((continuous_time v hv t).continuousAt.comp continuousAt_fst).prodMk
      (continuousAt_snd.sub continuousAt_const)
  have ho := hlocal (flow v hv x t) 0 (by simpa using hδ)
  have ho' : ContinuousAt (fun p : M × ℝ => flow v hv p.1 p.2)
      (flow v hv x t,t-t) := by simpa using ho
  have he := ho'.comp (f := fun p : M × ℝ => (flow v hv p.1 t,p.2-t)) (x := (x,t)) hc
  change ContinuousAt (fun p : M × ℝ => flow v hv (flow v hv p.1 t) (p.2-t)) (x,t) at he
  simpa only [← flow_add, sub_add_cancel] using he

/-- Each time map is a genuine homeomorphism with the negative-time inverse. -/
def homeomorph [Nonempty M] (t : ℝ) : M ≃ₜ M where
  toFun := fun x => flow v hv x t
  invFun := fun x => flow v hv x (-t)
  left_inv x := by
    change flow v hv (flow v hv x t) (-t) = x
    rw [← flow_add, neg_add_cancel, flow_zero]
  right_inv x := by
    change flow v hv (flow v hv x (-t)) t = x
    rw [← flow_add, add_neg_cancel, flow_zero]
  continuous_toFun := continuous_time v hv t
  continuous_invFun := continuous_time v hv (-t)

end
end QuaternionicSymmetry.CompactVectorFieldFlow
