import QuaternionicSymmetry.HolomorphicVectorFieldLocalFlow
import QuaternionicSymmetry.CompactVectorFieldFlow
import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphisms

/-! Complete holomorphic vector fields on compact complex manifolds give
continuous one-parameter subgroups of the actual full biholomorphism group. -/
namespace QuaternionicSymmetry.CompactHolomorphicVectorFieldFlow
open Set Filter Function HolomorphicVectorFieldRealSmooth GeneralHolomorphicFullAutomorphisms
open GeneralHolomorphicDistributionAutomorphisms GeneralHolomorphicDistributionAutomorphismTopology
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [CompactSpace M] [T2Space M] [Nonempty M]
  (X : ContMDiffSection 𝓘(ℂ,E) E ∞ (TangentSpace 𝓘(ℂ,E) : M → Type _))

def realC1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
    (fun x => (⟨x,X x⟩ : TangentBundle 𝓘(ℝ,E) M)) := (real_smooth X).of_le (by simp)

def flow (x : M) (t : ℝ) : M := CompactVectorFieldFlow.flow X (realC1 X) x t

@[simp] theorem flow_zero (x : M) : flow X x 0 = x := CompactVectorFieldFlow.flow_zero X (realC1 X) x

theorem flow_add (x : M) (s t : ℝ) : flow X x (s+t) = flow X (flow X x t) s :=
  CompactVectorFieldFlow.flow_add X (realC1 X) x s t

theorem integral (x : M) : IsMIntegralCurve (I := 𝓘(ℝ,E)) (flow X x) X :=
  CompactVectorFieldFlow.integral X (realC1 X) x

theorem continuous_flow : Continuous (fun p : M × ℝ => flow X p.1 p.2) :=
  CompactVectorFieldFlow.continuous_flow X (realC1 X)

theorem exists_uniform_holomorphic :
    ∃ δ > (0 : ℝ), ∀ t : ℝ, |t| < δ → ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (fun x => flow X x t) := by
  classical
  choose U hU hmem ε hε β hcont hhol hβ using fun x : M => HolomorphicVectorFieldLocalFlow.local_flow X x
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU (fun y _ => mem_iUnion.mpr ⟨y,hmem y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y,hy,_⟩ := mem_iUnion₂.mp (hs (mem_univ (Classical.choice ‹Nonempty M›)))
    exact ⟨y,hy⟩
  let δ := s.inf' hsne ε
  have hδ : 0 < δ := (Finset.lt_inf'_iff hsne).mpr (fun y _ => hε y)
  refine ⟨δ,hδ,?_⟩
  intro t ht x
  obtain ⟨z,hz,hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hδε : δ ≤ ε z := Finset.inf'_le ε hz
  have htz : t ∈ Ioo (-(ε z)) (ε z) := abs_lt.mp (lt_of_lt_of_le ht hδε)
  apply ((hhol z t htz x hx).contMDiffAt ((hU z).mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [(hU z).mem_nhds hx] with y hy
  exact CompactVectorFieldFlow.eq_local X (realC1 X) (U z) (ε z) (hε z) (β z) (hβ z) y hy t htz

theorem flow_holomorphic (t : ℝ) : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (fun x => flow X x t) := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_uniform_holomorphic X
  obtain ⟨n,hn⟩ := exists_nat_gt (|t|/δ)
  let N : ℕ := n+1
  have hN : (0 : ℝ) < (N : ℝ) := by dsimp [N]; positivity
  let d := t/(N : ℝ)
  have hd : |d| < δ := by
    dsimp only [d]
    rw [abs_div,abs_of_pos hN,div_lt_iff₀ hN]
    have hh : |t| < (n : ℝ)*δ := (div_lt_iff₀ hδ).mp hn
    have hNn : (n : ℝ) < (N : ℝ) := by dsimp [N]; push_cast; linarith
    nlinarith
  have hi (k : ℕ) (x : M) : (fun x => flow X x d)^[k] x = flow X x ((k : ℝ)*d) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,← flow_add]
      congr 1
      push_cast
      ring
  have hcN := (hlocal d hd).iterate N
  convert hcN using 1
  funext x
  rw [hi]
  congr 1
  dsimp only [d]
  field_simp [ne_of_gt hN]

/-- Actual smooth biholomorphisms, with negative time as their inverse. -/
def automorphism (t : ℝ) : HolomorphicAutomorphisms E M := by
  let f : Diffeomorph 𝓘(ℂ,E) 𝓘(ℂ,E) M M ∞ := {
    toEquiv := (CompactVectorFieldFlow.homeomorph X (realC1 X) t).toEquiv
    contMDiff_toFun := flow_holomorphic X t
    contMDiff_invFun := flow_holomorphic X (-t) }
  exact ⟨f,by constructor <;> intro x v hv <;> trivial⟩

def hom : Multiplicative ℝ →* HolomorphicAutomorphisms E M where
  toFun t := automorphism X t.toAdd
  map_one' := by
    apply Subtype.ext
    apply Diffeomorph.ext
    intro x
    exact flow_zero X x
  map_mul' s t := by
    apply Subtype.ext
    apply Diffeomorph.ext
    intro x
    exact flow_add X x s.toAdd t.toAdd

theorem hom_continuous : Continuous (hom X) := by
  apply continuous_representation_of_action (fullDistribution (V := E) (Z := M)) (hom X)
  exact (continuous_flow X).comp (continuous_snd.prodMk continuous_fst)

end
end QuaternionicSymmetry.CompactHolomorphicVectorFieldFlow
