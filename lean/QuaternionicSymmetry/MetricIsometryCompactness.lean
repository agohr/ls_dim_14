import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.CompactOpen

/-! A compactness foundation for isometries of an actual compact metric
space. We first treat distance-preserving continuous self-maps in the
uniform topology; inverse-pair compactness then gives the isometry group. -/
namespace QuaternionicSymmetry.MetricIsometryCompactness
open Set
open scoped BoundedContinuousFunction
noncomputable section

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- On compact source, bounded continuous maps with the sup metric and
ordinary continuous maps with compact-open topology agree. -/
def boundedContinuousEquivContinuous : (X →ᵇ X) ≃ C(X, X) where
  toFun := BoundedContinuousFunction.toContinuousMap
  invFun := BoundedContinuousFunction.mkOfCompact
  left_inv := by
    intro f
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  right_inv := by
    intro f
    ext x
    rfl

theorem boundedContinuous_isInducing_toContinuousMap :
    Topology.IsInducing
      (BoundedContinuousFunction.toContinuousMap : (X →ᵇ X) → C(X, X)) := by
  apply ContinuousMap.isUniformEmbedding_uniformFunOfFun.isInducing.of_comp_iff.mp
  simpa only [Function.comp_def] using
    (BoundedContinuousFunction.isInducing_coeFn (α := X) (β := X))

def boundedContinuousHomeomorphContinuous : (X →ᵇ X) ≃ₜ C(X, X) :=
  (boundedContinuousEquivContinuous (X := X)).toHomeomorphOfIsInducing
    boundedContinuous_isInducing_toContinuousMap

def isometricSelfMaps : Set (X →ᵇ X) :=
  {f | ∀ x y, dist (f x) (f y) = dist x y}

omit [CompactSpace X] in
theorem isometricSelfMaps_isClosed : IsClosed (isometricSelfMaps (X := X)) := by
  have hxy (x y : X) : IsClosed
      {f : X →ᵇ X | dist (f x) (f y) = dist x y} := by
    have hx : Continuous (fun f : X →ᵇ X => f x) :=
      ContinuousEvalConst.continuous_eval_const x
    have hy : Continuous (fun f : X →ᵇ X => f y) :=
      ContinuousEvalConst.continuous_eval_const y
    exact isClosed_eq (continuous_dist.comp (hx.prodMk hy)) continuous_const
  have hset : isometricSelfMaps (X := X) =
      ⋂ x, ⋂ y, {f : X →ᵇ X | dist (f x) (f y) = dist x y} := by
    ext f
    simp only [isometricSelfMaps, mem_setOf_eq, mem_iInter]
  rw [hset]
  exact isClosed_iInter fun x => isClosed_iInter fun y => hxy x y

omit [CompactSpace X] in
theorem isometricSelfMaps_equicontinuous :
    Equicontinuous ((↑) : isometricSelfMaps (X := X) → X → X) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy f
  rw [f.2 x y]
  simpa only [dist_comm] using hy

theorem isometricSelfMaps_isCompact :
    IsCompact (isometricSelfMaps (X := X)) :=
  BoundedContinuousFunction.arzela_ascoli₁ _
    isometricSelfMaps_isClosed isometricSelfMaps_equicontinuous

/-- A pair of distance-preserving maps which are mutual inverses. This
representation keeps the inverse continuous in the uniform topology. -/
def inverseIsometricPairs : Set ((X →ᵇ X) × (X →ᵇ X)) :=
  {p | p.1 ∈ isometricSelfMaps ∧ p.2 ∈ isometricSelfMaps ∧
    (∀ x, p.1 (p.2 x) = x) ∧ (∀ x, p.2 (p.1 x) = x)}

omit [CompactSpace X] in
theorem inverseIsometricPairs_isClosed :
    IsClosed (inverseIsometricPairs (X := X)) := by
  let L := isometricSelfMaps (X := X)
  have hleft : IsClosed {p : (X →ᵇ X) × (X →ᵇ X) | p.1 ∈ L} :=
    isometricSelfMaps_isClosed.preimage continuous_fst
  have hright : IsClosed {p : (X →ᵇ X) × (X →ᵇ X) | p.2 ∈ L} :=
    isometricSelfMaps_isClosed.preimage continuous_snd
  have hinvleft (x : X) : IsClosed
      {p : (X →ᵇ X) × (X →ᵇ X) | p.1 (p.2 x) = x} := by
    have harg : Continuous (fun p : (X →ᵇ X) × (X →ᵇ X) => p.2 x) :=
      (ContinuousEvalConst.continuous_eval_const x).comp continuous_snd
    have hcomp : Continuous (fun p : (X →ᵇ X) × (X →ᵇ X) => p.1 (p.2 x)) :=
      ContinuousEval.continuous_eval.comp (continuous_fst.prodMk harg)
    exact isClosed_eq hcomp continuous_const
  have hinvright (x : X) : IsClosed
      {p : (X →ᵇ X) × (X →ᵇ X) | p.2 (p.1 x) = x} := by
    have harg : Continuous (fun p : (X →ᵇ X) × (X →ᵇ X) => p.1 x) :=
      (ContinuousEvalConst.continuous_eval_const x).comp continuous_fst
    have hcomp : Continuous (fun p : (X →ᵇ X) × (X →ᵇ X) => p.2 (p.1 x)) :=
      ContinuousEval.continuous_eval.comp (continuous_snd.prodMk harg)
    exact isClosed_eq hcomp continuous_const
  have hset : inverseIsometricPairs (X := X) =
      {p : (X →ᵇ X) × (X →ᵇ X) | p.1 ∈ L} ∩
      {p | p.2 ∈ L} ∩
      (⋂ x, {p | p.1 (p.2 x) = x}) ∩
      (⋂ x, {p | p.2 (p.1 x) = x}) := by
    ext p
    simp only [inverseIsometricPairs, mem_setOf_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [hset]
  exact ((hleft.inter hright).inter (isClosed_iInter hinvleft)).inter
    (isClosed_iInter hinvright)

theorem inverseIsometricPairs_isCompact :
    IsCompact (inverseIsometricPairs (X := X)) := by
  apply (isometricSelfMaps_isCompact (X := X)).prod
    (isometricSelfMaps_isCompact (X := X)) |>.of_isClosed_subset
      inverseIsometricPairs_isClosed
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

/-- The inverse-pair presentation is exactly the group of metric
isometries, at the level of underlying sets. -/
def pairsToIsometryEquiv (p : inverseIsometricPairs (X := X)) : X ≃ᵢ X :=
  { toEquiv :=
      { toFun := p.1.1
        invFun := p.1.2
        left_inv := p.2.2.2.2
        right_inv := p.2.2.2.1 }
    isometry_toFun := Isometry.of_dist_eq p.2.1 }

def isometryEquivToPairs (e : X ≃ᵢ X) : inverseIsometricPairs (X := X) := by
  let f : X →ᵇ X := BoundedContinuousFunction.mkOfCompact ⟨e, e.continuous⟩
  let g : X →ᵇ X := BoundedContinuousFunction.mkOfCompact ⟨e.symm, e.symm.continuous⟩
  refine ⟨(f,g), ?_, ?_, ?_, ?_⟩
  · intro x y
    exact e.isometry.dist_eq x y
  · intro x y
    exact e.symm.isometry.dist_eq x y
  · intro x
    exact e.apply_symm_apply x
  · intro x
    exact e.symm_apply_apply x

def isometryEquivPairsEquiv : (X ≃ᵢ X) ≃ inverseIsometricPairs (X := X) where
  toFun := isometryEquivToPairs
  invFun := pairsToIsometryEquiv
  left_inv := by
    intro e
    ext x
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · apply BoundedContinuousFunction.ext
      intro x
      rfl
    · apply BoundedContinuousFunction.ext
      intro x
      rfl

/-- The canonical uniform topology on an isometry and its inverse,
transported from the sup-metric topology of bounded continuous maps. -/
def isometryEquivTopology : TopologicalSpace (X ≃ᵢ X) :=
  TopologicalSpace.induced (isometryEquivToPairs (X := X)) inferInstance

/-- The compact-open presentation records an isometry and its inverse as
ordinary continuous self-maps. -/
def isometryEquivToContinuousPairs (e : X ≃ᵢ X) : C(X, X) × C(X, X) :=
  (⟨e, e.continuous⟩, ⟨e.symm, e.symm.continuous⟩)

def isometryEquivCompactOpenTopology : TopologicalSpace (X ≃ᵢ X) :=
  TopologicalSpace.induced (isometryEquivToContinuousPairs (X := X)) inferInstance

theorem isometryEquivTopology_eq_compactOpen :
    isometryEquivTopology (X := X) =
      isometryEquivCompactOpenTopology (X := X) := by
  let h : ((X →ᵇ X) × (X →ᵇ X)) → C(X, X) × C(X, X) :=
    fun p => (boundedContinuousHomeomorphContinuous p.1,
      boundedContinuousHomeomorphContinuous p.2)
  have hInducing : Topology.IsInducing h := by
    exact (boundedContinuousHomeomorphContinuous (X := X)).isInducing.prodMap
      (boundedContinuousHomeomorphContinuous (X := X)).isInducing
  have hcomp : h ∘ (fun e : X ≃ᵢ X =>
      (isometryEquivToPairs (X := X) e).1) =
      isometryEquivToContinuousPairs (X := X) := by
    funext e
    ext x <;> rfl
  unfold isometryEquivTopology isometryEquivCompactOpenTopology
  rw [← hcomp, ← induced_compose, ← hInducing.eq_induced]
  change TopologicalSpace.induced isometryEquivToPairs
      (TopologicalSpace.induced Subtype.val inferInstance) = _
  rw [induced_compose]
  rfl

theorem isometryEquivToContinuousPairs_continuous :
    letI := isometryEquivTopology (X := X)
    Continuous (isometryEquivToContinuousPairs (X := X)) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  rw [isometryEquivTopology_eq_compactOpen]
  exact continuous_induced_dom

theorem isometryEquiv_action_continuous :
    letI := isometryEquivTopology (X := X)
    Continuous (fun p : (X ≃ᵢ X) × X => p.1 p.2) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  have hforward : Continuous (fun e : X ≃ᵢ X =>
      (isometryEquivToContinuousPairs (X := X) e).1) :=
    continuous_fst.comp isometryEquivToContinuousPairs_continuous
  have hev : Continuous (fun p : C(X, X) × X => p.1 p.2) :=
    ContinuousEval.continuous_eval
  exact hev.comp (hforward.prodMap continuous_id)

theorem isometryEquiv_inv_continuous :
    letI := isometryEquivTopology (X := X)
    Continuous (fun e : X ≃ᵢ X => e⁻¹) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  have hswap : Continuous (fun e : X ≃ᵢ X =>
      (isometryEquivToContinuousPairs (X := X) e).swap) :=
    continuous_swap.comp isometryEquivToContinuousPairs_continuous
  have hEq : (fun e : X ≃ᵢ X =>
      isometryEquivToContinuousPairs (X := X) e⁻¹) =
      (fun e => (isometryEquivToContinuousPairs (X := X) e).swap) := by
    funext e
    ext x <;> rfl
  change @Continuous (X ≃ᵢ X) _ (isometryEquivTopology (X := X)) _ _ at hswap
  rw [isometryEquivTopology_eq_compactOpen] at hswap
  rw [isometryEquivTopology_eq_compactOpen]
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, hEq] using hswap

theorem isometryEquiv_mul_continuous :
    letI := isometryEquivTopology (X := X)
    Continuous (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) => p.1 * p.2) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  let f : (X ≃ᵢ X) → C(X, X) :=
    fun e => (isometryEquivToContinuousPairs (X := X) e).1
  let g : (X ≃ᵢ X) → C(X, X) :=
    fun e => (isometryEquivToContinuousPairs (X := X) e).2
  have hf : Continuous f :=
    continuous_fst.comp isometryEquivToContinuousPairs_continuous
  have hg : Continuous g :=
    continuous_snd.comp isometryEquivToContinuousPairs_continuous
  have hforward : Continuous (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) =>
      (f p.1).comp (f p.2)) := by
    exact ContinuousMap.continuous_comp'.comp
      ((hf.comp continuous_snd).prodMk (hf.comp continuous_fst))
  have hinverse : Continuous (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) =>
      (g p.2).comp (g p.1)) := by
    exact ContinuousMap.continuous_comp'.comp
      ((hg.comp continuous_fst).prodMk (hg.comp continuous_snd))
  have hpair : Continuous (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) =>
      ((f p.1).comp (f p.2), (g p.2).comp (g p.1))) :=
    hforward.prodMk hinverse
  have hEq : (fun p : (X ≃ᵢ X) × (X ≃ᵢ X) =>
      isometryEquivToContinuousPairs (X := X) (p.1 * p.2)) =
      (fun p => ((f p.1).comp (f p.2), (g p.2).comp (g p.1))) := by
    funext p
    ext x <;> rfl
  change @Continuous _ _
    (@instTopologicalSpaceProd _ _ (isometryEquivTopology (X := X))
      (isometryEquivTopology (X := X))) _ _ at hpair
  rw [isometryEquivTopology_eq_compactOpen] at hpair
  rw [isometryEquivTopology_eq_compactOpen]
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, hEq] using hpair

theorem isometryEquiv_topologicalGroup :
    letI := isometryEquivTopology (X := X)
    IsTopologicalGroup (X ≃ᵢ X) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  exact { continuous_mul := isometryEquiv_mul_continuous
          continuous_inv := isometryEquiv_inv_continuous }

theorem isometryEquiv_compactSpace :
    letI := isometryEquivTopology (X := X)
    CompactSpace (X ≃ᵢ X) := by
  letI : TopologicalSpace (X ≃ᵢ X) := isometryEquivTopology (X := X)
  letI : CompactSpace (inverseIsometricPairs (X := X)) :=
    isCompact_iff_compactSpace.mp inverseIsometricPairs_isCompact
  have hi : Topology.IsInducing (isometryEquivPairsEquiv (X := X)) := ⟨rfl⟩
  exact (Equiv.toHomeomorphOfIsInducing
    (isometryEquivPairsEquiv (X := X)) hi).symm.compactSpace

end
end QuaternionicSymmetry.MetricIsometryCompactness
