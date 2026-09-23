/-
Copyright (c) 2026 Dishant Shah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dishant Shah
-/
module

public import Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

public import GraphDimension.Basic

import GraphDimension.Extremal.FourteenEdges
import GraphDimension.Geometry.CompleteGraph
import GraphDimension.Geometry.K133
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Proofs for `InlineErdos1007Dim5`

The proof sibling. Unlike its statement module this may import the development, and it is the one
explicit exception to the standalone isolation rule.

The bridge to the graph-dimension definitions is `Iff.rfl` in both directions of meaning:
`UnitDistanceEmbeddable` and `HasDimension` are the statement module's spellings of
`SimpleGraph.UnitDistEmbeddable` and `SimpleGraph.HasDimension`. On it stand the extremal
attainment — `K₆` and `K₁,₃,₃` each of dimension five with fifteen edges — its satisfiability
witness, the separating examples, and the lower bound: a graph with at most fourteen edges has a
unit-distance representation in `ℝ⁴`, so fifteen is the least number of edges of a graph of
dimension five.
-/

public section

namespace Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5

open SimpleGraph

/-- The statement module's `UnitDistanceEmbeddable` is the graph-dimension library's
`SimpleGraph.UnitDistEmbeddable`: the two definitions differ in binder names only, so the bridge
is `Iff.rfl`. -/
theorem unitDistanceEmbeddable_iff {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    UnitDistanceEmbeddable G n ↔ G.UnitDistEmbeddable n := Iff.rfl

/-- The statement module's `HasDimension` is the graph-dimension library's
`SimpleGraph.HasDimension`: the two definitions differ in binder names only, so the bridge is
`Iff.rfl`. -/
theorem hasDimension_iff {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    HasDimension G n ↔ G.HasDimension n := Iff.rfl

/-- `K₂` plus an isolated vertex, placed in `ℝ¹`, has a non-edge at distance one. -/
theorem UnitDistanceEmbeddable.separating.proof : UnitDistanceEmbeddable.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have inj : Function.Injective (fun j : Fin 3 =>
      EuclideanSpace.single (0 : Fin 1) (j : ℝ)) := by
    intro u v h
    have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) h
    simp only [PiLp.single_eq_same] at hcoord
    exact Fin.ext (Nat.cast_inj.mp hcoord)
  let f : Fin 3 → EuclideanSpace ℝ (Fin 1) := fun j => EuclideanSpace.single 0 (j : ℝ)
  refine ⟨Fin 3, fromEdgeSet {s(0, 1)}, 1, f, ⟨f, inj, ?_⟩, inj, ?_, 1, 2, ?_, ?_, ?_⟩
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · intro u v huv
    rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at huv
    rcases huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · rw [dist_axis]
      norm_num
    · rw [dist_axis]
      norm_num
  · decide
  · rw [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    decide
  · rw [dist_axis]
    norm_num

/-- A graph representable in `ℝ⁴` need not have dimension four. -/
theorem HasDimension.separating.proof : HasDimension.separating := by
  have dist_axis {n : ℕ} (i : Fin n) (a b : ℝ) :
      dist (EuclideanSpace.single i a) (EuclideanSpace.single i b) = |a - b| := by
    rw [PiLp.dist_single_same, Real.dist_eq]
  have k2 (n : ℕ) (i : Fin n) : UnitDistanceEmbeddable (completeGraph (Fin 2)) n := by
    refine ⟨fun j => EuclideanSpace.single i (j : ℝ), ?_, ?_⟩
    · intro u v h
      have hcoord := congr_arg (fun p : EuclideanSpace ℝ (Fin n) => p i) h
      simp only [PiLp.single_eq_same] at hcoord
      exact Fin.ext (Nat.cast_inj.mp hcoord)
    · intro u v huv
      fin_cases u <;> fin_cases v <;> rw [top_adj] at huv
      · exact (huv rfl).elim
      · rw [dist_axis]
        norm_num
      · rw [dist_axis]
        norm_num
      · exact (huv rfl).elim
  refine ⟨Fin 2, completeGraph (Fin 2), ⟨0, 1, ?_⟩, k2 4 0, ?_⟩
  · rw [top_adj]
    decide
  · intro h
    have hle : (4 : ℕ) ≤ 1 := (mem_lowerBounds.mp h.2) 1 (k2 1 0)
    exact absurd hle (by decide : ¬ (4 : ℕ) ≤ 1)

/-- The two vertices `⟨1, 0⟩` and `⟨1, 1⟩` of the middle part of `K₁,₃,₃` are distinct and
non-adjacent, which the complete graph on the same seven vertices does not allow. -/
theorem K133.separating.proof : K133.separating := by
  refine ⟨Sigma.mk (Fin.mk 1 (by decide)) (Fin.mk 1 (by decide)),
    Sigma.mk (Fin.mk 1 (by decide)) (Fin.mk 2 (by decide)), ?_, ?_⟩
  · decide
  · simp [K133]

/-- `K₆` has fifteen edges. -/
theorem completeGraph_six_edgeSet_ncard :
    (SimpleGraph.completeGraph (Fin 6)).edgeSet.ncard = 15 := by
  have hcard : (SimpleGraph.completeGraph (Fin 6)).edgeFinset.card = 15 := by decide
  exact (Set.ncard_eq_toFinset_card' (SimpleGraph.completeGraph (Fin 6)).edgeSet).trans hcard

/-- `K₁,₃,₃` has fifteen edges. -/
theorem K133_edgeSet_ncard : K133.edgeSet.ncard = 15 := by
  have hcard : K133.edgeFinset.card = 15 := by decide
  exact (Set.ncard_eq_toFinset_card' K133.edgeSet).trans hcard

/-- Fifteen is attained: `K₆` has dimension five and fifteen edges. -/
theorem DimensionFive.witness.proof : DimensionFive.witness :=
  ⟨6, SimpleGraph.completeGraph (Fin 6),
    (hasDimension_iff _ _).mp (hasDimension_completeGraph 6), completeGraph_six_edgeSet_ncard⟩

/-- **Erdős problem 1007, dimension five.** The least number of edges of a graph of dimension
five is fifteen. `K₆` attains fifteen, and every graph with at most fourteen edges has a
unit-distance representation in `ℝ⁴`, so none of them has dimension five. -/
theorem DimensionFive.proof : DimensionFive := by
  refine ⟨DimensionFive.witness.proof, ?_⟩
  intro m ⟨_, G, hdim, hcard⟩
  suffices ¬ m ≤ 14 by omega
  intro hm14
  have hE : G.edgeSet.ncard ≤ 14 := by
    rw [hcard]
    exact hm14
  have hembed : UnitDistanceEmbeddable G 4 :=
    (unitDistanceEmbeddable_iff G 4).mpr (unitDistEmbeddable_four_of_ncard_edgeSet_le G hE)
  have hle : (5 : ℕ) ≤ 4 := (mem_lowerBounds.mp hdim.2) 4 hembed
  exact absurd hle (by decide : ¬ (5 : ℕ) ≤ 4)

/-- **Erdős problem 1007, extremal half for dimension five.** `K₆` and `K₁,₃,₃` each have
dimension five and exactly fifteen edges: the complete-graph dimension of Erdős–Harary–Tutte for
`K₆`, and Chaffee–Noble Theorem 8 for `K₁,₃,₃`. -/
theorem DimensionFiveExtremal.proof : DimensionFiveExtremal :=
  ⟨⟨(hasDimension_iff _ _).mp (hasDimension_completeGraph 6), completeGraph_six_edgeSet_ncard⟩,
    ⟨(hasDimension_iff _ _).mp hasDimension_K133, K133_edgeSet_ncard⟩⟩

/-- `K₆` and `K₁,₃,₃` are not even isomorphic: six vertices against seven. -/
theorem DimensionFiveExtremal.witness.proof : DimensionFiveExtremal.witness := by
  rintro ⟨ψ⟩
  have hc := ψ.card_eq
  simp only [Fintype.card_fin, Fintype.card_sigma, Fin.sum_univ_three,
    show (![1, 3, 3] 0 : ℕ) = 1 from rfl,
    show (![1, 3, 3] 1 : ℕ) = 3 from rfl,
    show (![1, 3, 3] 2 : ℕ) = 3 from rfl] at hc
  omega

end Erdos1007Dim5.Standalone.Mathlib.InlineErdos1007Dim5
