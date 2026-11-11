/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: https://github.com/n-yamaguchi-0729
-/

module

public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Basic.Countable.Small
public import Mathlib.Data.Finset.Union
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Logic.Small.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Subfield
public import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
public import Nyll.AlgebraicCurves.Hilbert.LinearEquivBaseChangePieceMap

/-!
# Small coefficient fields for the original homogeneous ideal

Finite generators determine a small subfield of the original coefficient field. The ideal descends
along its actual inclusion, and the existing graded-piece base-change equivalence preserves every
degree. This provides small witnesses without changing a chosen Hilbert-polynomial bound.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial
open AlgebraicCurves.Hilbert.Proofs
open S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map

/-- A homogeneous ideal in finitely many variables has a universe-zero field model whose extension
is the original ideal and whose graded pieces have exactly the original dimensions. -/
theorem exists_small_field_homogeneous_ideal_finrank_piece_eq
    (n : ℕ) (K : Type u) [Field K] (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    ∃ (K₀ : Type) (_ : Field K₀) (f : K₀ →+* K)
      (J : Ideal (MvPolynomial (Fin (n + 1)) K₀)),
      (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) ∧
      J.map (MvPolynomial.map f) = I ∧
      ∀ d : ℕ, Module.finrank K₀ (piece J d) = Module.finrank K (piece I d) := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  let c : Finset K := s.biUnion MvPolynomial.coeffs
  let E : Subfield K := Subfield.closure (c : Set K)
  have : Countable E := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max (c : Set K)).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  let K₀ : Type := Shrink.{0} E
  let : Field K₀ := (equivShrink.{0} E).symm.field
  let e : K₀ ≃+* E := Shrink.ringEquiv.{0} E
  let f : K₀ →+* K := E.subtype.comp e.toRingHom
  let : Algebra K₀ K := f.toAlgebra
  let J : Ideal (MvPolynomial (Fin (n + 1)) K₀) := I.comap (MvPolynomial.map f)
  have hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J := by
    intro p hp d
    change MvPolynomial.map f (homogeneousComponent d p) ∈ I
    rw [← HilbPieceBC.homogeneousComponent_map f d p]
    exact hI (MvPolynomial.map f p) hp d
  have hmap : J.map (MvPolynomial.map f) = I := by
    refine le_antisymm Ideal.map_comap_le ?_
    have hsle : Ideal.span (s : Set (MvPolynomial (Fin (n + 1)) K)) ≤
        J.map (MvPolynomial.map f) := by
      refine Ideal.span_le.mpr ?_
      intro p hp
      have hpI : p ∈ I := hs ▸ Ideal.subset_span hp
      have hprange : p ∈ Set.range (MvPolynomial.map f) := by
        apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
        intro a ha
        have haE : a ∈ E := Subfield.subset_closure
          (Finset.mem_biUnion.mpr ⟨p, hp, ha⟩)
        refine ⟨e.symm ⟨a, haE⟩, ?_⟩
        exact congrArg (fun x : E => (x : K)) (e.apply_symm_apply ⟨a, haE⟩)
      obtain ⟨q, hq⟩ := hprange
      have hqJ : q ∈ J := by
        change MvPolynomial.map f q ∈ I
        rw [hq]
        exact hpI
      change p ∈ J.map (MvPolynomial.map f)
      exact hq ▸ Ideal.mem_map_of_mem (MvPolynomial.map f) hqJ
    exact hs ▸ hsle
  refine ⟨K₀, inferInstance, f, J, hJ, hmap, ?_⟩
  intro d
  obtain ⟨ε, -⟩ := (exists_linearEquiv_baseChange_piece_map n K₀ K J hJ).2 d
  have hdim : Module.finrank K₀ (piece J d) =
      Module.finrank K (piece (J.map (MvPolynomial.map f)) d) :=
    (Module.finrank_baseChange (R := K) (S := K₀) (M' := piece J d)).symm.trans ε.finrank_eq
  exact hdim.trans (congrArg (fun H : Ideal (MvPolynomial (Fin (n + 1)) K) =>
    Module.finrank K (piece H d)) hmap)

end AlgebraicGeometry.HilbertFunctor
