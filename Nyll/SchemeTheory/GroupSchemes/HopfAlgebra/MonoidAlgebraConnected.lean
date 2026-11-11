/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The inverse character-map construction follows the existing Mathlib construction:
Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean
Copyright (c) 2025 Amelia Livingston, Yaël Dillies, Michał Mrugała.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Group-algebra characters over connected coefficient rings

The coproduct compares each pair of coefficients. Trivial idempotents and a
nonzero counit therefore force a group-like element to be an original basis
element. This includes connected rings with nilpotents.
-/

@[expose] public section

noncomputable section

universe u

namespace SchemeTheory.HopfGroupLike.CharacterLattice

/-- A connected prime spectrum leaves only zero and one as idempotent coefficients. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem {R : Type u} [CommRing R]
    [ConnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hclopen : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
    rw [PrimeSpectrum.basicOpen_zero]
    exact TopologicalSpace.Opens.ext h
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
    rw [PrimeSpectrum.basicOpen_one]
    exact TopologicalSpace.Opens.ext h

end SchemeTheory.HopfGroupLike.CharacterLattice

namespace AddMonoidAlgebra

open Coalgebra
open scoped TensorProduct

variable {R M G H : Type*} [CommRing R]

private def connectedCoefficient (m : M) : R[M] →ₗ[R] R :=
  (Finsupp.lapply m).comp (coeffLinearEquiv R).toLinearMap

private def connectedTensorCoefficient (m n : M) : R[M] ⊗[R] R[M] →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map (connectedCoefficient m) (connectedCoefficient n))

private theorem connectedTensorCoefficient_tmul (m n : M) (x y : R[M]) :
    connectedTensorCoefficient m n (x ⊗ₜ[R] y) = x.coeff m * y.coeff n :=
  rfl

private theorem connectedTensorCoefficient_comul [DecidableEq M] (m n : M) (x : R[M]) :
    connectedTensorCoefficient m n (comul (R := R) x) =
      if m = n then x.coeff m else 0 := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    simp only [map_zero, coeff_zero, Finsupp.zero_apply, ite_self]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, coeff_add, Finsupp.add_apply]
    by_cases hmn : m = n
    · simp only [ite_eq_left hmn]
    · simp only [ite_eq_right hmn, zero_add]
  | single k a =>
    rw [comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
      lsingle_apply, lsingle_apply, connectedTensorCoefficient_tmul]
    simp only [coeff_single]
    by_cases hkm : k = m
    · subst k
      by_cases hmn : m = n
      · subst n
        simp only [Finsupp.single_eq_same, ite_true, one_mul]
      · simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hmn,
          ite_eq_right hmn, one_mul]
    · simp only [Finsupp.single_eq_of_ne' hkm, zero_mul, ite_self]

/-- If the coefficient ring has no nontrivial idempotents, every group-like element
of its additive monoid algebra is one of the original basis elements. -/
theorem isGroupLikeElem_iff_mem_range_single_one_of_idempotents [Nontrivial R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) := by
  classical
  constructor
  · intro hx
    have hcoeff (m n : M) :
        (if m = n then x.coeff m else 0) = x.coeff m * x.coeff n := by
      have h := congrArg (connectedTensorCoefficient m n) hx.comul_eq_tmul_self
      rw [connectedTensorCoefficient_comul, connectedTensorCoefficient_tmul] at h
      exact h
    obtain ⟨m, hm⟩ : ∃ m : M, x.coeff m ≠ 0 := by
      by_contra h
      apply hx.ne_zero
      apply coeff_injective
      ext m
      exact not_not.mp (not_exists.mp h m)
    have hmIdem : IsIdempotentElem (x.coeff m) := by
      change x.coeff m * x.coeff m = x.coeff m
      have h := hcoeff m m
      rw [ite_eq_left rfl] at h
      exact h.symm
    have hmOne : x.coeff m = 1 := (hidem _ hmIdem).resolve_left hm
    refine ⟨m, ?_⟩
    apply coeff_injective
    ext n
    by_cases hnm : n = m
    · subst n
      simp only [coeff_single, Finsupp.single_eq_same, hmOne]
    · have h := hcoeff m n
      rw [ite_eq_right (Ne.symm hnm), hmOne, one_mul] at h
      simpa only [coeff_single, Finsupp.single_eq_of_ne hnm] using h
  · rintro ⟨m, rfl⟩
    exact isGroupLikeElem_single_one m

/-- Over a nontrivial connected coefficient ring, the group-like elements are
exactly the basis elements with coefficient one. -/
theorem isGroupLikeElem_iff_mem_range_single_one_of_connected [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum R)] {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) :=
  isGroupLikeElem_iff_mem_range_single_one_of_idempotents
    (fun _ he =>
      SchemeTheory.HopfGroupLike.CharacterLattice.eq_zero_or_eq_one_of_isIdempotentElem he)

section AddGroup

variable [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)] [AddGroup G] [AddGroup H]

/-- Recover the actual character homomorphism from a bialgebra map over a connected ring. -/
def mapDomainOfBialgHomOfConnected (f : R[G] →ₐc[R] R[H]) : G →+ H := by
  classical
  let φ : G → H := fun g =>
    (isGroupLikeElem_iff_mem_range_single_one_of_connected.mp
      ((isGroupLikeElem_single_one g).map f)).choose
  have hφ (g : G) : single (φ g) 1 = f (single g 1) :=
    (isGroupLikeElem_iff_mem_range_single_one_of_connected.mp
      ((isGroupLikeElem_single_one g).map f)).choose_spec
  exact
    { toFun := φ
      map_zero' := single_left_injective (R := R) one_ne_zero <|
        (hφ 0).trans (by simpa only [one_def] using (map_one f))
      map_add' := fun g h => single_left_injective (R := R) one_ne_zero <| by
        calc
          single (φ (g + h)) 1 = f (single (g + h) 1) := hφ (g + h)
          _ = f (single g 1 * single h 1) := by rw [single_mul_single, one_mul]
          _ = f (single g 1) * f (single h 1) := map_mul f _ _
          _ = single (φ g) 1 * single (φ h) 1 :=
            congrArg₂ (· * ·) (hφ g).symm (hφ h).symm
          _ = single (φ g + φ h) 1 := by rw [single_mul_single, one_mul] }

/-- The recovered character map sends a basis element to its actual bialgebra image. -/
theorem single_mapDomainOfBialgHomOfConnected (f : R[G] →ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomOfConnected f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_single_one_of_connected.mp
    ((isGroupLikeElem_single_one g).map f)).choose_spec

/-- Rebuilding the bialgebra map from its recovered characters returns the original map. -/
theorem mapDomainBialgHom_mapDomainOfBialgHomOfConnected (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHomOfConnected f) = f := by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomOfConnected f x
  · ext

/-- Recovering the characters of the original `mapDomainBialgHom` returns the same map. -/
theorem mapDomainOfBialgHomOfConnected_mapDomainBialgHom (f : G →+ H) :
    mapDomainOfBialgHomOfConnected (mapDomainBialgHom R f) = f := by
  ext g
  apply single_left_injective (R := R) one_ne_zero
  change single (mapDomainOfBialgHomOfConnected (mapDomainBialgHom R f) g) 1 =
    single (f g) 1
  rw [single_mapDomainOfBialgHomOfConnected, mapDomainBialgHom_single]

/-- Character maps classify bialgebra maps over a nontrivial connected coefficient ring.
The forward map is the original `mapDomainBialgHom`. -/
def mapDomainBialgHomEquivOfConnected : (G →+ H) ≃ (R[G] →ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHomOfConnected
  left_inv := mapDomainOfBialgHomOfConnected_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHomOfConnected

end AddGroup

/-- On a domain the connected-ring equivalence is the existing Mathlib equivalence,
including its uniquely determined inverse. -/
theorem mapDomainBialgHomEquivOfConnected_eq [IsDomain R] [AddGroup G] [AddGroup H] :
    (mapDomainBialgHomEquivOfConnected (R := R) (G := G) (H := H)) =
      mapDomainBialgHomEquiv (R := R) := by
  apply Equiv.ext
  intro f
  rfl

end AddMonoidAlgebra
