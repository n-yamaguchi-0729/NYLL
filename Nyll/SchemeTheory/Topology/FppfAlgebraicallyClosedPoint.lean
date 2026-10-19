/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Fppf sections at an algebraically closed field

Every fppf covering sieve on the spectrum of an algebraically closed field is
the maximal sieve: a nonempty finite-type member has a rational closed point,
which gives a section. Thus a local bijection of presheaves is an actual
bijection at every algebraically closed field-valued test object.
-/

noncomputable section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A covering sieve on an algebraically closed field contains the identity.
The section is supplied by a rational closed point of a nonempty cover member. -/
theorem fppfSieve_eq_top_of_isAlgClosed
    (S : Sieve (Spec (CommRingCat.of K)))
    (hS : S ∈ fppfTopology (Spec (CommRingCat.of K))) : S = ⊤ := by
  have : fppfPrecoverage.HasIsos := ⟨fun f => Hom.singleton_mem_fppfPrecoverage f⟩
  have : JointlySurjective fppfPrecoverage.{u} :=
    inferInstanceAs (JointlySurjective
      (precoverage ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation)))
  obtain ⟨R, hR, hRS⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := fppfPrecoverage)).mp hS
  obtain ⟨V, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  have hV := hRS
  obtain ⟨j, y, _hy⟩ := Scheme.Cover.exists_eq V (IsLocalRing.closedPoint K)
  have : LocallyOfFinitePresentation (V.f j) :=
    (Scheme.Cover.map_prop
      (P := (@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) V j).2
  have : JacobsonSpace (V.X j) := LocallyOfFiniteType.jacobsonSpace (V.f j)
  obtain ⟨z, _hzU, hz⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set (V.X j))) ⟨y, Set.mem_univ y⟩ isOpen_univ.isLocallyClosed
  have hf : S (V.f j) := (Presieve.ofArrows_le_iff.mp hV) j
  have hs : S (pointOfClosedPoint (V.f j) z hz ≫ V.f j) :=
    S.downward_closed hf (pointOfClosedPoint (V.f j) z hz)
  have hid : S (𝟙 (Spec (CommRingCat.of K))) :=
    (congrArg (fun f => S f) (pointOfClosedPoint_comp (V.f j) z hz)).mp hs
  exact Sieve.id_mem_iff_eq_top.mp hid

/-- The same splitting applies in a slice over any base scheme. -/
theorem fppfOverSieve_eq_top_of_isAlgClosed {B : Scheme.{u}}
    (t : Spec (CommRingCat.of K) ⟶ B) (S : Sieve (Over.mk t))
    (hS : S ∈ (fppfTopology.over B) (Over.mk t)) : S = ⊤ := by
  have h := fppfSieve_eq_top_of_isAlgClosed (Sieve.overEquiv (Over.mk t) S)
    ((GrothendieckTopology.mem_over_iff _ _).mp hS)
  apply (Sieve.overEquiv (Over.mk t)).injective
  rw [h, map_top]

/-- A local bijection of actual presheaves is a bijection on any algebraically
closed field-valued test. In particular this applies to the sheafification map. -/
theorem fppf_locallyBijective_app_bijective {B : Scheme.{u}}
    {F G : (Over B)ᵒᵖ ⥤ Type w} (a : F ⟶ G)
    [Presheaf.IsLocallyInjective (fppfTopology.over B) a]
    [Presheaf.IsLocallySurjective (fppfTopology.over B) a]
    (t : Spec (CommRingCat.of K) ⟶ B) :
    Function.Bijective (a.app (op (Over.mk t))) := by
  constructor
  · intro x y hxy
    have h := fppfOverSieve_eq_top_of_isAlgClosed t (Presheaf.equalizerSieve (F := F) x y)
      (Presheaf.equalizerSieve_mem (fppfTopology.over B) a x y hxy)
    exact (Presheaf.equalizerSieve_eq_top_iff (F := F) x y).mp h
  · intro y
    have h := fppfOverSieve_eq_top_of_isAlgClosed t (Presheaf.imageSieve a y)
      (Presheaf.imageSieve_mem (fppfTopology.over B) a y)
    have hid : Presheaf.imageSieve a y (𝟙 (Over.mk t)) :=
      Sieve.id_mem_iff_eq_top.mpr h
    obtain ⟨x, hx⟩ := hid
    refine ⟨x, ?_⟩
    simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply] using hx

end AlgebraicGeometry.Scheme
