/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Etale.IsomorphismNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Isomorphism neighborhoods over a universally closed family

An actual base change which makes a finite flat finitely presented morphism
an isomorphism forces its rank to be one at every point of the corresponding
fiber. The existing proper-neighborhood theorem then gives a neighborhood
of the base whose entire inverse image lies in the rank-one locus.

This is the geometric spreading step used for morphisms of finite locally
constant sheaves after applying their existing finite étale representers.
The original base change and original morphism are retained throughout.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If a finite flat finitely presented morphism becomes an isomorphism
on the specified base change of a universally closed family, then it is an
isomorphism over the full inverse image of a neighborhood of each point
in the image of that base change. -/
theorem Scheme.Hom.exists_isIso_restrict_preimage_of_isIso_baseChange
    {Z Y X T : Scheme.{u}} (p : Z ⟶ Y) (f : Y ⟶ X) (t : T ⟶ X)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [UniversallyClosed f]
    [IsIso (pullback.snd p (pullback.fst f t))] (a : T) :
    ∃ U : X.Opens, t a ∈ U ∧ IsIso (p ∣_ (f ⁻¹ᵁ U)) := by
  let V : Y.Opens :=
    ⟨{y | p.finrank y = 1}, p.isLocallyConstant_finrank.isOpen_fiber 1⟩
  have hV (y : Y) (hy : f y = t a) : y ∈ V := by
    obtain ⟨b, hb, _⟩ := Scheme.Pullback.exists_preimage_pullback y a hy
    have h := congrFun
      (Scheme.Hom.finrank_eq_one_of_isIso (pullback.snd p (pullback.fst f t))) b
    rw [Scheme.Hom.finrank_pullback_snd, hb] at h
    exact h
  obtain ⟨U, ha, hUV⟩ := f.exists_preimage_le_of_fiber_subset (t a) V hV
  refine ⟨U, ha, (Scheme.Hom.isIso_iff_finrank_eq (p ∣_ (f ⁻¹ᵁ U))).mpr ?_⟩
  funext y
  calc
    (p ∣_ (f ⁻¹ᵁ U)).finrank y = p.finrank ((f ⁻¹ᵁ U).ι y) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _
        (isPullback_morphismRestrict p (f ⁻¹ᵁ U)).flip y
    _ = 1 := hUV y.property

end AlgebraicGeometry
