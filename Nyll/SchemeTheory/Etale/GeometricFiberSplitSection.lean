/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# A section of the original algebraically closed geometric fiber

A surjective locally finite type morphism has a section after base change
to an algebraically closed field. The actual section comes from the
existing rational-point equivalence applied to a closed point of the
original geometric fiber. No replacement model or splitting is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  [LocallyOfFiniteType q] [Surjective q]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (CommRingCat.of Ω) ⟶ X)

/-- The actual base change of a surjective locally finite type morphism
to an algebraically closed geometric point admits a section. -/
theorem exists_geometricFiberSection_of_isAlgClosed :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ pullback q t,
      s ≫ pullback.snd q t = 𝟙 _ := by
  have : JacobsonSpace ↥(pullback q t) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q t)
  obtain ⟨y, _hy⟩ := (pullback.snd q t).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨z, _hz, hz⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set ↥(pullback q t))) ⟨y, Set.mem_univ y⟩
      isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint (pullback.snd q t) z hz,
    pointOfClosedPoint_comp (pullback.snd q t) z hz⟩

end AlgebraicGeometry.Scheme.Hom
