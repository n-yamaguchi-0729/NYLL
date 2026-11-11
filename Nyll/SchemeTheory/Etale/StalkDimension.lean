/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Stalk dimension under etale morphisms

The maximal ideal of an unramified local extension is the extension of the
base maximal ideal. The flat dimension formula therefore has zero fiber
term. This identifies the dimensions used in codimension-one branch
criteria before and after an etale neighborhood change.
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

/-- Etale changes of neighborhood preserve the dimension of the actual
local ring, without regularity or irreducibility assumptions. -/
theorem ringKrullDim_stalk_eq_of_etale
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Etale f] (x : X) :
    ringKrullDim (Y.presheaf.stalk (f x)) = ringKrullDim (X.presheaf.stalk x) := by
  let R : CommRingCat.{u} := Y.presheaf.stalk (f x)
  let S : CommRingCat.{u} := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let : Module.Flat R S := Flat.stalkMap f x
  let : Algebra.FormallyUnramified R S := FormallyUnramified.stalkMap f x
  let : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f x
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal S)
  rw [Algebra.FormallyUnramified.map_maximalIdeal] at h
  have hheight : (maximalIdeal R).height = (maximalIdeal S).height := by
    simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h.symm
  calc
    ringKrullDim (Y.presheaf.stalk (f x)) =
        ((maximalIdeal R).height : WithBot ℕ∞) :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = ((maximalIdeal S).height : WithBot ℕ∞) :=
      congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight
    _ = ringKrullDim (X.presheaf.stalk x) :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end AlgebraicGeometry.Scheme
