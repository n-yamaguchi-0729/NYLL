/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecializationBaseChange

/-!
# Cartesian and natural comparison of actual family fibers

These lemmas use the already defined family-fiber maps. Base change
constructs the map of total spaces and makes the comparison squares
commute for every compatible pair of points of the two bases.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- A cartesian family square gives a cartesian square on the actual fibers. -/
theorem properFamilyFiberMapOver_isPullback {X Y S T P Q : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (a : X ⟶ Y) (c : S ⟶ T)
    (ha : f ≫ c = a ≫ g) (v : P ⟶ S) (w : Q ⟶ T)
    (j : P ⟶ Q) (hv : v ≫ c = j ≫ w) (hcart : IsPullback a f g c) :
    IsPullback (properFamilyFiberMapOver f g a c ha v w j hv)
      (Limits.pullback.snd f v) (Limits.pullback.snd g w) j := by
  apply IsPullback.of_right
    (p := properFamilyFiberMapOver_snd f g a c ha v w j hv)
    (t := IsPullback.of_hasPullback g w)
  rw [properFamilyFiberMapOver_fst, ← hv]
  exact (IsPullback.of_hasPullback f v).paste_horiz hcart

/-- A morphism of the original families commutes with the actual fiber
comparisons obtained from one common base change and one common point square. -/
theorem properFamilyFiberMapOver_baseChange_naturality
    {X Y S T P Q : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (a : X ⟶ Y) (ha : a ≫ g = f)
    (c : T ⟶ S) (v : P ⟶ T) (w : Q ⟶ S) (j : P ⟶ Q)
    (hv : v ≫ c = j ≫ w) :
    let fC := Limits.pullback.snd f c
    let gC := Limits.pullback.snd g c
    let aC := properFamilyFiberMap f g a ha c
    properFamilyFiberMap fC gC aC (properFamilyFiberMap_snd f g a ha c) v ≫
        properFamilyFiberMapOver gC g (Limits.pullback.fst g c) c
          Limits.pullback.condition.symm v w j hv =
      properFamilyFiberMapOver fC f (Limits.pullback.fst f c) c
          Limits.pullback.condition.symm v w j hv ≫
        properFamilyFiberMap f g a ha w := by
  intro fC gC aC
  have haC : aC ≫ Limits.pullback.fst g c = Limits.pullback.fst f c ≫ a :=
    properFamilyFiberMap_fst f g a ha c
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, properFamilyFiberMapOver_fst,
      properFamilyFiberMapOver_fst_assoc,
      properFamilyFiberMap_fst_assoc, properFamilyFiberMap_fst, haC]
  · simp only [Category.assoc, properFamilyFiberMapOver_snd,
      properFamilyFiberMap_snd_assoc, properFamilyFiberMap_snd]

end AlgebraicGeometry.FiniteEtale
