/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The actual group comparison for iterated scheme base change

The canonical monoidal pullback comparison gives a group-scheme isomorphism
whose underlying arrow is the inverse component of the supplied pullback comparison.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GroupSchemes

/-- The actual iterated and direct group pullbacks are isomorphic, with the
same underlying comparison as the given scheme pullback functors. -/
theorem exists_baseChangeTowerIso
    {S S' S'' : Scheme.{u}} (f : S' ⟶ S) (g : S'' ⟶ S') (h : S'' ⟶ S)
    (e : Over.pullback h ≅ Over.pullback f ⋙ Over.pullback g)
    (H : CommGrp (Over S)) :
    ∃ eH : (baseChange g).obj ((baseChange f).obj H) ≅ (baseChange h).obj H,
      eH.hom.hom.hom.hom = e.inv.app H.X := by
  refine ⟨((Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso).app H).symm, ?_⟩
  change (𝟙 _ ≫ e.inv.app H.X) = e.inv.app H.X
  exact Category.id_comp (e.inv.app H.X)

/-- A square for the underlying pullback functors is the square for an
actual target-group comparison. The same two maps are retained with their
native group-carrier targets before the comparison witness is returned. -/
theorem exists_baseChangeTowerIso_square
    {S S' S'' : Scheme.{u}} (f : S' ⟶ S) (g : S'' ⟶ S') (h : S'' ⟶ S)
    (e : Over.pullback h ≅ Over.pullback f ⋙ Over.pullback g)
    (H : CommGrp (Over S)) {U₁ U₂ : Over S''} (a : U₁ ⟶ U₂)
    (q₁ : U₁ ⟶ (Over.pullback g).obj ((Over.pullback f).obj H.X))
    (q₂ : U₂ ⟶ (Over.pullback h).obj H.X)
    (hq : a ≫ q₂ = q₁ ≫ e.inv.app H.X) :
    let q₁native : U₁ ⟶ ((baseChange g).obj ((baseChange f).obj H)).X := q₁
    let q₂native : U₂ ⟶ ((baseChange h).obj H).X := q₂
    ∃ eH : (baseChange g).obj ((baseChange f).obj H) ≅ (baseChange h).obj H,
      a ≫ q₂native = q₁native ≫ eH.hom.hom.hom.hom := by
  intro q₁native q₂native
  obtain ⟨eH, heH⟩ := exists_baseChangeTowerIso f g h e H
  refine ⟨eH, ?_⟩
  exact hq.trans (congrArg
    (fun t : (Over.pullback g).obj ((Over.pullback f).obj H.X) ⟶
      (Over.pullback h).obj H.X => q₁ ≫ t) heH.symm)

end AlgebraicGeometry.GroupSchemes
