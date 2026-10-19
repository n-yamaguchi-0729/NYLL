/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction

/-!
# A natural local comparison preserves the canonical descent action

A natural transformation need only be invertible after the actual descent
cover. Transporting a local representation along that local isomorphism
preserves its scheme-valued descent action exactly.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
  (G H : (Over S)ᵒᵖ ⥤ Type (u + 1)) (η : G ⟶ H)
  [IsIso (Functor.whiskerLeft (Over.map s).op η)]
  {X' : Scheme.{u}} (x' : X' ⟶ S')
  (eG : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))

/-- Transport the actual local representation along the restricted comparison. -/
def localRepresentationOfNaturalIso :
    ((Over.map s).op ⋙ H).RepresentableBy (Over.mk x') :=
  eG.ofIso (asIso (Functor.whiskerLeft (Over.map s).op η))

/-- The local comparison sends each represented class by the given natural map. -/
theorem localRepresentationOfNaturalIso_homEquiv {T : Over S'} (m : T ⟶ Over.mk x') :
    (localRepresentationOfNaturalIso s G H η x' eG).homEquiv m =
      η.app (op ((Over.map s).obj T)) (eG.homEquiv m) := rfl

/-- The transported representation induces the identical action on the same scheme. -/
theorem repAct_localRepresentationOfNaturalIso :
    repAct s H x' (localRepresentationOfNaturalIso s G H η x' eG) = repAct s G x' eG := by
  let eH := localRepresentationOfNaturalIso s G H η x' eG
  have h : repActOver s H x' eH = repActOver s G x' eG := by
    apply eH.homEquiv.injective
    calc
      eH.homEquiv (repActOver s H x' eH) =
          H.map (fstOver s x').op (eH.homEquiv (𝟙 (Over.mk x'))) := by
        rw [repActOver, Equiv.apply_symm_apply]
        rfl
      _ = H.map (fstOver s x').op
          (η.app (op ((Over.map s).obj (Over.mk x'))) (eG.homEquiv (𝟙 (Over.mk x')))) := rfl
      _ = η.app (op ((Over.map s).obj (Over.mk (pullback.snd (x' ≫ s) s))))
          (G.map (fstOver s x').op (eG.homEquiv (𝟙 (Over.mk x')))) :=
        (ConcreteCategory.congr_hom (η.naturality (fstOver s x').op)
          (eG.homEquiv (𝟙 (Over.mk x')))).symm
      _ = eH.homEquiv (repActOver s G x' eG) := by
        change _ = η.app _ (eG.homEquiv (eG.homEquiv.symm _))
        rw [Equiv.apply_symm_apply]
        rfl
  exact congrArg (fun m => m.left) h

end AlgebraicGeometry.DescentAction
