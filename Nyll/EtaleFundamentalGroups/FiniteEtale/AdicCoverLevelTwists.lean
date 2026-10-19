/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraMap
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Tensor.AffineProjectionFormula
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The original cover modules on their actual closed levels

The finite cover at each level has its original direct-image module
on that level. The actual composition isomorphism identifies its
direct image on the ambient scheme with the previously constructed
adic cover module.

For a quasicoherent twisting factor, the actual affine projection
formula identifies the ambient twisted module with the direct image
of the original cover module twisted on its own closed level. Thus
the level module used in a presentation is a constructed object,
including the comparison with the original ambient cover sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The native direct-image module of the actual finite cover on
its own original closed level. -/
def coverLevelModule (n : ℕ) : (level f I n).Modules :=
  Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (cover f I V n).hom)

instance coverLevelModule_isQuasicoherent (n : ℕ) :
    (coverLevelModule f I V n).IsQuasicoherent := by
  have : IsFinite (cover f I V n).hom := (cover f I V n).prop.1
  exact Scheme.DirectImageAlgebra.isQuasicoherent_underlyingModule (cover f I V n).hom

instance coverLevelModule_isFiniteType (n : ℕ) :
    (coverLevelModule f I V n).IsFiniteType := by
  have : IsFinite (cover f I V n).hom := (cover f I V n).prop.1
  exact Scheme.DirectImageAlgebra.isFiniteType_underlyingModule (cover f I V n).hom

/-- The actual composition of direct images recovers the original
adic cover module on the ambient scheme. -/
def moduleSheafLevelIso (n : ℕ) :
    moduleSheaf f I V n ≅
      (pushforward (Limits.pullback.fst f (baseInclusion I n))).obj
        (coverLevelModule f I V n) := by
  let c : (cover f I V n).left ⟶ level f I n := (cover f I V n).hom
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let T : (cover f I V n).left.Modules :=
    SheafOfModules.unit (cover f I V n).left.ringCatSheaf
  let e₁ : moduleSheaf f I V n ≅ (pushforward (c ≫ i)).obj T :=
    Scheme.DirectImageAlgebra.underlyingModuleIso (coverToOriginal f I V n)
  let e₂ : (pushforward (c ≫ i)).obj T ≅ (pushforward i).obj ((pushforward c).obj T) :=
    ((pushforwardComp c i).app T).symm
  let e₃ : coverLevelModule f I V n ≅ (pushforward c).obj T :=
    Scheme.DirectImageAlgebra.underlyingModuleIso c
  exact e₁ ≪≫ e₂ ≪≫ (pushforward i).mapIso e₃.symm

variable (L : X.Modules)

/-- The actual twisting factor is pulled back to the original
closed level before tensoring its original cover module. -/
def coverLevelTwistedModule (n : ℕ) : (level f I n).Modules :=
  tensor (coverLevelModule f I V n)
    ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).obj L)

instance coverLevelTwistedModule_isQuasicoherent [L.IsQuasicoherent] (n : ℕ) :
    (coverLevelTwistedModule f I V L n).IsQuasicoherent := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  have : ((Scheme.Modules.pullback i).obj L).IsQuasicoherent := isQuasicoherent_pullback i L
  exact isQuasicoherent_tensor (coverLevelModule f I V n) ((Scheme.Modules.pullback i).obj L)

/-- The actual projection formula, applied to the constructed level
module, recovers the original twisted ambient cover module. -/
def moduleSheafTwistedLevelIso [L.IsQuasicoherent] (n : ℕ) :
    tensor (moduleSheaf f I V n) L ≅
      (pushforward (Limits.pullback.fst f (baseInclusion I n))).obj
        (coverLevelTwistedModule f I V L n) := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let C : (level f I n).Modules := coverLevelModule f I V n
  let e : moduleSheaf f I V n ≅ (pushforward i).obj C := moduleSheafLevelIso f I V n
  have : IsClosedImmersion i := levelProjection_isClosedImmersion f I n
  exact whiskerRightIso e L ≪≫ affineProjectionFormulaIso i C L

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
