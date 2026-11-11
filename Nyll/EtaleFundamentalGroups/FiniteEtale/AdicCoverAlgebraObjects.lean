/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraSheafObjectMap

/-!
# Native algebra objects on the actual adic cover modules

The existing canonical algebra-object structure applies to the original
`moduleSheaf`, without changing its underlying sheaf or scalar action.
Its operations are the original cover's operations on inverse-image
opens. The original `moduleTransition` preserves these operations, using
the actual structural triangle of the cover transition.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- Expose the existing canonical monoid through the original module alias. -/
instance moduleSheafMonObj (n : ℕ) : MonObj (moduleSheaf f I V n) :=
  inferInstanceAs
    (MonObj (Scheme.RelativeSpec.underlyingModule (algebraStructure f I V n)))

/-- Expose the same canonical commutative structure through that alias. -/
instance moduleSheafIsCommMonObj (n : ℕ) : IsCommMonObj (moduleSheaf f I V n) :=
  inferInstanceAs
    (IsCommMonObj (Scheme.RelativeSpec.underlyingModule (algebraStructure f I V n)))

/-- The native unit is the actual cover map on the original open. -/
theorem moduleSheaf_one_app (n : ℕ) (U : X.Opens) (r : Γ(X, U)) :
    η[moduleSheaf f I V n].app U r = (coverToOriginal f I V n).app U r :=
  Scheme.RelativeSpec.underlyingModule_one_app (algebraStructure f I V n) U r

/-- The native multiplication is the original cover's ring multiplication
on its actual inverse-image open. -/
theorem moduleSheaf_mul_app (n : ℕ) (U : X.Opens)
    (x y : Γ((cover f I V n).left, coverToOriginal f I V n ⁻¹ᵁ U)) :
    μ[moduleSheaf f I V n].app U (Scheme.Modules.tensorSections x y) = x * y :=
  Scheme.RelativeSpec.underlyingModule_mul_app (algebraStructure f I V n) U x y

/-- The original native transition is a monoid morphism for the canonical
algebra structures. Its two laws are `IsMonHom.one_hom` and `IsMonHom.mul_hom`. -/
instance moduleTransition_isMonHom (n : ℕ) : IsMonHom (moduleTransition f I V n) := by
  change IsMonHom (Scheme.RelativeSpec.underlyingModuleMap
    (algebraStructure f I V (n + 1)) (algebraStructure f I V n)
    (algebraTransition f I V n) (algebraStructure_transition f I V n))
  infer_instance

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
