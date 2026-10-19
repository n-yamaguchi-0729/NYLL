/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardFunctor
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The fppf sheaf of modulus-rigidified line-bundle classes

Sheafification is applied to the presheaf of actual chosen rigidifications and
compatible isomorphisms. The sheafification exists canonically in the universe
of these classes. No sheaf condition on the naive presheaf, rational point,
or representability assumption is needed.

For empty modulus this construction still performs sheafification; it does not
identify the naive classes with a relative Picard scheme's points. The local
image and equality results specify the relationship with actual bundles.
-/

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The fppf sheafification of compatible-isomorphism classes with a chosen
trivialization on the full modulus. -/
def modulusPicardSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).obj
    (modulusPicardPresheaf c i)

/-- Send an actual chosen-rigidified bundle class to its fppf sheaf class. -/
def toModulusPicardSheaf : modulusPicardPresheaf c i ⟶ (modulusPicardSheaf c i).obj :=
  CategoryTheory.toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusPicardPresheaf c i)

/-- Every section of the sheaf is fppf locally represented by a chosen-rigidified bundle. -/
instance toModulusPicardSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (toModulusPicardSheaf c i) :=
  inferInstanceAs (Presheaf.IsLocallySurjective
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (CategoryTheory.toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardPresheaf c i)))

/-- Equality of sheaf classes of actual bundles is witnessed fppf locally. -/
instance toModulusPicardSheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (toModulusPicardSheaf c i) :=
  inferInstanceAs (Presheaf.IsLocallyInjective
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (CategoryTheory.toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardPresheaf c i)))

/-- The sieve of local representatives of a sheaf section is an fppf covering sieve. -/
theorem modulusPicardSheaf_localRepresentatives {T : Over (Spec (CommRingCat.of R))}
    (x : (modulusPicardSheaf c i).obj.obj (op T)) :
    Presheaf.imageSieve (toModulusPicardSheaf c i) x ∈
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) T :=
  Presheaf.imageSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (toModulusPicardSheaf c i) x

/-- Two actual classes identified by sheafification agree on an fppf covering sieve;
equality of the original classes uses compatible isomorphisms. -/
theorem modulusPicardSheaf_localEquality {T : Over (Spec (CommRingCat.of R))}
    (x y : (modulusPicardPresheaf c i).obj (op T))
    (h : (toModulusPicardSheaf c i).app (op T) x =
      (toModulusPicardSheaf c i).app (op T) y) :
    Presheaf.equalizerSieve (F := modulusPicardPresheaf c i) x y ∈
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) T :=
  Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (toModulusPicardSheaf c i) x y h

variable {c i}

/-- A natural map from actual classes into an fppf sheaf extends uniquely to
the sheafification. -/
def modulusPicardSheafLift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))}
    (a : modulusPicardPresheaf c i ⟶ Q.obj) : modulusPicardSheaf c i ⟶ Q :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).homEquiv (modulusPicardPresheaf c i) Q).symm a

@[reassoc] theorem toModulusPicardSheaf_lift
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))}
    (a : modulusPicardPresheaf c i ⟶ Q.obj) :
    toModulusPicardSheaf c i ≫ (modulusPicardSheafLift a).hom = a :=
  CategoryTheory.toSheafify_sheafifyLift
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) a Q.property

theorem modulusPicardSheafLift_unique
    {Q : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))}
    (a : modulusPicardPresheaf c i ⟶ Q.obj) (g : modulusPicardSheaf c i ⟶ Q)
    (h : toModulusPicardSheaf c i ≫ g.hom = a) : g = modulusPicardSheafLift a := by
  apply Sheaf.hom_ext
  exact CategoryTheory.sheafifyLift_unique
    (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) a Q.property g.hom h

end AlgebraicGeometry.GeneralizedJacobian
