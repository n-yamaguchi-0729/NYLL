/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Mathlib.CategoryTheory.EqToHom

/-!
# The actual isomorphism on a fixed reduced component

The original component isomorphism becomes an automorphism of the
same original reduced component when its actual image component is
fixed. The equality transport retains the original inclusion and
therefore retains every actual semilinearity square on the base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

private theorem component_eqToHom_ι {Z W : irreducibleComponents X} (h : Z = W) :
    eqToHom (congrArg (fun U : irreducibleComponents X =>
      X.reducedIrreducibleComponent U.1 U.2) h) ≫ X.reducedIrreducibleComponentι W.1 W.2 =
        X.reducedIrreducibleComponentι Z.1 Z.2 := by
  subst W
  rw [eqToHom_refl, Category.id_comp]

/-- The original component isomorphism, transported along the actual
equality of its image component with its source component. -/
def reducedIrreducibleFixedComponentIso (e : X ≅ X) (Z : irreducibleComponents X)
    (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    X.reducedIrreducibleComponent Z.1 Z.2 ≅ X.reducedIrreducibleComponent Z.1 Z.2 :=
  (reducedIrreducibleComponentIso e Z).trans
    (eqToIso (congrArg (fun U : irreducibleComponents X =>
      X.reducedIrreducibleComponent U.1 U.2) hZ))

/-- Equality transport does not change the actual inclusion square. -/
theorem reducedIrreducibleFixedComponentIso_hom_ι (e : X ≅ X)
    (Z : irreducibleComponents X) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    (reducedIrreducibleFixedComponentIso e Z hZ).hom ≫
        X.reducedIrreducibleComponentι Z.1 Z.2 =
      X.reducedIrreducibleComponentι Z.1 Z.2 ≫ e.hom := by
  change ((reducedIrreducibleComponentIso e Z).hom ≫
    eqToHom (congrArg (fun U : irreducibleComponents X =>
      X.reducedIrreducibleComponent U.1 U.2) hZ)) ≫
    X.reducedIrreducibleComponentι Z.1 Z.2 =
      X.reducedIrreducibleComponentι Z.1 Z.2 ≫ e.hom
  rw [Category.assoc, component_eqToHom_ι hZ, reducedIrreducibleComponentIso_hom_ι]

/-- The actual fixed-component automorphism has the same base
semilinearity as the original scheme automorphism. -/
theorem reducedIrreducibleFixedComponentIso_toBase (e : X ≅ X)
    (Z : irreducibleComponents X) (hZ : irreducibleComponentsIsoEquiv e Z = Z)
    {S : Scheme.{u}} (c : X ⟶ S) (a : S ⟶ S) (hc : e.hom ≫ c = c ≫ a) :
    (reducedIrreducibleFixedComponentIso e Z hZ).hom ≫
        (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) =
      (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) ≫ a := by
  rw [← Category.assoc, reducedIrreducibleFixedComponentIso_hom_ι,
    Category.assoc, hc, ← Category.assoc]

end AlgebraicGeometry.Scheme
