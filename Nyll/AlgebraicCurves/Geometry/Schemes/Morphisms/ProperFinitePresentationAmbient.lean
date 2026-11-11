/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.FiniteTypeFinitePresentationAmbient
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ProperClosedFinitePresentationThickening
public import Mathlib.Algebra.Ring.ULift

/-!
# A proper finite-presentation ambient for an arbitrary proper scheme

First construct a separated finite-presentation ambient for the actual
proper scheme. The finite-subideal thickening theorem then supplies a
proper closed thickening inside that ambient. The source and its original
structure morphism are retained by the canonical image and ideal inclusion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-- Every proper scheme over an arbitrary ring embeds as a closed subscheme
of a proper finitely presented scheme over the same ring. The embedding
retains the original scheme and factors its original structure morphism. -/
theorem exists_proper_finitePresentation_ambient
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧ i ≫ g = f := by
  let : Algebra (ULift.{u} ℤ) R :=
    ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
  obtain ⟨Y, i, g, hi, hgqc, hgsep, hgfp, hig⟩ := exists_finitePresentation_ambient f
  have : IsClosedImmersion i := hi
  have : QuasiCompact g := hgqc
  have : IsSeparated g := hgsep
  have : LocallyOfFinitePresentation g := hgfp
  let I := i.ker
  have hIg : I.subschemeι ≫ g = inv i.toImage ≫ f := by
    apply (cancel_epi i.toImage).mp
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hig, IsIso.hom_inv_id_assoc]
  have : IsProper (I.subschemeι ≫ g) :=
    hIg.symm ▸ inferInstanceAs (IsProper (inv i.toImage ≫ f))
  obtain ⟨J, hJ⟩ := exists_proper_finiteSubideal_of_finitePresentation (ULift.{u} ℤ) g I
  have : LocallyOfFinitePresentation J.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg J.1 J.2.2
  let i' : X ⟶ J.1.subscheme := i.toImage ≫ inclusion J.2.1
  refine ⟨J.1.subscheme, i', J.1.subschemeι ≫ g,
    inferInstance, hJ, inferInstance, ?_⟩
  change (i.toImage ≫ inclusion J.2.1) ≫ (J.1.subschemeι ≫ g) = f
  rw [Category.assoc, ← Category.assoc (inclusion J.2.1), inclusion_subschemeι,
    ← Category.assoc, Scheme.Hom.toImage_imageι, hig]

end AlgebraicGeometry
