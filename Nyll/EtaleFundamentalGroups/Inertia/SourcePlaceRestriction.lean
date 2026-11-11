/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.OpenSourceBoundaryPlaces
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FiniteConstantRayReindex
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEqMem
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual generic-source places under finite curve maps

The generic-source square determines the original local-ring coefficient
square. Its inclusion of valuation rings proves the actual restriction of
places. For an actual pullback of an open curve, the resulting place
restriction identifies its reduced boundary modulus with the original
modulus pulled through the field extension, including finite enlargement
of the specified constant field.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] integralOpenDominant

/-- The original generic-source square also commutes on every actual
local ring. Both spectrum maps factor the same original morphism. -/
theorem genericFieldSourceStalkMap_comp
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    {F L : Type} [Field F] [Field L] [Algebra F L]
    (pX : Spec (.of F) ⟶ X) [IsDominant pX] [IsPreimmersion pX]
    (pY : Spec (.of L) ⟶ Y) [IsDominant pY] [IsPreimmersion pY]
    (f : Y ⟶ X)
    (hsource : pY ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ pX)
    (y : Y) :
    let : Algebra (X.presheaf.stalk (f y)) F := genericFieldSourceStalkAlgebra pX (f y)
    let : Algebra (Y.presheaf.stalk y) L := genericFieldSourceStalkAlgebra pY y
    (algebraMap (Y.presheaf.stalk y) L).comp (f.stalkMap y).hom =
      (algebraMap F L).comp (algebraMap (X.presheaf.stalk (f y)) F) := by
  intro algXF algYL
  have hcoeff : CommRingCat.ofHom
      ((algebraMap (Y.presheaf.stalk y) L).comp (f.stalkMap y).hom) =
      CommRingCat.ofHom
        ((algebraMap F L).comp (algebraMap (X.presheaf.stalk (f y)) F)) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (f y))).mp
    change Spec.map (f.stalkMap y ≫
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) L)) ≫ _ =
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (f y)) F) ≫
          CommRingCat.ofHom (algebraMap F L)) ≫ _
    let qY : Spec (.of L) ⟶ Spec (Y.presheaf.stalk y) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) L))
    let qX : Spec (.of F) ⟶ Spec (X.presheaf.stalk (f y)) :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (f y)) F))
    let q : Spec (.of L) ⟶ Spec (.of F) :=
      Spec.map (CommRingCat.ofHom (algebraMap F L))
    have hY : qY ≫ Y.fromSpecStalk y = pY :=
      genericFieldSourceStalkMap_fromSpecStalk pY y
    have hX : qX ≫ X.fromSpecStalk (f y) = pX :=
      genericFieldSourceStalkMap_fromSpecStalk pX (f y)
    have hstalk : Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y) =
        Y.fromSpecStalk y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
    calc
      Spec.map (f.stalkMap y ≫
          CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) L)) ≫
          X.fromSpecStalk (f y) =
          (qY ≫ Spec.map (f.stalkMap y)) ≫ X.fromSpecStalk (f y) :=
        congrArg (fun t : Spec (.of L) ⟶ Spec (X.presheaf.stalk (f y)) =>
          t ≫ X.fromSpecStalk (f y))
          (Spec.map_comp (f.stalkMap y)
            (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) L)))
      _ = qY ≫ (Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y)) :=
        Category.assoc _ _ _
      _ = qY ≫ (Y.fromSpecStalk y ≫ f) := congrArg (fun t => qY ≫ t) hstalk
      _ = (qY ≫ Y.fromSpecStalk y) ≫ f := (Category.assoc _ _ _).symm
      _ = pY ≫ f := congrArg (fun t => t ≫ f) hY
      _ = q ≫ pX := hsource
      _ = q ≫ (qX ≫ X.fromSpecStalk (f y)) := congrArg (fun t => q ≫ t) hX.symm
      _ = (q ≫ qX) ≫ X.fromSpecStalk (f y) := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (f y)) F) ≫
          CommRingCat.ofHom (algebraMap F L)) ≫ X.fromSpecStalk (f y) :=
        congrArg (fun t : Spec (.of L) ⟶ Spec (X.presheaf.stalk (f y)) =>
          t ≫ X.fromSpecStalk (f y))
          (Spec.map_comp
            (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (f y)) F))
            (CommRingCat.ofHom (algebraMap F L))).symm
  exact congrArg CommRingCat.Hom.hom hcoeff

/-- A finite morphism sends each actual closed point to its actual closed
image point. -/
def finiteSourceClosedPoint {X Y : Scheme} (f : Y ⟶ X) [IsFinite f]
    (y : closedPoints Y) : closedPoints X :=
  ⟨f y.val, mem_closedPoints_iff.mpr (by
    simpa only [Set.image_singleton] using
      f.isClosedMap {y.val} (mem_closedPoints_iff.mp y.property))⟩

/-- Restriction of the original valuation ring keeps the actual image
point even when both models use different finite constant fields. No
scalar map between those two chosen constant coordinates is needed. -/
theorem closedPointSourcePlace_restrict_forgetBothConstants
    {k E₁ E₂ F L : Type} [Field k] [Field E₁] [Field E₂] [Field F] [Field L]
    [Algebra k E₁] [Algebra k E₂] [Algebra k F] [Algebra k L]
    [Algebra E₁ F] [Algebra E₂ L] [Algebra F L]
    [IsScalarTower k E₁ F] [IsScalarTower k E₂ L]
    [IsScalarTower k F L] [Algebra.IsIntegral F L]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (cX : X ⟶ Spec (.of E₁)) [SmoothOfRelativeDimension 1 cX]
    (cY : Y ⟶ Spec (.of E₂)) [SmoothOfRelativeDimension 1 cY]
    (pX : Spec (.of F) ⟶ X) [IsDominant pX] [IsPreimmersion pX]
    (hpX : pX ≫ cX = Spec.map (CommRingCat.ofHom (algebraMap E₁ F)))
    (pY : Spec (.of L) ⟶ Y) [IsDominant pY] [IsPreimmersion pY]
    (hpY : pY ≫ cY = Spec.map (CommRingCat.ofHom (algebraMap E₂ L)))
    (f : Y ⟶ X) [IsFinite f]
    (hsource : pY ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ pX)
    (y : closedPoints Y) :
    ((closedPointSourcePlace cY pY hpY y).forgetConstants (K := k)).restrict F =
      (closedPointSourcePlace cX pX hpX (finiteSourceClosedPoint f y)).forgetConstants
        (K := k) := by
  let x := finiteSourceClosedPoint f y
  let : Algebra (X.presheaf.stalk x.val) F := genericFieldSourceStalkAlgebra pX x.val
  let : Algebra (Y.presheaf.stalk y.val) L := genericFieldSourceStalkAlgebra pY y.val
  apply Place.restrict_eq_of_forall_mem
  intro a ha
  change a ∈ (closedPointSourcePlace cX pX hpX x).toValuationSubring.toSubring at ha
  have ha' : a ∈ (algebraMap (X.presheaf.stalk x.val) F).range := by
    rw [closedPointSourcePlace_range cX pX hpX x]
    exact ha
  obtain ⟨b, rfl⟩ := ha'
  change algebraMap F L (algebraMap (X.presheaf.stalk x.val) F b) ∈
    (closedPointSourcePlace cY pY hpY y).toValuationSubring.toSubring
  rw [← closedPointSourcePlace_range cY pY hpY y]
  exact ⟨(f.stalkMap y.val).hom b,
    RingHom.congr_fun (genericFieldSourceStalkMap_comp pX pY f hsource y.val) b⟩

/-- Restriction of the actual source-field place is the place of the
actual image point, with any larger finite constants forgotten first. -/
theorem closedPointSourcePlace_restrict_forgetConstants
    {k E F L : Type} [Field k] [Field E] [Field F] [Field L]
    [Algebra k E] [Algebra k F] [Algebra k L] [Algebra E L] [Algebra F L]
    [IsScalarTower k E L] [IsScalarTower k F L] [Algebra.IsIntegral F L]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (cX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 cX]
    (cY : Y ⟶ Spec (.of E)) [SmoothOfRelativeDimension 1 cY]
    (pX : Spec (.of F) ⟶ X) [IsDominant pX] [IsPreimmersion pX]
    (hpX : pX ≫ cX = Spec.map (CommRingCat.ofHom (algebraMap k F)))
    (pY : Spec (.of L) ⟶ Y) [IsDominant pY] [IsPreimmersion pY]
    (hpY : pY ≫ cY = Spec.map (CommRingCat.ofHom (algebraMap E L)))
    (f : Y ⟶ X) [IsFinite f]
    (hsource : pY ≫ f = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ pX)
    (y : closedPoints Y) :
    ((closedPointSourcePlace cY pY hpY y).forgetConstants (K := k)).restrict F =
      closedPointSourcePlace cX pX hpX (finiteSourceClosedPoint f y) :=
  (closedPointSourcePlace_restrict_forgetBothConstants cX cY pX hpX pY hpY f hsource y).trans
    (Place.ext rfl)

section BoundaryPullback

variable {k E F L : Type} [Field k] [Field E] [Field F] [Field L]
  [Algebra k E] [Algebra k F] [Algebra k L] [Algebra E L] [Algebra F L]
  [IsScalarTower k E L] [IsScalarTower k F L] [Algebra.IsIntegral k E]
  [FiniteDimensional F L]
  {X U Y V : Scheme} [IsIntegral X] [IsIntegral U] [IsIntegral Y] [IsIntegral V]
  (cX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 cX] [IsProper cX]
  (cY : Y ⟶ Spec (.of E)) [SmoothOfRelativeDimension 1 cY] [IsProper cY]
  (jX : U ⟶ X) [IsOpenImmersion jX] (jY : V ⟶ Y) [IsOpenImmersion jY]
  (pX : Spec (.of F) ⟶ U) [IsDominant pX] [IsPreimmersion pX]
  (hpX : pX ≫ (jX ≫ cX) = Spec.map (CommRingCat.ofHom (algebraMap k F)))
  (pY : Spec (.of L) ⟶ V) [IsDominant pY] [IsPreimmersion pY]
  (hpY : pY ≫ (jY ≫ cY) = Spec.map (CommRingCat.ofHom (algebraMap E L)))
  (f : Y ⟶ X) [IsFinite f] (g : V ⟶ U)
  (hcart : IsPullback jY g f jX)
  (hsource : pY ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫ pX)

include hcart hsource in
omit [Algebra.IsIntegral k E] in
/-- The point-place correspondence in the actual compactification keeps
the literal restriction of source fields through the actual pullback. -/
theorem genericSourcePlaceEquiv_restrict_pullback (y : closedPoints Y) :
    ((genericSourcePlaceEquiv cY jY pY hpY y).forgetConstants (K := k)).restrict F =
      genericSourcePlaceEquiv cX jX pX hpX (finiteSourceClosedPoint f y) := by
  apply closedPointSourcePlace_restrict_forgetConstants
    cX cY (pX ≫ jX) ((Category.assoc pX jX cX).trans hpX)
    (pY ≫ jY) ((Category.assoc pY jY cY).trans hpY) f
  rw [Category.assoc, hcart.w, ← Category.assoc, hsource, Category.assoc]

include hcart in
omit [IsIntegral X] [IsIntegral U] [IsIntegral Y] [IsIntegral V]
  [IsOpenImmersion jY] [IsFinite f] in
private theorem range_pullbackOpen : Set.range jY = f ⁻¹' Set.range jX := by
  calc
    Set.range jY = Set.range (Limits.pullback.fst f jX) := by
      rw [← hcart.isoPullback_hom_fst]
      change Set.range ((Limits.pullback.fst f jX) ∘ hcart.isoPullback.hom) = _
      have hsurj : Function.Surjective hcart.isoPullback.hom := fun z =>
        ⟨hcart.isoPullback.inv z, Scheme.inv_hom_apply hcart.isoPullback z⟩
      exact hsurj.range_comp (Limits.pullback.fst f jX)
    _ = f ⁻¹' Set.range jX := IsOpenImmersion.range_pullbackFst jX f

include hcart hsource in
omit [Algebra.IsIntegral k E] in
/-- The actual boundary places upstairs are exactly those whose original
restriction lies in the original boundary. -/
theorem genericSourceBoundaryPlaces_restrict_pullback (w : Place E L) :
    w ∈ genericSourceBoundaryPlaces cY jY pY hpY ↔
      (w.forgetConstants (K := k)).restrict F ∈ genericSourceBoundaryPlaces cX jX pX hpX := by
  obtain ⟨y, rfl⟩ := (genericSourcePlaceEquiv cY jY pY hpY).surjective w
  rw [genericSourcePlaceEquiv_restrict_pullback cX cY jX jY pX hpX pY hpY f g hcart hsource,
    genericSourcePlaceEquiv_mem_boundary_iff, genericSourcePlaceEquiv_mem_boundary_iff,
    range_pullbackOpen jX jY f g hcart]
  rfl

include hcart hsource in
/-- The reduced modulus of the actual pulled-back curve, after forgetting
finite constants, is exactly the original field-extension modulus. -/
theorem genericSourceBoundaryModulus_pullback :
    FunctionField.RayClass.modulusForgetConstants k E L
        (genericSourceBoundaryModulus cY jY pY hpY) =
      FunctionField.RayClass.rayModulusBaseChange L
        (genericSourceBoundaryModulus cX jX pX hpX) := by
  classical
  apply Finsupp.ext
  intro v
  rw [FunctionField.RayClass.modulusForgetConstants_apply,
    FunctionField.RayClass.rayModulusBaseChange_apply,
    genericSourceBoundaryModulus_apply, genericSourceBoundaryModulus_apply,
    genericSourceBoundaryPlaces_restrict_pullback cX cY jX jY pX hpX pY hpY f g hcart hsource]
  have hv : (v.extendConstants E).forgetConstants (K := k) = v := Place.ext rfl
  rw [hv]

end BoundaryPullback

end EtaleFundamentalGroups.Inertia
