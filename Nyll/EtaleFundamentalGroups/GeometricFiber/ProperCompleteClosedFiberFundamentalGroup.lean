/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperCompleteFiniteEtale
public import Nyll.EtaleFundamentalGroups.GaloisCategories.EquivalenceFunctoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-!
# Proper complete-local comparison of fundamental groups

The actual closed-fiber pullback equivalence gives an isomorphism on
fundamental groups whose forward map is the original closed-fiber morphism.
The construction commutes with morphisms of the original proper schemes.
The base remains complete Noetherian local; general henselian comparison
requires its separate essential-surjectivity theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  {Ω : Type u} [Field Ω]

/-- The actual closed-fiber projection induces a continuous group
isomorphism. At a geometric point these are the étale fundamental groups. -/
def fundamentalGroupEquivProperCompleteClosedFiber
    (xi : Spec (CommRingCat.of Ω) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
  let i := Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have : (FiniteEtale.pullback i).IsEquivalence :=
    pullback_isEquivalence_closedFiber_of_isProper_of_isAdicComplete R f
  exact CategoryTheory.PreGaloisCategory.autEquivOfCompIsoOfEquivalence
    (FiniteEtale.pullback i) (pullbackFiberIso i xi)

/-- The forward map is literally the homomorphism induced by the original
closed-fiber projection, rather than an independently chosen isomorphism. -/
theorem fundamentalGroupEquivProperCompleteClosedFiber_apply
    (xi : Spec (CommRingCat.of Ω) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivProperCompleteClosedFiber R f xi a =
      fundamentalGroupHom
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
        xi a := rfl

/-- The comparison commutes with a morphism of the original proper
families; both paths retain their specified geometric basepoints. -/
theorem fundamentalGroupEquivProperCompleteClosedFiber_naturality
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of R)) [IsProper fY]
    (g : X ⟶ Y) (hg : g ≫ fY = f)
    (xi : Spec (CommRingCat.of Ω) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (a : π₁ᵉᵗ(xi)) :
    let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let pX : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
    let pY : Limits.pullback fY i ⟶ Y := Limits.pullback.fst fY i
    let g₀ : Limits.pullback f i ⟶ Limits.pullback fY i :=
      Limits.pullback.lift (pX ≫ g) (Limits.pullback.snd f i)
        ((Category.assoc pX g fY).trans
          ((congrArg (fun k => pX ≫ k) hg).trans Limits.pullback.condition))
    let hleft : (xi ≫ g₀) ≫ pY = xi ≫ pX ≫ g :=
      (Category.assoc xi g₀ pY).trans
        (congrArg (fun k => xi ≫ k) (Limits.pullback.lift_fst _ _ _))
    let hright : (xi ≫ pX) ≫ g = xi ≫ pX ≫ g := Category.assoc xi pX g
    hleft ▸ fundamentalGroupEquivProperCompleteClosedFiber R fY (xi ≫ g₀)
        (fundamentalGroupHom g₀ xi a) =
      hright ▸ fundamentalGroupHom g (xi ≫ pX)
        (fundamentalGroupEquivProperCompleteClosedFiber R f xi a) := by
  intro i pX pY g₀ hleft hright
  rw [fundamentalGroupEquivProperCompleteClosedFiber_apply,
    fundamentalGroupEquivProperCompleteClosedFiber_apply]
  have hm : pX ≫ g = g₀ ≫ pY := (Limits.pullback.lift_fst _ _ _).symm
  exact (fundamentalGroupHom_comp_of_eq g₀ pY (pX ≫ g) hm xi hleft a).trans
    (fundamentalGroupHom_comp_of_eq pX g (pX ≫ g) rfl xi hright a).symm


/-- Specialization to the closed fiber over a complete local base, with
its chosen path on the total space. For a generic fiber, `j` is the actual
generic-fiber projection. -/
def properCompleteSpecializationHom
    {T : Scheme.{u}} (j : T ⟶ X) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t : fiber (xi ≫ j) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :
    π₁ᵉᵗ(xi) →ₜ* π₁ᵉᵗ(xs) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (fundamentalGroupEquivProperCompleteClosedFiber R f xs).symm).comp
      ((ContinuousMonoidHom.toContinuousMonoidHom
        (CategoryTheory.PreGaloisCategory.continuousConjAut t)).comp
          (fundamentalGroupHom j xi))

/-- The specialization map has the required triangle with the original
total space and the specified path. -/
theorem properCompleteSpecializationHom_triangle
    {T : Scheme.{u}} (j : T ⟶ X) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t : fiber (xi ≫ j) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupHom
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) xs
        (properCompleteSpecializationHom R f j xi xs t a) =
      CategoryTheory.PreGaloisCategory.continuousConjAut t (fundamentalGroupHom j xi a) := by
  let e := fundamentalGroupEquivProperCompleteClosedFiber R f xs
  change e (e.symm (CategoryTheory.PreGaloisCategory.continuousConjAut t
    (fundamentalGroupHom j xi a))) = _
  exact e.apply_symm_apply _

/-- For a connected proper total space the required path exists; hence
specialization and its triangle are obtained without assuming a comparison
of the two fiber functors. -/
theorem exists_properCompleteSpecializationHom [ConnectedSpace X] [IsSepClosed Ω]
    {T : Scheme.{u}} (j : T ⟶ X) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    ∃ t : fiber (xi ≫ j) ≅ fiber (xs ≫
        Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))),
      ∃ sp : π₁ᵉᵗ(xi) →ₜ* π₁ᵉᵗ(xs), ∀ a : π₁ᵉᵗ(xi),
        fundamentalGroupHom
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
            xs (sp a) =
          CategoryTheory.PreGaloisCategory.continuousConjAut t
            (fundamentalGroupHom j xi a) := by
  obtain ⟨t⟩ := nonempty_fiber_iso (xi ≫ j)
    (xs ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact ⟨t, properCompleteSpecializationHom R f j xi xs t,
    properCompleteSpecializationHom_triangle R f j xi xs t⟩

end AlgebraicGeometry.FiniteEtale
