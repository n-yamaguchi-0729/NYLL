/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionLocal
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilyGeometricFiberCartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Actual geometric lifts to the completion colimit

The proved faithfully flat map from the original henselian ring to its
completion colimit supplies a point above every specified field-valued
point. The algebraic closure of its actual residue field gives compatible
ring maps from the original field and the completion colimit. The induced
map of proper geometric fibers retains its original total-space triangle
and is an actual finite-etale pullback equivalence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A field-valued point lifts along a surjective scheme morphism after an
actual extension to an algebraically closed field. -/
theorem exists_algClosed_lift_of_surjective
    {Y Z : Scheme.{u}} (p : Z ⟶ Y) [Surjective p]
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L)
      (β : K →+* L) (v : Spec (CommRingCat.of L) ⟶ Z),
      v ≫ p = Spec.map (CommRingCat.ofHom β) ≫ t := by
  obtain ⟨x, -⟩ := (pullback.fst t p).surjective (IsLocalRing.closedPoint K)
  let L := AlgebraicClosure ((pullback t p).residueField x)
  let ξ : Spec (CommRingCat.of L) ⟶ pullback t p :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback t p).residueField x) L)) ≫
      (pullback t p).fromSpecResidueField x
  let β := (Spec.preimage (ξ ≫ pullback.fst t p)).hom
  have hβ : Spec.map (CommRingCat.ofHom β) = ξ ≫ pullback.fst t p :=
    Spec.map_preimage _
  refine ⟨L, inferInstance, inferInstance, β, ξ ≫ pullback.snd t p, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hβ]

namespace HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

/-- The actual faithfully flat completion base map supplies compatible
geometric ring maps. Neither a prime above the original point nor a lift
to the completion colimit is assumed. -/
theorem exists_completionGeometricLift
    {K : Type u} [Field K] (ψ : A →+* K) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L)
      (β : K →+* L) (α : completionColimit R A →+* L),
      α.comp (completionBaseMap R A).hom = β.comp ψ := by
  have : Surjective (Spec.map (completionBaseMap R A)) :=
    ((flat_and_surjective_SpecMap_iff (completionBaseMap R A)).mpr
      (completionBaseMap_faithfullyFlat R A)).2
  obtain ⟨L, hL, hLc, β, v, hv⟩ := exists_algClosed_lift_of_surjective
    (Spec.map (completionBaseMap R A)) (Spec.map (CommRingCat.ofHom ψ))
  let α : completionColimit R A →+* L := (Spec.preimage v).hom
  have hα : Spec.map (CommRingCat.ofHom α) = v := Spec.map_preimage v
  have hm : Spec.map (CommRingCat.ofHom (α.comp (completionBaseMap R A).hom)) =
      Spec.map (CommRingCat.ofHom (β.comp ψ)) := by
    change Spec.map (completionBaseMap R A ≫ CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β)
    exact (Spec.map_comp (completionBaseMap R A) (CommRingCat.ofHom α)).trans
      ((congrArg (fun a => a ≫ Spec.map (completionBaseMap R A)) hα).trans
        (hv.trans (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)).symm))
  exact ⟨L, hL, hLc, β, α, congrArg CommRingCat.Hom.hom (Spec.map_injective hm)⟩

open EtaleFundamentalGroups.StrictHenselian

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The constructed lift gives the actual geometric fiber comparison of
the original proper family, retaining its Cartesian square, original
total-space projection, and proved finite-etale pullback equivalence. -/
theorem exists_completionFamilyGenericComparison
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (p : Spec (CommRingCat.of A) ⟶ S)
    {K : Type u} [Field K] [IsSepClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (ψ : A →+* K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ p = t) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L)
      (β : K →+* L) (α : completionColimit R A →+* L),
      α.comp (completionBaseMap R A).hom = β.comp ψ ∧
        let q := Spec.map (completionBaseMap R A) ≫ p
        let g := pullback.fst q f
        let γ := Spec.map (CommRingCat.ofHom α)
        ∃ c : pullback γ g ⟶ pullback t f,
          IsPullback c (pullback.fst γ g) (pullback.fst t f)
            (Spec.map (CommRingCat.ofHom β)) ∧
          c ≫ pullback.snd t f = pullback.snd γ g ≫ pullback.snd q f ∧
          (FiniteEtale.pullback c).IsEquivalence := by
  obtain ⟨L, hL, hLc, β, α, hα⟩ := exists_completionGeometricLift R A ψ
  refine ⟨L, hL, hLc, β, α, hα, ?_⟩
  dsimp only
  let q := Spec.map (completionBaseMap R A) ≫ p
  let g := pullback.fst q f
  let γ := Spec.map (CommRingCat.ofHom α)
  have hγ : γ ≫ q = Spec.map (CommRingCat.ofHom β) ≫ t := by
    dsimp only [γ, q]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (α.comp (completionBaseMap R A).hom)) ≫ p = _
    rw [hα]
    change Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β) ≫ p = _
    rw [Spec.map_comp, Category.assoc, hψ]
  have hq : g ≫ q = pullback.snd q f ≫ f := pullback.condition
  have hcart : IsPullback (pullback.snd q f) g f q :=
    (IsPullback.of_hasPullback q f).flip
  let c := familyGeometricFiberMap f g (pullback.snd q f) q hq γ t β hγ
  exact ⟨c,
    familyGeometricFiberMap_isPullback f g (pullback.snd q f) q hq γ t β hγ hcart,
    familyGeometricFiberMap_snd f g (pullback.snd q f) q hq γ t β hγ,
    pullback_familyGeometricFiberMap_isEquivalence
      f g (pullback.snd q f) q hq γ t β hγ hcart⟩

end HenselianNoetherianImageStages
end AlgebraicGeometry
