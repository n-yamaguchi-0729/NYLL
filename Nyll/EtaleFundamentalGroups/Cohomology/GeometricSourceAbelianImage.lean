/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Abelian images of actual geometric source morphisms

Changing the fiber path has no effect after abelianization. Replacing a
connected geometric source by an actual isomorphic scheme over the target,
with any geometric point, preserves the same image subgroup. These statements
refer to the original finite-etale pullback maps.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian

namespace EtaleFundamentalGroups.Cohomology

universe u

variable {U T : Scheme.{u}} {Ω Ξ : Type u} [Field Ω] [Field Ξ]

/-- The actual source morphism followed by a fiber path and the full
topological abelianization map. -/
def geometricSourceAbelianHom (j : T ⟶ U) (xi : Spec (.of Ω) ⟶ T)
    (point : Spec (.of Ξ) ⟶ U) (t : fiber (xi ≫ j) ≅ fiber point) :
    π₁ᵉᵗ(xi) →ₜ* TopologicalAbelianization π₁ᵉᵗ(point) :=
  (TopologicalAbelianization.mkₜ π₁ᵉᵗ(point)).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
      (fundamentalGroupHom j xi))

private theorem map_conj_to_commGroup {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (g a : G) : f (MulAut.conj g a) = f a := by
  change f (g * a * g⁻¹) = f a
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-- Fiber paths have the same original map into the abelianization. -/
theorem geometricSourceAbelianHom_eq (j : T ⟶ U) (xi : Spec (.of Ω) ⟶ T)
    (point : Spec (.of Ξ) ⟶ U) (t₁ t₂ : fiber (xi ≫ j) ≅ fiber point) :
    geometricSourceAbelianHom j xi point t₁ = geometricSourceAbelianHom j xi point t₂ := by
  apply ContinuousMonoidHom.ext
  intro a
  exact ((congrArg (TopologicalAbelianization.mk π₁ᵉᵗ(point))
    (continuousConjAut_eq_conj t₁ t₂ (fundamentalGroupHom j xi a))).trans
    (map_conj_to_commGroup (TopologicalAbelianization.mk π₁ᵉᵗ(point))
      (Aut.of (t₁.symm ≪≫ t₂)) _)).symm

private theorem conjAut_eqToIso_point_eq {S : Scheme.{u}}
    {p q : Spec (.of Ω) ⟶ S} (h : p = q) (a : π₁ᵉᵗ(p)) :
    (eqToIso (congrArg fiber h)).conjAut a = h ▸ a := by
  subst q
  rfl

/-- The source image is invariant under an actual isomorphism over the
target and arbitrary choices of geometric points and fiber paths. -/
theorem geometricSourceAbelianHom_range_eq_of_iso
    {T' : Scheme.{u}} [ConnectedSpace T] [ConnectedSpace T']
    [IsSepClosed Ω] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (j : T ⟶ U) (j' : T' ⟶ U) (e : T' ≅ T) (he : e.hom ≫ j = j')
    (xi : Spec (.of Ω) ⟶ T) (xi' : Spec (.of Ω') ⟶ T')
    (point : Spec (.of Ξ) ⟶ U)
    (t : fiber (xi ≫ j) ≅ fiber point) (t' : fiber (xi' ≫ j') ≅ fiber point) :
    (geometricSourceAbelianHom j' xi' point t').toMonoidHom.range =
      (geometricSourceAbelianHom j xi point t).toMonoidHom.range := by
  subst j'
  let E : FiniteEtale T ≌ FiniteEtale T' :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have : (pullback e.hom).IsEquivalence := E.isEquivalence_functor
  let eπ := fundamentalGroupEquivOfPullbackEquivalence e.hom xi'
  obtain ⟨s⟩ := nonempty_fiber_iso (xi' ≫ e.hom) xi
  let sU := (pullbackFiberIso j (xi' ≫ e.hom)).symm ≪≫
    Functor.isoWhiskerLeft (pullback j) s ≪≫ pullbackFiberIso j xi
  let hpoint : (xi' ≫ e.hom) ≫ j = xi' ≫ (e.hom ≫ j) := Category.assoc xi' e.hom j
  let c := eqToIso (congrArg fiber hpoint)
  let t₀ := c.symm ≪≫ sU ≪≫ t
  have hvalue (a : π₁ᵉᵗ(xi')) :
      geometricSourceAbelianHom (e.hom ≫ j) xi' point t₀ a =
        geometricSourceAbelianHom j xi point t (s.conjAut (eπ a)) := by
    have hcomp : c.conjAut (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a)) =
        fundamentalGroupHom (e.hom ≫ j) xi' a :=
      (conjAut_eqToIso_point_eq hpoint _).trans
        (fundamentalGroupHom_comp_of_eq e.hom j (e.hom ≫ j) rfl xi' hpoint a)
    have hs := fundamentalGroupHom_conjAut j (xi' ≫ e.hom) xi s (eπ a)
    change TopologicalAbelianization.mk π₁ᵉᵗ(point)
        (t₀.conjAut (fundamentalGroupHom (e.hom ≫ j) xi' a)) =
      TopologicalAbelianization.mk π₁ᵉᵗ(point)
        (t.conjAut (fundamentalGroupHom j xi (s.conjAut (eπ a))))
    apply congrArg (TopologicalAbelianization.mk π₁ᵉᵗ(point))
    rw [← hcomp]
    change (c.symm ≪≫ sU ≪≫ t).conjAut
      (c.conjAut (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a))) = _
    rw [Iso.trans_conjAut, Iso.trans_conjAut]
    rw [show c.symm.conjAut (c.conjAut
      (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a))) =
        fundamentalGroupHom j (xi' ≫ e.hom) (eπ a) from
      c.conjAut.symm_apply_apply _]
    exact congrArg t.conjAut hs
  rw [geometricSourceAbelianHom_eq (e.hom ≫ j) xi' point t' t₀]
  apply Subgroup.ext
  intro z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨s.conjAut (eπ a), (hvalue a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := eπ.surjective (s.conjAut.symm a)
    refine ⟨b, (hvalue b).trans ?_⟩
    rw [hb, s.conjAut.apply_symm_apply]
    rfl

end EtaleFundamentalGroups.Cohomology
