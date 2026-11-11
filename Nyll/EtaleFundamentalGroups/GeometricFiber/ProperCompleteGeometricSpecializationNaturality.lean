/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteGeometricSpecializationFunctor
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition

/-!
# Naturality for the constructed geometric specialization

A morphism between proper families over the same chosen complete strict
local base commutes with the already constructed continuous geometric
specialization maps. The path on the target is the actual image of the
chosen path on the source total space. Both geometric pointing fields,
the two actual fiber maps, and both original total-space triangles are
retained. No comparison between unrelated DVR models is asserted.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

private theorem geometric_conjAut_of_point_transports_eq
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x y z : Spec (CommRingCat.of Ω) ⟶ X}
    (hx : x = z) (hy : y = z) (a : π₁ᵉᵗ(x)) (b : π₁ᵉᵗ(y))
    (h : hx ▸ a = hy ▸ b) :
    (eqToIso (congrArg fiber (hx.trans hy.symm))).conjAut a = b := by
  subst z
  subst y
  exact h

/-- The genuine geometric specialization maps commute with a morphism of
proper families over the same complete strict local base. The target path
is explicitly induced by the original family map. -/
theorem properCompleteGeometricSpecializationHom_naturality
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of R)) [IsProper g]
    (a : X ⟶ Y) (ha : a ≫ g = f)
    {k K : Type u} [Field k] [IsSepClosed k] [Field K]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (ι : IsLocalRing.ResidueField R →+* k)
    (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s)) (b : π₁ᵉᵗ(xη)) :
    let qη := properFamilyFiberMap f g a ha η
    let qs := properFamilyFiberMap f g a ha s
    let hsource : (xη ≫ qη) ≫ Limits.pullback.fst g η =
        (xη ≫ Limits.pullback.fst f η) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xη ≫ q) (properFamilyFiberMap_fst f g a ha η)).trans
          (Category.assoc _ _ _).symm)
    let htarget : (xs ≫ qs) ≫ Limits.pullback.fst g s =
        (xs ≫ Limits.pullback.fst f s) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xs ≫ q) (properFamilyFiberMap_fst f g a ha s)).trans
          (Category.assoc _ _ _).symm)
    let ta : fiber ((xη ≫ Limits.pullback.fst f η) ≫ a) ≅
        fiber ((xs ≫ Limits.pullback.fst f s) ≫ a) :=
      (pullbackFiberIso a (xη ≫ Limits.pullback.fst f η)).symm ≪≫
        Functor.isoWhiskerLeft (pullback a) t ≪≫
        pullbackFiberIso a (xs ≫ Limits.pullback.fst f s)
    let tY : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η) ≅
        fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s) :=
      eqToIso (congrArg fiber hsource) ≪≫ ta ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    fundamentalGroupHom qs xs
        (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t b) =
      properCompleteGeometricSpecializationHom R g s ι hs η (xη ≫ qη) (xs ≫ qs) tY
        (fundamentalGroupHom qη xη b) := by
  intro qη qs hsource htarget ta tY
  let eX : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ Limits.pullback.fst f s) :=
    fundamentalGroupEquivProperCompleteGeometricClosedFiber R f s ι hs xs
  let eY : π₁ᵉᵗ(xs ≫ qs) ≃ₜ* π₁ᵉᵗ((xs ≫ qs) ≫ Limits.pullback.fst g s) :=
    fundamentalGroupEquivProperCompleteGeometricClosedFiber R g s ι hs (xs ≫ qs)
  let csource : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η) ≅
      fiber ((xη ≫ Limits.pullback.fst f η) ≫ a) :=
    eqToIso (congrArg fiber hsource)
  let ctarget : fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s) ≅
      fiber ((xs ≫ Limits.pullback.fst f s) ≫ a) :=
    eqToIso (congrArg fiber htarget)
  have hclosed (c : π₁ᵉᵗ(xs)) :
      ctarget.conjAut (eY (fundamentalGroupHom qs xs c)) =
        fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s) (eX c) := by
    dsimp only [eX, eY]
    rw [fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply,
      fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply]
    let hleft : (xs ≫ qs) ≫ Limits.pullback.fst g s =
        xs ≫ Limits.pullback.fst f s ≫ a :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => xs ≫ q) (properFamilyFiberMap_fst f g a ha s))
    let hright : (xs ≫ Limits.pullback.fst f s) ≫ a =
        xs ≫ Limits.pullback.fst f s ≫ a := Category.assoc _ _ _
    exact geometric_conjAut_of_point_transports_eq hleft hright
      (fundamentalGroupHom (Limits.pullback.fst g s) (xs ≫ qs)
        (fundamentalGroupHom qs xs c))
      (fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s)
        (fundamentalGroupHom (Limits.pullback.fst f s) xs c))
      ((fundamentalGroupHom_comp_of_eq qs (Limits.pullback.fst g s)
        (Limits.pullback.fst f s ≫ a) (properFamilyFiberMap_fst f g a ha s).symm
        xs hleft c).trans
        (fundamentalGroupHom_comp_of_eq (Limits.pullback.fst f s) a
          (Limits.pullback.fst f s ≫ a) rfl xs hright c).symm)
  have hgeneric : csource.conjAut
      (fundamentalGroupHom (Limits.pullback.fst g η) (xη ≫ qη)
        (fundamentalGroupHom qη xη b)) =
      fundamentalGroupHom a (xη ≫ Limits.pullback.fst f η)
        (fundamentalGroupHom (Limits.pullback.fst f η) xη b) := by
    let hleft : (xη ≫ qη) ≫ Limits.pullback.fst g η =
        xη ≫ Limits.pullback.fst f η ≫ a :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => xη ≫ q) (properFamilyFiberMap_fst f g a ha η))
    let hright : (xη ≫ Limits.pullback.fst f η) ≫ a =
        xη ≫ Limits.pullback.fst f η ≫ a := Category.assoc _ _ _
    exact geometric_conjAut_of_point_transports_eq hleft hright _ _
      ((fundamentalGroupHom_comp_of_eq qη (Limits.pullback.fst g η)
        (Limits.pullback.fst f η ≫ a) (properFamilyFiberMap_fst f g a ha η).symm
        xη hleft b).trans
        (fundamentalGroupHom_comp_of_eq (Limits.pullback.fst f η) a
          (Limits.pullback.fst f η ≫ a) rfl xη hright b).symm)
  have hpath (c : π₁ᵉᵗ((xη ≫ qη) ≫ Limits.pullback.fst g η)) :
      ctarget.conjAut (tY.conjAut c) = ta.conjAut (csource.conjAut c) := by
    change ctarget.conjAut ((csource ≪≫ ta ≪≫ ctarget.symm).conjAut c) = _
    rw [Iso.trans_conjAut, Iso.trans_conjAut]
    exact ctarget.conjAut.apply_symm_apply _
  apply eY.injective
  apply ctarget.conjAut.injective
  calc
    _ = fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s)
        (eX (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t b)) :=
      hclosed _
    _ = fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s)
        (t.conjAut (fundamentalGroupHom (Limits.pullback.fst f η) xη b)) :=
      congrArg (fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s))
        ((fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply R f s ι hs xs
          (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t b)).trans
          (properCompleteGeometricSpecializationHom_triangle R f s ι hs η xη xs t b))
    _ = ta.conjAut (fundamentalGroupHom a (xη ≫ Limits.pullback.fst f η)
        (fundamentalGroupHom (Limits.pullback.fst f η) xη b)) :=
      (fundamentalGroupHom_conjAut a (xη ≫ Limits.pullback.fst f η)
        (xs ≫ Limits.pullback.fst f s) t
        (fundamentalGroupHom (Limits.pullback.fst f η) xη b)).symm
    _ = ta.conjAut (csource.conjAut
        (fundamentalGroupHom (Limits.pullback.fst g η) (xη ≫ qη)
          (fundamentalGroupHom qη xη b))) := congrArg ta.conjAut hgeneric.symm
    _ = ctarget.conjAut (tY.conjAut
        (fundamentalGroupHom (Limits.pullback.fst g η) (xη ≫ qη)
          (fundamentalGroupHom qη xη b))) := (hpath _).symm
    _ = _ := congrArg ctarget.conjAut
      ((fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply
        R g s ι hs (xs ≫ qs)
        (properCompleteGeometricSpecializationHom R g s ι hs η
          (xη ≫ qη) (xs ≫ qs) tY (fundamentalGroupHom qη xη b))).trans
        (properCompleteGeometricSpecializationHom_triangle R g s ι hs η
          (xη ≫ qη) (xs ≫ qs) tY (fundamentalGroupHom qη xη b))).symm

end AlgebraicGeometry.FiniteEtale
