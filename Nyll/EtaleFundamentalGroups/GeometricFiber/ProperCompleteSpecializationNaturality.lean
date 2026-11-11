/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompleteClosedFiberFundamentalGroup
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension

/-!
# Paths and naturality for complete-local proper specialization

Changing the chosen path conjugates specialization by the actual inverse
image of the path difference under the closed-fibre comparison. A morphism
of proper families induces the target path by pullback of covers; the
specialization square then commutes with that constructed path.

The base is complete Noetherian local. No assertion about independence of
a completion or a DVR model is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

private theorem mulEquiv_conj {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g a : G) :
    e (MulAut.conj g a) = MulAut.conj (e g) (e a) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem conjAut_of_point_transports_eq
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x y z : Spec (CommRingCat.of Ω) ⟶ X}
    (hx : x = z) (hy : y = z) (a : π₁ᵉᵗ(x)) (b : π₁ᵉᵗ(y))
    (h : hx ▸ a = hy ▸ b) :
    (eqToIso (congrArg fiber (hx.trans hy.symm))).conjAut a = b := by
  subst z
  subst y
  exact h

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  {Ω : Type u} [Field Ω]

/-- The change of path acts by the explicit inner conjugation in the
original closed-fibre fundamental group. -/
theorem properCompleteSpecializationHom_path_change
    {T : Scheme.{u}} (j : T ⟶ X) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t₁ t₂ : fiber (xi ≫ j) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (a : π₁ᵉᵗ(xi)) :
    properCompleteSpecializationHom R f j xi xs t₂ a =
      MulAut.conj
        ((fundamentalGroupEquivProperCompleteClosedFiber R f xs).symm (Aut.of (t₁.symm ≪≫ t₂)))
        (properCompleteSpecializationHom R f j xi xs t₁ a) := by
  let e := fundamentalGroupEquivProperCompleteClosedFiber R f xs
  change e.symm (continuousConjAut t₂ (fundamentalGroupHom j xi a)) =
    MulAut.conj (e.symm (Aut.of (t₁.symm ≪≫ t₂)))
      (e.symm (continuousConjAut t₁ (fundamentalGroupHom j xi a)))
  exact (congrArg e.symm
    (continuousConjAut_eq_conj t₁ t₂ (fundamentalGroupHom j xi a))).trans
      (mulEquiv_conj e.symm.toMulEquiv (Aut.of (t₁.symm ≪≫ t₂))
        (continuousConjAut t₁ (fundamentalGroupHom j xi a)))

/-- Naturality through a commuting map of the two native closed fibers.
Both closed-fiber comparisons are supplied by the complete-local theorem. -/
theorem properCompleteSpecializationHom_naturality_of_closedFiberMap
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A)) [IsProper fY]
    (g : X ⟶ Y)
    (g₀ : Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶
      Limits.pullback fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (hclosedMap : g₀ ≫
        Limits.pullback.fst fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) =
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g)
    {T U : Scheme.{u}} (jX : T ⟶ X) (jY : U ⟶ Y) (q : T ⟶ U)
    (hq : q ≫ jY = jX ≫ g) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t : fiber (xi ≫ jX) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (a : π₁ᵉᵗ(xi)) :
    let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let pX : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
    let pY := Limits.pullback.fst fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    let hsource : (xi ≫ q) ≫ jY = (xi ≫ jX) ≫ g :=
      (Category.assoc xi q jY).trans
        ((congrArg (fun k => xi ≫ k) hq).trans (Category.assoc xi jX g).symm)
    let htarget : (xs ≫ g₀) ≫ pY = (xs ≫ pX) ≫ g :=
      (Category.assoc xs g₀ pY).trans
        ((congrArg (fun k => xs ≫ k) hclosedMap).trans
          (Category.assoc xs pX g).symm)
    let tg : fiber ((xi ≫ jX) ≫ g) ≅ fiber ((xs ≫ pX) ≫ g) :=
      (pullbackFiberIso g (xi ≫ jX)).symm ≪≫
        Functor.isoWhiskerLeft (pullback g) t ≪≫ pullbackFiberIso g (xs ≫ pX)
    let tY : fiber ((xi ≫ q) ≫ jY) ≅ fiber ((xs ≫ g₀) ≫ pY) :=
      eqToIso (congrArg fiber hsource) ≪≫ tg ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    fundamentalGroupHom g₀ xs (properCompleteSpecializationHom R f jX xi xs t a) =
      properCompleteSpecializationHom A fY jY (xi ≫ q) (xs ≫ g₀) tY
        (fundamentalGroupHom q xi a) := by
  intro i pX pY hsource htarget tg tY
  let eX : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ pX) :=
    fundamentalGroupEquivProperCompleteClosedFiber R f xs
  let eY : π₁ᵉᵗ(xs ≫ g₀) ≃ₜ* π₁ᵉᵗ((xs ≫ g₀) ≫ pY) :=
    fundamentalGroupEquivProperCompleteClosedFiber A fY (xs ≫ g₀)
  let csource : fiber ((xi ≫ q) ≫ jY) ≅ fiber ((xi ≫ jX) ≫ g) :=
    eqToIso (congrArg fiber hsource)
  let ctarget : fiber ((xs ≫ g₀) ≫ pY) ≅ fiber ((xs ≫ pX) ≫ g) :=
    eqToIso (congrArg fiber htarget)
  have hclosed (b : π₁ᵉᵗ(xs)) :
      ctarget.conjAut (eY (fundamentalGroupHom g₀ xs b)) =
        fundamentalGroupHom g (xs ≫ pX) (eX b) := by
    dsimp only [eX, eY]
    rw [fundamentalGroupEquivProperCompleteClosedFiber_apply,
      fundamentalGroupEquivProperCompleteClosedFiber_apply]
    let hleft : (xs ≫ g₀) ≫ pY = xs ≫ pX ≫ g :=
      (Category.assoc xs g₀ pY).trans
        (congrArg (fun k => xs ≫ k) hclosedMap)
    let hright : (xs ≫ pX) ≫ g = xs ≫ pX ≫ g := Category.assoc xs pX g
    exact conjAut_of_point_transports_eq hleft hright
      (fundamentalGroupHom pY (xs ≫ g₀) (fundamentalGroupHom g₀ xs b))
      (fundamentalGroupHom g (xs ≫ pX) (fundamentalGroupHom pX xs b))
      ((fundamentalGroupHom_comp_of_eq g₀ pY (pX ≫ g) hclosedMap.symm xs hleft b).trans
        (fundamentalGroupHom_comp_of_eq pX g (pX ≫ g) rfl xs hright b).symm)
  have hgeneric : csource.conjAut
      (fundamentalGroupHom jY (xi ≫ q) (fundamentalGroupHom q xi a)) =
        fundamentalGroupHom g (xi ≫ jX) (fundamentalGroupHom jX xi a) := by
    let hleft : (xi ≫ q) ≫ jY = xi ≫ jX ≫ g :=
      (Category.assoc xi q jY).trans (congrArg (fun k => xi ≫ k) hq)
    let hright : (xi ≫ jX) ≫ g = xi ≫ jX ≫ g := Category.assoc xi jX g
    exact conjAut_of_point_transports_eq hleft hright
      (fundamentalGroupHom jY (xi ≫ q) (fundamentalGroupHom q xi a))
      (fundamentalGroupHom g (xi ≫ jX) (fundamentalGroupHom jX xi a))
      ((fundamentalGroupHom_comp_of_eq q jY (jX ≫ g) hq.symm xi hleft a).trans
        (fundamentalGroupHom_comp_of_eq jX g (jX ≫ g) rfl xi hright a).symm)
  have heX : eX (properCompleteSpecializationHom R f jX xi xs t a) =
      t.conjAut (fundamentalGroupHom jX xi a) :=
    (fundamentalGroupEquivProperCompleteClosedFiber_apply R f xs
      (properCompleteSpecializationHom R f jX xi xs t a)).trans
        (properCompleteSpecializationHom_triangle R f jX xi xs t a)
  have heY : eY (properCompleteSpecializationHom A fY jY (xi ≫ q) (xs ≫ g₀) tY
      (fundamentalGroupHom q xi a)) =
        tY.conjAut (fundamentalGroupHom jY (xi ≫ q) (fundamentalGroupHom q xi a)) :=
    (fundamentalGroupEquivProperCompleteClosedFiber_apply A fY (xs ≫ g₀)
      (properCompleteSpecializationHom A fY jY (xi ≫ q) (xs ≫ g₀) tY
        (fundamentalGroupHom q xi a))).trans
        (properCompleteSpecializationHom_triangle A fY jY (xi ≫ q) (xs ≫ g₀) tY
          (fundamentalGroupHom q xi a))
  have hpath (b : π₁ᵉᵗ((xi ≫ q) ≫ jY)) :
      ctarget.conjAut (tY.conjAut b) = tg.conjAut (csource.conjAut b) := by
    change ctarget.conjAut ((csource ≪≫ tg ≪≫ ctarget.symm).conjAut b) = _
    rw [Iso.trans_conjAut, Iso.trans_conjAut]
    exact ctarget.conjAut.apply_symm_apply _
  apply eY.injective
  apply ctarget.conjAut.injective
  calc
    _ = fundamentalGroupHom g (xs ≫ pX)
        (eX (properCompleteSpecializationHom R f jX xi xs t a)) := hclosed _
    _ = fundamentalGroupHom g (xs ≫ pX)
        (t.conjAut (fundamentalGroupHom jX xi a)) :=
      congrArg (fundamentalGroupHom g (xs ≫ pX)) heX
    _ = tg.conjAut
        (fundamentalGroupHom g (xi ≫ jX) (fundamentalGroupHom jX xi a)) :=
      (fundamentalGroupHom_conjAut g (xi ≫ jX) (xs ≫ pX) t
        (fundamentalGroupHom jX xi a)).symm
    _ = tg.conjAut (csource.conjAut
        (fundamentalGroupHom jY (xi ≫ q) (fundamentalGroupHom q xi a))) :=
      congrArg tg.conjAut hgeneric.symm
    _ = ctarget.conjAut (tY.conjAut
        (fundamentalGroupHom jY (xi ≫ q) (fundamentalGroupHom q xi a))) :=
      (hpath _).symm
    _ = _ := congrArg ctarget.conjAut heY.symm

/-- A morphism of proper families carries specialization to specialization
for the path induced on the target total space. The closed-fibre map is
the actual pullback map; the generic square may in particular be the
actual geometric-fibre square of the family morphism. -/
theorem properCompleteSpecializationHom_naturality
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of R)) [IsProper fY]
    (g : X ⟶ Y) (hg : g ≫ fY = f)
    {T U : Scheme.{u}} (jX : T ⟶ X) (jY : U ⟶ Y) (q : T ⟶ U)
    (hq : q ≫ jY = jX ≫ g) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t : fiber (xi ≫ jX) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (a : π₁ᵉᵗ(xi)) :
    let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let pX : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
    let pY : Limits.pullback fY i ⟶ Y := Limits.pullback.fst fY i
    let g₀ : Limits.pullback f i ⟶ Limits.pullback fY i :=
      Limits.pullback.lift (pX ≫ g) (Limits.pullback.snd f i)
        ((Category.assoc pX g fY).trans
          ((congrArg (fun k => pX ≫ k) hg).trans Limits.pullback.condition))
    let hsource : (xi ≫ q) ≫ jY = (xi ≫ jX) ≫ g :=
      (Category.assoc xi q jY).trans
        ((congrArg (fun k => xi ≫ k) hq).trans (Category.assoc xi jX g).symm)
    let htarget : (xs ≫ g₀) ≫ pY = (xs ≫ pX) ≫ g :=
      (Category.assoc xs g₀ pY).trans
        ((congrArg (fun k => xs ≫ k) (Limits.pullback.lift_fst _ _ _)).trans
          (Category.assoc xs pX g).symm)
    let tg : fiber ((xi ≫ jX) ≫ g) ≅ fiber ((xs ≫ pX) ≫ g) :=
      (pullbackFiberIso g (xi ≫ jX)).symm ≪≫
        Functor.isoWhiskerLeft (pullback g) t ≪≫ pullbackFiberIso g (xs ≫ pX)
    let tY : fiber ((xi ≫ q) ≫ jY) ≅ fiber ((xs ≫ g₀) ≫ pY) :=
      eqToIso (congrArg fiber hsource) ≪≫ tg ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    fundamentalGroupHom g₀ xs (properCompleteSpecializationHom R f jX xi xs t a) =
      properCompleteSpecializationHom R fY jY (xi ≫ q) (xs ≫ g₀) tY
        (fundamentalGroupHom q xi a) := by
  intro i pX pY g₀ hsource htarget tg tY
  exact properCompleteSpecializationHom_naturality_of_closedFiberMap R f R fY g g₀
    (Limits.pullback.lift_fst _ _ _) jX jY q hq xi xs t a

/-- The actual map of closed fibers induced by a local base homomorphism
and a morphism of the original families. -/
def properClosedFiberMapOfLocalHom
    {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ)) :
    Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶
      Limits.pullback fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) :=
  Limits.pullback.lift
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g)
    (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))) (by
      have hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫
          Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]
      rw [Category.assoc, hg, ← Category.assoc, Limits.pullback.condition,
        Category.assoc, hres, ← Category.assoc])

omit [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsProper f] in
@[reassoc]
theorem properClosedFiberMapOfLocalHom_fst
    {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ)) :
    properClosedFiberMapOfLocalHom R f φ fY g hg ≫
        Limits.pullback.fst fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) =
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g :=
  Limits.pullback.lift_fst _ _ _

omit [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsProper f] in
@[reassoc]
theorem properClosedFiberMapOfLocalHom_snd
    {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ)) :
    properClosedFiberMapOfLocalHom R f φ fY g hg ≫
        Limits.pullback.snd fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) =
      Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) :=
  Limits.pullback.lift_snd _ _ _

omit [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsProper f] in
/-- A cartesian family morphism gives the actual residue-field base-change
square on the closed fibers. -/
theorem properClosedFiberMapOfLocalHom_isPullback
    {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ))
    (hcart : IsPullback g f fY (Spec.map (CommRingCat.ofHom φ))) :
    IsPullback (properClosedFiberMapOfLocalHom R f φ fY g hg)
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      (Limits.pullback.snd fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ))) := by
  have hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]
  apply IsPullback.of_right (p := properClosedFiberMapOfLocalHom_snd R f φ fY g hg)
    (t := IsPullback.of_hasPullback fY
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
  rw [properClosedFiberMapOfLocalHom_fst, ← hres]
  exact (IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).paste_horiz hcart

omit [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [IsProper f] in
/-- For separably closed residue fields, the actual closed-fiber map of a
proper cartesian family induces the existing field-extension equivalence. -/
theorem pullback_properClosedFiberMapOfLocalHom_isEquivalence
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A)) [IsProper fY]
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ))
    (hcart : IsPullback g f fY (Spec.map (CommRingCat.ofHom φ))) :
    (FiniteEtale.pullback (properClosedFiberMapOfLocalHom R f φ fY g hg)).IsEquivalence := by
  have : IsProper
      (Limits.pullback.snd fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) :=
    inferInstance
  exact pullback_isEquivalence_of_isProper_of_isSepClosed_field_square
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField.map φ)
    (Limits.pullback.snd fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (properClosedFiberMapOfLocalHom R f φ fY g hg)
    (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (properClosedFiberMapOfLocalHom_isPullback R f φ fY g hg hcart)

/-- Specialization commutes with a local change between complete
Noetherian bases and a morphism of proper families over it. The closed-fiber
map and target path are constructed, rather than supplied as assumptions. -/
theorem properCompleteSpecializationHom_naturality_of_localHom
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (φ : A →+* R) [IsLocalHom φ]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of A)) [IsProper fY]
    (g : X ⟶ Y) (hg : g ≫ fY = f ≫ Spec.map (CommRingCat.ofHom φ))
    {T U : Scheme.{u}} (jX : T ⟶ X) (jY : U ⟶ Y) (q : T ⟶ U)
    (hq : q ≫ jY = jX ≫ g) (xi : Spec (CommRingCat.of Ω) ⟶ T)
    {Ω₀ : Type u} [Field Ω₀]
    (xs : Spec (CommRingCat.of Ω₀) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (t : fiber (xi ≫ jX) ≅ fiber (xs ≫
      Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))
    (a : π₁ᵉᵗ(xi)) :
    let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let pX : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
    let pY := Limits.pullback.fst fY (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    let g₀ := properClosedFiberMapOfLocalHom R f φ fY g hg
    let hsource : (xi ≫ q) ≫ jY = (xi ≫ jX) ≫ g :=
      (Category.assoc xi q jY).trans
        ((congrArg (fun k => xi ≫ k) hq).trans (Category.assoc xi jX g).symm)
    let htarget : (xs ≫ g₀) ≫ pY = (xs ≫ pX) ≫ g :=
      (Category.assoc xs g₀ pY).trans
        ((congrArg (fun k => xs ≫ k) (properClosedFiberMapOfLocalHom_fst R f φ fY g hg)).trans
          (Category.assoc xs pX g).symm)
    let tg : fiber ((xi ≫ jX) ≫ g) ≅ fiber ((xs ≫ pX) ≫ g) :=
      (pullbackFiberIso g (xi ≫ jX)).symm ≪≫
        Functor.isoWhiskerLeft (pullback g) t ≪≫ pullbackFiberIso g (xs ≫ pX)
    let tY : fiber ((xi ≫ q) ≫ jY) ≅ fiber ((xs ≫ g₀) ≫ pY) :=
      eqToIso (congrArg fiber hsource) ≪≫ tg ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    fundamentalGroupHom g₀ xs (properCompleteSpecializationHom R f jX xi xs t a) =
      properCompleteSpecializationHom A fY jY (xi ≫ q) (xs ≫ g₀) tY
        (fundamentalGroupHom q xi a) := by
  intro i pX pY g₀ hsource htarget tg tY
  exact properCompleteSpecializationHom_naturality_of_closedFiberMap R f A fY g g₀
    (properClosedFiberMapOfLocalHom_fst R f φ fY g hg) jX jY q hq xi xs t a

end AlgebraicGeometry.FiniteEtale
