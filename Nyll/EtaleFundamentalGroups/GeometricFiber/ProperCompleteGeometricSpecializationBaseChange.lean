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
# Comparison through compatible complete-local models

An actual map between two proper complete-local models, together with
commuting actual generic and geometric closed-fiber maps, compares their
constructed specializations. This applies to compatible completed DVR
models. Neither a common dominating DVR nor any map between unrelated
models is assumed to exist.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

/-- A supplied map of families and a supplied compatible map of field
points construct the actual map of fiber products. -/
def properFamilyFiberMapOver {X Y S T P Q : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (a : X ⟶ Y) (c : S ⟶ T)
    (ha : f ≫ c = a ≫ g) (v : P ⟶ S) (w : Q ⟶ T)
    (j : P ⟶ Q) (hv : v ≫ c = j ≫ w) :
    Limits.pullback f v ⟶ Limits.pullback g w :=
  Limits.pullback.map f v g w a j c ha hv

@[reassoc]
theorem properFamilyFiberMapOver_fst {X Y S T P Q : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (a : X ⟶ Y) (c : S ⟶ T)
    (ha : f ≫ c = a ≫ g) (v : P ⟶ S) (w : Q ⟶ T)
    (j : P ⟶ Q) (hv : v ≫ c = j ≫ w) :
    properFamilyFiberMapOver f g a c ha v w j hv ≫ Limits.pullback.fst g w =
      Limits.pullback.fst f v ≫ a :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem properFamilyFiberMapOver_snd {X Y S T P Q : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (a : X ⟶ Y) (c : S ⟶ T)
    (ha : f ≫ c = a ≫ g) (v : P ⟶ S) (w : Q ⟶ T)
    (j : P ⟶ Q) (hv : v ≫ c = j ≫ w) :
    properFamilyFiberMapOver f g a c ha v w j hv ≫ Limits.pullback.snd g w =
      Limits.pullback.snd f v ≫ j :=
  Limits.pullback.lift_snd _ _ _

private theorem model_conjAut_of_point_transports_eq
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x y z : Spec (CommRingCat.of Ω) ⟶ X}
    (hx : x = z) (hy : y = z) (a : π₁ᵉᵗ(x)) (b : π₁ᵉᵗ(y))
    (h : hx ▸ a = hy ▸ b) :
    (eqToIso (congrArg fiber (hx.trans hy.symm))).conjAut a = b := by
  subst z
  subst y
  exact h

private theorem model_fundamentalGroupHom_square
    {T U V X : Scheme.{u}}
    (a : T ⟶ U) (b : U ⟶ X) (c : T ⟶ V) (d : V ⟶ X)
    (h : a ≫ b = c ≫ d) {Ω : Type u} [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ T)
    (hx : (x ≫ a) ≫ b = (x ≫ c) ≫ d) (α : π₁ᵉᵗ(x)) :
    (eqToIso (congrArg fiber hx)).conjAut
        (fundamentalGroupHom b (x ≫ a) (fundamentalGroupHom a x α)) =
      fundamentalGroupHom d (x ≫ c) (fundamentalGroupHom c x α) := by
  let hleft : (x ≫ a) ≫ b = x ≫ c ≫ d :=
    (Category.assoc x a b).trans (congrArg (fun k => x ≫ k) h)
  let hright : (x ≫ c) ≫ d = x ≫ c ≫ d := Category.assoc x c d
  exact model_conjAut_of_point_transports_eq hleft hright _ _
    ((fundamentalGroupHom_comp_of_eq a b (c ≫ d) h.symm x hleft α).trans
      (fundamentalGroupHom_comp_of_eq c d (c ≫ d) rfl x hright α).symm)

/-- Actual compatible geometric-fiber maps between two complete-local
models compare the constructed specializations. The common path on the
target is induced by the given total-space map, and both closed-fiber
isomorphisms are supplied by the proved complete-local comparison. -/
theorem properCompleteGeometricSpecializationHom_naturality_of_fiberSquares
    (R A : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of A)) [IsProper g]
    (a : X ⟶ Y)
    {k k' K K' : Type u}
    [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field K] [Field K']
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (ι : IsLocalRing.ResidueField R →+* k)
    (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (s' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of A))
    (ι' : IsLocalRing.ResidueField A →+* k')
    (hs' : s' = Spec.map (CommRingCat.ofHom ι') ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    (η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (η' : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of A))
    (qη : Limits.pullback f η ⟶ Limits.pullback g η')
    (qs : Limits.pullback f s ⟶ Limits.pullback g s')
    (hqη : qη ≫ Limits.pullback.fst g η' = Limits.pullback.fst f η ≫ a)
    (hqs : qs ≫ Limits.pullback.fst g s' = Limits.pullback.fst f s ≫ a)
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s)) (b : π₁ᵉᵗ(xη)) :
    let hsource : (xη ≫ qη) ≫ Limits.pullback.fst g η' =
        (xη ≫ Limits.pullback.fst f η) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xη ≫ q) hqη).trans (Category.assoc _ _ _).symm)
    let htarget : (xs ≫ qs) ≫ Limits.pullback.fst g s' =
        (xs ≫ Limits.pullback.fst f s) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xs ≫ q) hqs).trans (Category.assoc _ _ _).symm)
    let ta : fiber ((xη ≫ Limits.pullback.fst f η) ≫ a) ≅
        fiber ((xs ≫ Limits.pullback.fst f s) ≫ a) :=
      (pullbackFiberIso a (xη ≫ Limits.pullback.fst f η)).symm ≪≫
        Functor.isoWhiskerLeft (pullback a) t ≪≫
        pullbackFiberIso a (xs ≫ Limits.pullback.fst f s)
    let tY : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η') ≅
        fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s') :=
      eqToIso (congrArg fiber hsource) ≪≫ ta ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    fundamentalGroupHom qs xs
        (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t b) =
      properCompleteGeometricSpecializationHom A g s' ι' hs' η' (xη ≫ qη) (xs ≫ qs) tY
        (fundamentalGroupHom qη xη b) := by
  intro hsource htarget ta tY
  let eX : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ Limits.pullback.fst f s) :=
    fundamentalGroupEquivProperCompleteGeometricClosedFiber R f s ι hs xs
  let eY : π₁ᵉᵗ(xs ≫ qs) ≃ₜ* π₁ᵉᵗ((xs ≫ qs) ≫ Limits.pullback.fst g s') :=
    fundamentalGroupEquivProperCompleteGeometricClosedFiber A g s' ι' hs' (xs ≫ qs)
  let csource : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η') ≅
      fiber ((xη ≫ Limits.pullback.fst f η) ≫ a) :=
    eqToIso (congrArg fiber hsource)
  let ctarget : fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s') ≅
      fiber ((xs ≫ Limits.pullback.fst f s) ≫ a) :=
    eqToIso (congrArg fiber htarget)
  have hclosed (c : π₁ᵉᵗ(xs)) :
      ctarget.conjAut (eY (fundamentalGroupHom qs xs c)) =
        fundamentalGroupHom a (xs ≫ Limits.pullback.fst f s) (eX c) := by
    dsimp only [eX, eY]
    rw [fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply,
      fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply]
    exact model_fundamentalGroupHom_square qs (Limits.pullback.fst g s')
      (Limits.pullback.fst f s) a hqs xs htarget c
  have hgeneric : csource.conjAut
      (fundamentalGroupHom (Limits.pullback.fst g η') (xη ≫ qη)
        (fundamentalGroupHom qη xη b)) =
      fundamentalGroupHom a (xη ≫ Limits.pullback.fst f η)
        (fundamentalGroupHom (Limits.pullback.fst f η) xη b) :=
    model_fundamentalGroupHom_square qη (Limits.pullback.fst g η')
      (Limits.pullback.fst f η) a hqη xη hsource b
  have hpath (c : π₁ᵉᵗ((xη ≫ qη) ≫ Limits.pullback.fst g η')) :
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
        (fundamentalGroupHom (Limits.pullback.fst g η') (xη ≫ qη)
          (fundamentalGroupHom qη xη b))) := congrArg ta.conjAut hgeneric.symm
    _ = ctarget.conjAut (tY.conjAut
        (fundamentalGroupHom (Limits.pullback.fst g η') (xη ≫ qη)
          (fundamentalGroupHom qη xη b))) := (hpath _).symm
    _ = _ := congrArg ctarget.conjAut
      ((fundamentalGroupEquivProperCompleteGeometricClosedFiber_apply
        A g s' ι' hs' (xs ≫ qs)
        (properCompleteGeometricSpecializationHom A g s' ι' hs' η'
          (xη ≫ qη) (xs ≫ qs) tY (fundamentalGroupHom qη xη b))).trans
        (properCompleteGeometricSpecializationHom_triangle A g s' ι' hs' η'
          (xη ≫ qη) (xs ≫ qs) tY (fundamentalGroupHom qη xη b))).symm

private theorem model_mulEquiv_conj {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (g a : G) : e (MulAut.conj g a) = MulAut.conj (e g) (e a) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- Changing the selected path conjugates geometric specialization by
its actual inverse image under the proved closed-fiber group equivalence. -/
theorem properCompleteGeometricSpecializationHom_path_change
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {k K : Type u} [Field k] [IsSepClosed k] [Field K]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (ι : IsLocalRing.ResidueField R →+* k)
    (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t₁ t₂ : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s)) (b : π₁ᵉᵗ(xη)) :
    properCompleteGeometricSpecializationHom R f s ι hs η xη xs t₂ b =
      MulAut.conj
        ((fundamentalGroupEquivProperCompleteGeometricClosedFiber R f s ι hs xs).symm
          (Aut.of (t₁.symm ≪≫ t₂)))
        (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t₁ b) := by
  let e := fundamentalGroupEquivProperCompleteGeometricClosedFiber R f s ι hs xs
  change e.symm (continuousConjAut t₂
      (fundamentalGroupHom (Limits.pullback.fst f η) xη b)) =
    MulAut.conj (e.symm (Aut.of (t₁.symm ≪≫ t₂)))
      (e.symm (continuousConjAut t₁
        (fundamentalGroupHom (Limits.pullback.fst f η) xη b)))
  exact (congrArg e.symm
    (continuousConjAut_eq_conj t₁ t₂
      (fundamentalGroupHom (Limits.pullback.fst f η) xη b))).trans
      (model_mulEquiv_conj e.symm.toMulEquiv (Aut.of (t₁.symm ≪≫ t₂))
        (continuousConjAut t₁ (fundamentalGroupHom (Limits.pullback.fst f η) xη b)))

/-- Compatible complete-local constructions with independently chosen
paths agree up to the explicit inner conjugator. This is the comparison
for compatible completed DVR models; it does not assert existence of a
comparison map for arbitrary DVRs with the same underlying two points. -/
theorem properCompleteGeometricSpecializationHom_naturality_up_to_conjugacy
    (R A : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of A)) [IsProper g]
    (a : X ⟶ Y)
    {k k' K K' : Type u}
    [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field K] [Field K']
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (ι : IsLocalRing.ResidueField R →+* k)
    (hs : s = Spec.map (CommRingCat.ofHom ι) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (s' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of A))
    (ι' : IsLocalRing.ResidueField A →+* k')
    (hs' : s' = Spec.map (CommRingCat.ofHom ι') ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
    (η : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (η' : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of A))
    (qη : Limits.pullback f η ⟶ Limits.pullback g η')
    (qs : Limits.pullback f s ⟶ Limits.pullback g s')
    (hqη : qη ≫ Limits.pullback.fst g η' = Limits.pullback.fst f η ≫ a)
    (hqs : qs ≫ Limits.pullback.fst g s' = Limits.pullback.fst f s ≫ a)
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (CommRingCat.of Ωη) ⟶ Limits.pullback f η)
    (xs : Spec (CommRingCat.of Ωs) ⟶ Limits.pullback f s)
    (t : fiber (xη ≫ Limits.pullback.fst f η) ≅
      fiber (xs ≫ Limits.pullback.fst f s))
    (t' : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η') ≅
      fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s')) (b : π₁ᵉᵗ(xη)) :
    let hsource : (xη ≫ qη) ≫ Limits.pullback.fst g η' =
        (xη ≫ Limits.pullback.fst f η) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xη ≫ q) hqη).trans (Category.assoc _ _ _).symm)
    let htarget : (xs ≫ qs) ≫ Limits.pullback.fst g s' =
        (xs ≫ Limits.pullback.fst f s) ≫ a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => xs ≫ q) hqs).trans (Category.assoc _ _ _).symm)
    let ta : fiber ((xη ≫ Limits.pullback.fst f η) ≫ a) ≅
        fiber ((xs ≫ Limits.pullback.fst f s) ≫ a) :=
      (pullbackFiberIso a (xη ≫ Limits.pullback.fst f η)).symm ≪≫
        Functor.isoWhiskerLeft (pullback a) t ≪≫
        pullbackFiberIso a (xs ≫ Limits.pullback.fst f s)
    let tY : fiber ((xη ≫ qη) ≫ Limits.pullback.fst g η') ≅
        fiber ((xs ≫ qs) ≫ Limits.pullback.fst g s') :=
      eqToIso (congrArg fiber hsource) ≪≫ ta ≪≫
        (eqToIso (congrArg fiber htarget)).symm
    properCompleteGeometricSpecializationHom A g s' ι' hs' η' (xη ≫ qη) (xs ≫ qs) t'
        (fundamentalGroupHom qη xη b) =
      MulAut.conj
        ((fundamentalGroupEquivProperCompleteGeometricClosedFiber
          A g s' ι' hs' (xs ≫ qs)).symm (Aut.of (tY.symm ≪≫ t')))
        (fundamentalGroupHom qs xs
          (properCompleteGeometricSpecializationHom R f s ι hs η xη xs t b)) := by
  intro hsource htarget ta tY
  have hnat := properCompleteGeometricSpecializationHom_naturality_of_fiberSquares
    R A f g a s ι hs s' ι' hs' η η' qη qs hqη hqs xη xs t b
  let c := (fundamentalGroupEquivProperCompleteGeometricClosedFiber
    A g s' ι' hs' (xs ≫ qs)).symm (Aut.of (tY.symm ≪≫ t'))
  exact (properCompleteGeometricSpecializationHom_path_change
    A g s' ι' hs' η' (xη ≫ qη) (xs ≫ qs) tY t'
      (fundamentalGroupHom qη xη b)).trans
    (congrArg (MulAut.conj c) hnat.symm)

end AlgebraicGeometry.FiniteEtale
