/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticMap
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction

/-!
# Actual generic-source lifts of coefficient Frobenius

Surjectivity of the original generic-point Galois map realizes every arithmetic
fundamental-group element by a source automorphism. For a geometrically
connected scheme over a finite field, the arithmetic projection then supplies
a source automorphism restricting to inverse coefficient Frobenius. Its action
on the actual constant-field extension is the original constant-field twist.

The coefficient restriction is proved from the existing arithmetic label
formula. Frobenius is central by its power formula, so its label is independent
of the base-point comparison used by the arithmetic projection.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

section GenericSource

private theorem sourceAutomorphism_eq_fieldSource
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (.of F) ⟶ X) (ρ : Gal(Ω/F))
    (e : Spec (.of Ω) ≅ Spec (.of Ω))
    (he : e.hom = Spec.map (CommRingCat.ofHom ρ.toRingHom))
    (hsource : e.hom ≫ (ξ F Ω ≫ j) = ξ F Ω ≫ j) :
    Aut.of (fiberSourceIso (ξ F Ω ≫ j) e ≪≫ eqToIso (congrArg fiber hsource)) =
      fieldSourceAbsoluteGaloisHom F Ω j ρ := by
  apply Aut.ext
  ext A a
  apply (fiberObjEquivHom (ξ F Ω ≫ j) A).injective
  ext1
  calc
    _ = e.hom ≫ (fiberObjEquivHom (ξ F Ω ≫ j) A a).left :=
      fiberSourceIso_aut_point (ξ F Ω ≫ j) e hsource A a
    _ = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
        (fiberObjEquivHom (ξ F Ω ≫ j) A a).left := by rw [he]
    _ = _ := (fundamentalGroupHom_point_of_point_action j (ξ F Ω)
      (suppliedGaloisEquivFundamentalGroup F Ω ρ) ρ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point F Ω ρ) A a).symm

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (j : Spec (.of F) ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]

/-- Every automorphism of the actual generic fiber functor is induced by a
source automorphism, with its equality on actual field-valued points. -/
theorem exists_genericSourceAutomorphism (g : Aut (fiber (ξ F Ω ≫ j))) :
    ∃ ρ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
      ∃ hsource : e.hom ≫ (ξ F Ω ≫ j) = ξ F Ω ≫ j,
        Aut.of (fiberSourceIso (ξ F Ω ≫ j) e ≪≫ eqToIso (congrArg fiber hsource)) = g := by
  obtain ⟨ρ, hρ⟩ := fieldSourceAbsoluteGaloisHom_surjective F Ω j g
  let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
  have hs : e.hom ≫ ξ F Ω = ξ F Ω := by
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact ρ.commutes a
  have hsource : e.hom ≫ (ξ F Ω ≫ j) = ξ F Ω ≫ j := by
    rw [← Category.assoc, hs]
  refine ⟨ρ, hsource, ?_⟩
  exact (sourceAutomorphism_eq_fieldSource F Ω j ρ e rfl hsource).trans hρ

end GenericSource

section Frobenius

variable (k L F Ω : Type u) [Field k] [Fintype k] [Field L] [Field F] [Field Ω]
  [Algebra k L] [IsSepClosure k L]
  [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
  [Algebra L Ω] [IsScalarTower k L Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (f : X ⟶ Spec (.of k))
  [ConnectedSpace ↑(Limits.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
  (j : Spec (.of F) ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]

/-- Inverse coefficient Frobenius extends to the supplied separable closure
of the original function field while fixing that function field. Geometric
connectedness and the actual generic-point surjection supply the extension. -/
theorem exists_inverseFrobeniusFieldSource
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω) :
    ∃ ρ : Gal(Ω/F),
      ρ.toRingHom.comp (algebraMap L Ω) = (algebraMap L Ω).comp
        (FiniteField.frobeniusAlgEquivOfAlgebraic k L).symm.toRingHom := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let π := arithmeticFundamentalGroupHom k L f (ξ F Ω ≫ j)
  obtain ⟨g, hg⟩ :=
    arithmeticFundamentalGroupHom_surjective_of_connected_constantField
      k L L f (ξ F Ω ≫ j) φ.symm
  obtain ⟨ρ, hsource, hρg⟩ := exists_genericSourceAutomorphism F Ω j g
  let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
  let σ := (ρ.restrictScalars k).restrictNormal L
  have hρ : ρ.toRingHom.comp (algebraMap L Ω) =
      (algebraMap L Ω).comp σ.toRingHom := by
    ext a
    exact ((ρ.restrictScalars k).restrictNormal_commutes L a).symm
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction k L Ω f (ξ F Ω ≫ j) hbase
  have hlabel : π (Aut.of (fiberSourceIso (ξ F Ω ≫ j) e ≪≫
      eqToIso (congrArg fiber hsource))) = α * σ * α⁻¹ :=
    hα e ρ.toRingHom rfl σ hρ hsource
  have hc : Commute α φ := by
    change α * φ = φ * α
    apply AlgEquiv.ext
    intro a
    change α (a ^ Fintype.card k) = (α a) ^ Fintype.card k
    exact map_pow α a (Fintype.card k)
  have hφ : α * φ.symm * α⁻¹ = φ.symm := by
    change α * φ⁻¹ * α⁻¹ = φ⁻¹
    rw [hc.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hσ : σ = φ.symm := by
    exact mul_left_cancel (mul_right_cancel
      (hlabel.symm.trans ((congrArg π hρg).trans (hg.trans hφ.symm))))
  refine ⟨ρ, ?_⟩
  exact hρ.trans (congrArg (fun a : Gal(L/k) =>
    (algebraMap L Ω).comp a.toRingHom) hσ)

end Frobenius

section ConstantExtension

variable (k L F Ω : Type u) [Field k] [Fintype k] [Field L] [Field F] [Field Ω]
  [Algebra k L] [IsSepClosure k L]
  [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
  [Algebra L Ω] [IsScalarTower k L Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]
  (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] [X.Over (Spec (.of k))]
  [ConnectedSpace ↑(Limits.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) (X ↘ Spec (.of k)))]
  (j : Spec (.of F) ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "f" => (X ↘ Spec (CommRingCat.of k))

/-- The constructed inverse Frobenius lift gives the actual pointed square
for the constant-field twist. The two point hypotheses specify the original
generic point and its coefficient map; the action square is proved. -/
theorem exists_inverseFrobeniusSourceSquare
    (x : Spec (.of Ω) ⟶ Limits.pullback f b)
    (hfst : x ≫ Limits.pullback.fst f b = ξ F Ω ≫ j)
    (hsnd : x ≫ Limits.pullback.snd f b = ξ L Ω) :
    ∃ ρ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
      e.hom ≫ x = x ≫ Scheme.constantFieldTwist k L X
        (FiniteField.frobeniusAlgEquivOfAlgebraic k L).symm := by
  have hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω := by
    rw [← hfst, Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd]
    exact fieldGeometricPoint_comp k L Ω
  obtain ⟨ρ, hρ⟩ := exists_inverseFrobeniusFieldSource k L F Ω f j hbase
  let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
  have hs : e.hom ≫ ξ F Ω = ξ F Ω := by
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact ρ.commutes a
  have hL : e.hom ≫ ξ L Ω = ξ L Ω ≫
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k L).symm.toRingHom) := by
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun r : L →+* Ω => Spec.map (CommRingCat.ofHom r)) hρ
  refine ⟨ρ, ?_⟩
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, hfst, ← Category.assoc, hs, Category.assoc,
      Scheme.constantFieldTwist_fst, hfst]
  · rw [Category.assoc, hsnd, hL, Category.assoc, Scheme.constantFieldTwist_snd,
      ← Category.assoc, hsnd]

end ConstantExtension

private theorem exists_genericSourceAutomorphism_of_eq
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (j : Spec (.of F) ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (z : Spec (.of Ω) ⟶ X)
    (hz : z = Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j)
    (g : Aut (fiber z)) :
    ∃ ρ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
      ∃ hs : e.hom ≫ z = z,
        Aut.of (fiberSourceIso z e ≪≫ eqToIso (congrArg fiber hs)) = g := by
  subst z
  exact exists_genericSourceAutomorphism F Ω j g

/-- Every native arithmetic lift of a Frobenius power supplies its actual
coefficient source square. Its induced automorphism is the specified lift,
so no action comparison or independent Frobenius lift is an input. -/
theorem exists_nativeFrobeniusPowerSourceSquare
    (k L F Ω : Type u) [Field k] [Fintype k] [Field L] [Field F] [Field Ω]
    [Algebra k L] [IsSepClosure k L] [IsAlgClosed L]
    [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
    [Algebra L Ω] [IsScalarTower k L Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (f : X ⟶ Spec (.of k))
    (j : Spec (.of F) ⟶ X) [IsPreimmersion j] [IsDominant j] [QuasiCompact j]
    (x : Spec (.of Ω) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (hX : x ≫ Limits.pullback.snd _ f =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ j)
    (hL : x ≫ Limits.pullback.fst _ f =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
    (n : ℕ) (g : Aut (fiber (x ≫ Limits.pullback.snd _ f)))
    (hg : arithmeticFundamentalGroupHom k L f (x ≫ Limits.pullback.snd _ f) g =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ n) :
    ∃ ρ : Gal(Ω/F),
      let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
      ∃ hpoint : e.hom ≫ x = x ≫
          (coefficientBaseChangeIso k L f (FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ n)).hom,
        let hz : e.hom ≫ (x ≫ Limits.pullback.snd _ f) = x ≫ Limits.pullback.snd _ f := by
          rw [← Category.assoc, hpoint, Category.assoc, coefficientBaseChangeIso_hom_snd]
        Aut.of (fiberSourceIso (x ≫ Limits.pullback.snd _ f) e ≪≫
          eqToIso (congrArg fiber hz)) = g := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  let θ := (coefficientBaseChangeIso k L f (φ ^ n)).hom
  let π := arithmeticFundamentalGroupHom k L f (x ≫ Limits.pullback.snd b f)
  obtain ⟨ρ, hs, hρg⟩ := exists_genericSourceAutomorphism_of_eq
    F Ω j (x ≫ Limits.pullback.snd b f) hX g
  let e := Scheme.Spec.mapIso ρ.toRingEquiv.toCommRingCatIso.op
  have hbase : (x ≫ Limits.pullback.snd b f) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, hL]
    exact fieldGeometricPoint_comp k L Ω
  let σ := (ρ.restrictScalars k).restrictNormal L
  have hρ : ρ.toRingHom.comp (algebraMap L Ω) =
      (algebraMap L Ω).comp σ.toRingHom := by
    ext a
    exact ((ρ.restrictScalars k).restrictNormal_commutes L a).symm
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction
    k L Ω f (x ≫ Limits.pullback.snd b f) hbase
  have hlabel : π (Aut.of (fiberSourceIso (x ≫ Limits.pullback.snd b f) e ≪≫
      eqToIso (congrArg fiber hs))) = α * σ * α⁻¹ :=
    hα e ρ.toRingHom rfl σ hρ hs
  have hc : Commute α φ := by
    change α * φ = φ * α
    apply AlgEquiv.ext
    intro a
    change α (a ^ Fintype.card k) = (α a) ^ Fintype.card k
    exact map_pow α a (Fintype.card k)
  have hφ : α * (φ ^ n) * α⁻¹ = φ ^ n := by
    rw [(hc.pow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hσ : σ = φ ^ n :=
    mul_left_cancel (mul_right_cancel
      (hlabel.symm.trans ((congrArg π hρg).trans (hg.trans hφ.symm))))
  have hρφ : ρ.toRingHom.comp (algebraMap L Ω) =
      (algebraMap L Ω).comp (φ ^ n).toRingHom :=
    hρ.trans (congrArg (fun a : Gal(L/k) => (algebraMap L Ω).comp a.toRingHom) hσ)
  have hfixed : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) := by
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    exact ρ.commutes a
  have hcoeff : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (φ ^ n).toRingHom) := by
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun r : L →+* Ω => Spec.map (CommRingCat.ofHom r)) hρφ
  have hpoint : e.hom ≫ x = x ≫ θ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hL, hcoeff, Category.assoc,
        coefficientBaseChangeIso_hom_fst, ← Category.assoc, hL]
    · rw [Category.assoc, hX, ← Category.assoc, hfixed, Category.assoc,
        coefficientBaseChangeIso_hom_snd, hX]
  exact ⟨ρ, hpoint, hρg⟩

end AlgebraicGeometry.FiniteEtale
