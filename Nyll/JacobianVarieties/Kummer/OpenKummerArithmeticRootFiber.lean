/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverTorsor
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift

/-!
# Root coordinates on the original arithmetic Kummer fiber

The original normalized cover is used over an arbitrary constant field.
Its actual generic fiber is identified with all roots of an actual local
unit. The equivalence retains both the existing coefficient-root scaling
and the original generic Galois action on that arithmetic cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer Opposite TopologicalSpace
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem specAutomorphism_eval_appTop
    {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω) (v : Γ(Spec (.of Ω), ⊤)) :
    (Scheme.ΓSpecIso (.of Ω)).hom
        ((Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop v) =
      σ ((Scheme.ΓSpecIso (.of Ω)).hom v) := by
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom)) v

private theorem rootCoordinate_precomp_field
    {Ω : Type} [Field Ω] {Y : Scheme} (V : Y.Opens) (T : Γ(Y, V))
    (σ : Ω ≃+* Ω) (s s' : Spec (.of Ω) ⟶ Y)
    (hs : s ⁻¹ᵁ V = ⊤) (hs' : s' ⁻¹ᵁ V = ⊤)
    (he : s' = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s) :
    (Scheme.ΓSpecIso (.of Ω)).hom (s'.appLE V ⊤ hs'.ge T) =
      σ ((Scheme.ΓSpecIso (.of Ω)).hom (s.appLE V ⊤ hs.ge T)) := by
  subst s'
  let d := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE d s V ⊤ ⊤ hs.ge le_top) T
  change d.appLE ⊤ ⊤ le_top (s.appLE V ⊤ hs.ge T) =
    (d ≫ s).appLE V ⊤ hs'.ge T at h
  have htop : d.appLE ⊤ ⊤ le_top = d.appTop := d.appLE_eq_app
  have hv := ConcreteCategory.congr_hom htop (s.appLE V ⊤ hs.ge T)
  exact (congrArg (Scheme.ΓSpecIso (.of Ω)).hom (h.symm.trans hv)).trans
    (specAutomorphism_eval_appTop σ _)

/-- Actual arithmetic Kummer fibers have complete root coordinates, without
assuming the constant field contains roots of unity. The last identity is
for the ORIGINAL arithmetic-cover action induced by generic Galois elements. -/
theorem exists_arithmeticKummerFiber_rootEquiv
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    letI := kummerGeometricRootAction M S n w j hj hi hn ξ
    ∃ a : Ωˣ, ∃ e : (FiniteEtale.fiber ξ).obj W ≃ {β : Ω // β ^ (n : ℕ) = (a : Ω)},
      (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
        (e (ζ • x)).val = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * (e x).val) ∧
      ∀ (σ : Ω ≃ₐ[X.functionField] Ω) x,
        (e (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ) • x)).val =
          σ (e x).val := by
  intro η ξ W
  let := kummerGeometricRootAction M S n w j hj hi hn ξ
  let f := M.openKummerGenericMap S n w j hj
  let π := f.fromNormalization
  obtain ⟨V, _hV, hxV, h, _hh, v, hv, T, hTpow, hTgen, hlift⟩ :=
    exists_kummer_root_chart M S n w j hj hi hn (ξ default)
  have : Nonempty V := ⟨⟨ξ default, hxV⟩⟩
  have hξ : ξ ⁻¹ᵁ V = ⊤ := point_preimage_top ξ V hxV
  let l := fiberLiftEquiv ξ W
  let c : {s : Spec (.of Ω) ⟶ f.normalization // s ≫ π = ξ} → Γ(Spec (.of Ω), ⊤) :=
    rootLiftCoordinate π V ξ hξ T
  let q : (FiniteEtale.fiber ξ).obj W → Ω :=
    fun x => (Scheme.ΓSpecIso (.of Ω)).hom (c (l x))
  let av : Ω := (Scheme.ΓSpecIso (.of Ω)).hom (ξ.appLE V ⊤ hξ.ge v)
  have hav : IsUnit av :=
    (hv.map (ξ.appLE V ⊤ hξ.ge).hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
  let a : Ωˣ := Units.mk0 av hav.ne_zero
  have hpow (x : (FiniteEtale.fiber ξ).obj W) : q x ^ (n : ℕ) = (a : Ω) := by
    change ((Scheme.ΓSpecIso (.of Ω)).hom (c (l x))) ^ (n : ℕ) = _
    rw [← map_pow]
    exact congrArg (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate_pow π V ξ hξ T (n : ℕ) v hTpow (l x))
  let qe : (FiniteEtale.fiber ξ).obj W → {β : Ω // β ^ (n : ℕ) = (a : Ω)} :=
    fun x => ⟨q x, hpow x⟩
  have hinj : Function.Injective qe := by
    intro x y hxy
    apply l.injective
    apply rootLiftCoordinate_injective π V ξ hξ T (n : ℕ) v hTpow (hlift _ ξ hξ)
    exact (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
      (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective qe := by
    intro β
    let τ : Γ(Spec (.of Ω), ⊤) := (Scheme.ΓSpecIso (.of Ω)).inv β.val
    have hτ : τ ^ (n : ℕ) = ξ.appLE V ⊤ hξ.ge v := by
      apply (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
      rw [map_pow]
      change ((Scheme.ΓSpecIso (.of Ω)).hom ((Scheme.ΓSpecIso (.of Ω)).inv β.val)) ^
        (n : ℕ) = av
      rw [Iso.inv_hom_id_apply]
      exact β.property
    obtain ⟨s, hs⟩ :=
      exists_rootLiftCoordinate π V ξ hξ T (n : ℕ) v (hlift _ ξ hξ) τ hτ
    refine ⟨l.symm s, Subtype.ext ?_⟩
    change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (l.symm s))) = β.val
    exact (congrArg (fun z => (Scheme.ΓSpecIso (.of Ω)).hom (c z))
      (l.apply_symm_apply s)).trans
        ((congrArg (Scheme.ΓSpecIso (.of Ω)).hom hs).trans
          (Iso.inv_hom_id_apply _ _))
  let e := Equiv.ofBijective qe ⟨hinj, hsurj⟩
  refine ⟨a, e, ?_, ?_⟩
  · intro ζ x
    let d := kummerNormalizationRootScale M S n w j hj ζ
    have hd : d.hom ≫ π = π :=
      EtaleFundamentalGroups.Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _
    have hpre : π ⁻¹ᵁ V ≤ d.hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, hd]
    have hscale := kummerNormalizationRootScale_localRoot M S n w j hj V h T hTgen ζ
    have hcoord := rootLiftCoordinate_comp π V ξ hξ T d.hom hd hpre
      ((j ≫ M.toBase).appLE ⊤ V le_top ((Scheme.ΓSpecIso (.of K)).inv (ζ.val : K)))
      hscale (l x)
    have hl : l (ζ • x) =
        ⟨(l x).1 ≫ d.hom,
          (Category.assoc _ _ _).trans ((congrArg ((l x).1 ≫ ·) hd).trans (l x).2)⟩ := by
      apply Subtype.ext
      exact fiberLiftEquiv_naturality ξ (kummerCoverRootScale M S n w j hj hi hn ζ).hom x
    change (Scheme.ΓSpecIso (.of Ω)).hom (c (l (ζ • x))) = _
    rw [hl]
    change (Scheme.ΓSpecIso (.of Ω)).hom
      (rootLiftCoordinate π V ξ hξ T _) = _
    apply (congrArg (Scheme.ΓSpecIso (.of Ω)).hom hcoord).trans
    apply (map_mul (Scheme.ΓSpecIso (.of Ω)).hom.hom _ _).trans
    exact congrArg (fun z : Γ(Spec (.of Ω), ⊤) =>
      (Scheme.ΓSpecIso (.of Ω)).hom z * q x)
      (appLE_baseScalar (j ≫ M.toBase) ξ V hξ ((Scheme.ΓSpecIso (.of K)).inv (ζ.val : K)))
  · intro σ x
    let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    have hl : (l (g • x)).val =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (l x).val :=
      FiniteEtale.fundamentalGroupHom_field_fiberLift
        (X.fromSpecStalk (genericPoint X)) W σ x
    exact rootCoordinate_precomp_field (π ⁻¹ᵁ V) T σ.toRingEquiv
      (l x).val (l (g • x)).val (rootLift_preimage π V ξ hξ (l x))
      (rootLift_preimage π V ξ hξ (l (g • x))) hl

end AlgebraicCurve.CurveModel.OpenKummer
