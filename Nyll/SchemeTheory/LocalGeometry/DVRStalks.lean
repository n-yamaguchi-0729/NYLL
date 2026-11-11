/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalLocalizationAtPrimeEtale
public import Nyll.ValuedFieldTheory.Valuation.Subring.Arithmetic.MemSubMemNonunits

/-!
# Stalks and affine neighborhoods over a discrete valuation ring

Codimension-one points, smooth special-fibre stalks, specialization localizations,
and simultaneous affine neighborhoods of finitely many DVR points.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.CodimensionOne
universe u
open AlgebraicGeometry CategoryTheory Topology

theorem _root_.AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Flat t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
      x.1 ∈ V)
    (x : T) (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1) : x ∈ V := by
  classical
  by_cases hxs : t.base x = IsLocalRing.closedPoint R
  swap
  · exact hVη x hxs
  have key : ∀ y : T, y ⤳ x → t.base y = IsLocalRing.closedPoint R → y = x := by
    intro y hyx hys
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨𝔮, rfl⟩ : y ∈ Set.range (T.fromSpecStalk x).base := by
      rw [Scheme.range_fromSpecStalk]; exact hyx
    let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (t.base x) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base
        x) trivial
    let φ : CommRingCat.of R ⟶ T.presheaf.stalk x := g ≫ t.stalkMap x
    have hfac : T.fromSpecStalk x ≫ t = Spec.map φ := by
      rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk t, Spec.fromSpecStalk_eq]
    have hbase : t.base ((T.fromSpecStalk x).base 𝔮) = (Spec.map φ).base 𝔮 := by
      rw [← hfac]; rfl
    have hcomap : ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := rfl
    have hϖ𝔮 : φ.hom ϖ ∈ 𝔮.asIdeal := by
      have h1 : ((Spec.map φ).base 𝔮).asIdeal = IsLocalRing.maximalIdeal R := by
        rw [← hbase, hys]; rfl
      have h2 : ϖ ∈ 𝔮.asIdeal.comap φ.hom := by
        rw [← hcomap, h1]; exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
      exact h2
    have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (g.hom ϖ) := by
      let : Algebra Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk
        (t.base x)) :=
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base x) trivial).hom.toAlgebra
      have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x))
          ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
            ⟨t.base x, trivial⟩).asIdeal :=
        (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨t.base x, trivial⟩
      have : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
        Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
        ⟨t.base x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
      have : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) :=
        IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
      have hne : g.hom ϖ ≠ 0 := by
        intro h0
        have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk (t.base
          x)) hle
        have h0' : algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of
          R)).presheaf.stalk (t.base x))
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
            = algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk
              (t.base x)) 0 := by
          rw [map_zero]; exact h0
        have := hinj h0'
        exact hϖ.ne_zero ((Scheme.ΓSpecIso (CommRingCat.of
          R)).symm.commRingCatIsoToRingEquiv.injective
          (by rw [map_zero]; exact this))
      exact (IsRegular.of_ne_zero hne).left.isSMulRegular
    have hflat : (t.stalkMap x).hom.Flat := Flat.stalkMap t x
    have hreg : IsSMulRegular (T.presheaf.stalk x) (φ.hom ϖ) := by
      let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x))
          (T.presheaf.stalk x) := (t.stalkMap x).hom.toAlgebra
      have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (t.base x)) (T.presheaf.stalk
        x) := hflat
      exact hgreg.of_flat
    have hnzd : φ.hom ϖ ∈ nonZeroDivisors (T.presheaf.stalk x) := by
      rw [mem_nonZeroDivisors_iff]
      refine ⟨fun a ha => hreg ?_, fun a ha => hreg ?_⟩
      · change φ.hom ϖ * a = φ.hom ϖ * 0; rw [mul_zero]; exact ha
      · change φ.hom ϖ * a = φ.hom ϖ * 0; rw [mul_zero, mul_comm]; exact ha
    have hnotmin : 𝔮.asIdeal ∉ minimalPrimes (T.presheaf.stalk x) := fun hmin =>
      Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hϖ𝔮 hnzd
    have : Ring.KrullDimLE 1 (T.presheaf.stalk x) := (Ring.krullDimLE_iff).mpr hx
    have hmax : 𝔮.asIdeal.IsMaximal :=
      ((Ring.krullDimLE_one_iff.mp inferInstance) 𝔮.asIdeal 𝔮.isPrime).resolve_left hnotmin
    have h𝔮 : 𝔮 = IsLocalRing.closedPoint (T.presheaf.stalk x) :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    rw [h𝔮, Scheme.fromSpecStalk_closedPoint]
  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  have : QuasiSober {y : T // t.base y = IsLocalRing.closedPoint R} :=
    hS.isClosedEmbedding_subtypeVal.quasiSober
  let xs : {y : T // t.base y = IsLocalRing.closedPoint R} := ⟨x, hxs⟩
  have hZ : closure ({xs} : Set {y : T // t.base y = IsLocalRing.closedPoint R}) ∈
      irreducibleComponents {y : T // t.base y = IsLocalRing.closedPoint R} := by
    refine ⟨isIrreducible_singleton.closure, fun W hW hZW => ?_⟩
    have hη := hW.isGenericPoint_genericPoint_closure
    have hxW : xs ∈ closure W := subset_closure (hZW (subset_closure (Set.mem_singleton xs)))
    have hηx : hW.genericPoint ⤳ xs := hη.specializes hxW
    have hηeq : hW.genericPoint = xs :=
      Subtype.ext (key hW.genericPoint.1 (hηx.map continuous_subtype_val) hW.genericPoint.2)
    have hcl : closure W = closure {xs} := by rw [← hηeq]; exact hη.symm
    exact subset_closure.trans hcl.le
  obtain ⟨y, hyZ, hyV⟩ := hVs _ hZ
  have hsp : x ⤳ y.1 := (specializes_iff_mem_closure.mpr hyZ).map continuous_subtype_val
  exact hsp.mem_open V.isOpen hyV

end SchemeTheory.DVRStalks.CodimensionOne
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.SpecialFibre

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace SpecialPrime

theorem isDomain_quot_of_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (𝔓 : Ideal B) [𝔓.IsPrime] (hϖ𝔓 : algebraMap R B ϖ ∈ 𝔓)
    (O : Type u) [CommRing O] [Algebra B O] [IsLocalization.AtPrime O 𝔓] :
    IsDomain (O ⧸ Ideal.map (algebraMap B O) (Ideal.span {algebraMap R B ϖ})) := by
  classical
  let I₀ : Ideal R := Ideal.span {ϖ}
  have hmax : I₀.IsMaximal := by
    rw [show I₀ = IsLocalRing.maximalIdeal R from hϖ.symm]; exact
      IsLocalRing.maximalIdeal.isMaximal R
  let k := R ⧸ I₀
  let : Field k := Ideal.Quotient.field I₀
  let I : Ideal B := Ideal.span {algebraMap R B ϖ}
  have hI : I = I₀.map (algebraMap R B) := by
    change Ideal.span {algebraMap R B ϖ} = Ideal.map (algebraMap R B) (Ideal.span {ϖ})
    rw [Ideal.map_span, Set.image_singleton]
  have hIle : I ≤ 𝔓 := by
    change Ideal.span {algebraMap R B ϖ} ≤ 𝔓
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hϖ𝔓
  let C := B ⧸ I
  let algkC : Algebra k C := Ideal.Quotient.algebraQuotientOfLEComap (by rw [hI]; exact
    Ideal.le_comap_map)
  have hsmooth : Algebra.Smooth k C := by
    let e₁ : C ≃ₐ[B] B ⊗[R] k :=
      (Ideal.quotientEquivAlgOfEq B hI).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        I₀)
    let e₂ : B ⊗[R] k ≃ₐ[R] k ⊗[R] B := Algebra.TensorProduct.comm R B k
    have he₁ : ∀ b : B, e₁ (Ideal.Quotient.mk I b) = b ⊗ₜ[R] (1 : k) := by
      intro b
      change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀)
        (Ideal.quotientEquivAlgOfEq B hI (Ideal.Quotient.mk I b)) = _
      rw [Ideal.quotientEquivAlgOfEq_mk]
      exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B I₀ b
    let e : C ≃ₐ[k] k ⊗[R] B :=
      AlgEquiv.ofRingEquiv (f := (e₁.toRingEquiv.trans e₂.toRingEquiv)) (by
        intro c
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change e₂ (e₁ (Ideal.Quotient.mk I (algebraMap R B r))) = algebraMap k (k ⊗[R] B)
          (Ideal.Quotient.mk I₀ r)
        rw [he₁, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one r,
          ← TensorProduct.smul_tmul', map_smul]
        change r • (Algebra.TensorProduct.comm R B k) ((1 : B) ⊗ₜ[R] (1 : k)) = _
        rw [Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
        rfl)
    exact Algebra.Smooth.of_equiv e.symm
  let q : Ideal C := 𝔓.map (Ideal.Quotient.mk I)
  have hqcomap : q.comap (Ideal.Quotient.mk I) = 𝔓 := by
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) 𝔓) = 𝔓
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker,
      sup_eq_left.mpr hIle]
  have hq : q.IsPrime := by
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]; exact hIle
  let O' := O ⧸ Ideal.map (algebraMap B O) I
  let algCO' : Algebra C O' := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsLocalization (𝔓.primeCompl.map (Ideal.Quotient.mk I)) O' :=
    IsLocalization.of_surjective (M := 𝔓.primeCompl) (S := O) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap B O) I)) Ideal.Quotient.mk_surjective (by rfl)
      (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hM : 𝔓.primeCompl.map (Ideal.Quotient.mk I) = q.primeCompl := by
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      change Ideal.Quotient.mk I b ∉ q
      intro hc
      apply hb
      change b ∈ 𝔓
      rw [← hqcomap]; exact hc
    · intro hc
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨b, ?_, rfl⟩
      intro hb
      exact hc (Ideal.mem_map_of_mem _ hb)
  have : IsLocalization.AtPrime O' q := by
    change IsLocalization q.primeCompl O'
    rw [← hM]; infer_instance
  have : IsDomain (Localization.AtPrime q) :=
    (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
      k C q (Localization.AtPrime q)).1
  exact MulEquiv.isDomain (Localization.AtPrime q) (IsLocalization.algEquiv q.primeCompl O'
    (Localization.AtPrime q)).toMulEquiv

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
      p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime := by
  classical
  let O := Y.presheaf.stalk p
  have hmor : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤
        (f.base p) trivial) ≫
        f.stalkMap p := by
    apply Spec.map_injective
    rw [← halg, Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hc : ∀ r : R, algebraMap R O r =
      (f.stalkMap p).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base p) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r
    exact congrArg (fun φ : CommRingCat.of R ⟶ Y.presheaf.stalk p => φ.hom r) hmor
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field R
    rw [hϖ, Ideal.span_singleton_eq_bot]
    exact h
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  let A := Γ(Spec (CommRingCat.of R), ⊤)
  let B := Γ(Y, V)
  let algAB : Algebra A B := (f.appLE ⊤ V le_top).hom.toAlgebra
  have hsAB : (f.appLE ⊤ V le_top).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have : Algebra.Smooth A B := hsAB
  let algRA : Algebra R A := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toAlgebra
  let algRB : Algebra R B := f.sectionsAlgebra V
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Smooth R A := by
    have : Algebra.Smooth R R := {}
    refine Algebra.Smooth.of_equiv (A := R) ?_
    exact AlgEquiv.ofBijective (Algebra.ofId R A)
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
  have : Algebra.Smooth R B := Algebra.Smooth.comp R A B
  let 𝔓 := hV.primeIdealOf ⟨p, hpV⟩
  let algBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨p, hpV⟩ : V)
  have hloc : IsLocalization.AtPrime O 𝔓.asIdeal := hV.isLocalization_stalk ⟨p, hpV⟩
  have htow : ∀ r : R, algebraMap B O (algebraMap R B r) = algebraMap R O r := by
    intro r
    rw [hc r]
    change (Y.presheaf.germ V p hpV).hom ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso
      (CommRingCat.of R)).inv.hom r)) =
      (f.stalkMap p).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base p) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    have hres := Y.presheaf.germ_res
      (homOfLE (show V ≤ f ⁻¹ᵁ ⊤ from le_top)) p hpV
    have hst := Scheme.Hom.germ_stalkMap f ⊤ p trivial
    exact (congrArg (fun α : Γ(Y, f ⁻¹ᵁ ⊤) ⟶ Y.presheaf.stalk p =>
      α.hom ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) hres).trans
      (congrArg (fun α : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Y.presheaf.stalk p =>
        α.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hst).symm
  have : IsScalarTower R B O := IsScalarTower.of_algebraMap_eq fun r => (htow r).symm
  have : Module.Flat B O := IsLocalization.flat O 𝔓.asIdeal.primeCompl
  have : Module.Flat R O := Module.Flat.trans R B O
  have hne : algebraMap R O ϖ ≠ 0 := by
    intro h
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := O)
      (mem_nonZeroDivisors_of_ne_zero hϖ0)
    have h1 : ϖ • (1 : O) = ϖ • (0 : O) := by rw [Algebra.smul_def, mul_one, smul_zero]; exact h
    exact one_ne_zero (hreg h1)
  have hmem : algebraMap R B ϖ ∈ 𝔓.asIdeal := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff O 𝔓.asIdeal, htow, hc,
      IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_map_iff (f.stalkMap p).hom,
      ← Scheme.mem_basicOpen (Spec (CommRingCat.of R)) ((Scheme.ΓSpecIso (CommRingCat.of
        R)).inv.hom ϖ) (f.base p) trivial,
      AlgebraicGeometry.basicOpen_eq_of_affine]
    have : ϖ ∈ (f.base p).asIdeal := by
      rw [hp]; change ϖ ∈ IsLocalRing.maximalIdeal R; rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    intro hmem
    exact hmem this
  have hdom := isDomain_quot_of_smooth ϖ hϖ 𝔓.asIdeal hmem O
  have hmap : Ideal.map (algebraMap B O) (Ideal.span {algebraMap R B ϖ}) =
      Ideal.span {algebraMap R O ϖ} := by
    rw [Ideal.map_span, Set.image_singleton, htow]
  refine ⟨hne, ?_⟩
  change (Ideal.span {algebraMap R O ϖ}).IsPrime
  rw [← hmap]
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

end SpecialPrime

theorem
_root_.AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk
      p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime :=
  SpecialPrime.main ϖ hϖ f p hp halg

end SchemeTheory.DVRStalks.SpecialFibre
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.BirationalFractionFields

open CategoryTheory AlgebraicGeometry

universe u

namespace Localizations

theorem isFractionRing_of_localization_iso
    {R S R' S' : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing R'] [CommRing S'] [Nontrivial S'] [Algebra R R'] (M : Submonoid R) [IsLocalization M
      R']
    (φ : R →+* S) (β : S →+* S') (hβ : Function.Injective β) (e : R' ≃+* S')
    (he : ∀ r, e (algebraMap R R' r) = β (φ r)) :
    let : Algebra R (FractionRing S) := ((algebraMap S (FractionRing S)).comp φ).toAlgebra
    IsFractionRing R (FractionRing S) := by
  intro fractionAlgebra
  have hM0 : ∀ m : M, (m : R) ≠ 0 := by
    intro m hm
    have hu : IsUnit (algebraMap R R' m) := IsLocalization.map_units R' m
    rw [hm, map_zero, isUnit_zero_iff] at hu
    have : (0 : S') = 1 := by rw [← map_zero e, hu, map_one]
    exact zero_ne_one this
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    have h1 : algebraMap R R' (a - b) = 0 := by
      apply e.injective
      rw [he, map_sub φ, hab, map_zero, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M R' (a - b)).mp h1
    rcases mul_eq_zero.mp hm with h | h
    · exact absurd h (hM0 m)
    · exact h
  have hkey : ∀ s : S, ∃ r : R, ∃ m : M, s * φ m = φ r := by
    intro s
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj M (e.symm (β s))
    refine ⟨r, m, hβ ?_⟩
    rw [map_mul, ← he, ← he, ← hrm, map_mul, RingEquiv.apply_symm_apply]
  have halg : ∀ r, algebraMap R (FractionRing S) r = algebraMap S (FractionRing S) (φ r) := fun _
    => rfl
  have : FaithfulSMul R (FractionRing S) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    rw [halg, halg] at hab
    exact hinj (IsFractionRing.injective S (FractionRing S) hab)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨s, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  obtain ⟨r₁, m₁, h₁⟩ := hkey s
  obtain ⟨r₂, m₂, h₂⟩ := hkey t
  have hm₁ : algebraMap S (FractionRing S) (φ m₁) ≠ 0 := fun h0 =>
    hM0 m₁ (hinj ((IsFractionRing.injective S (FractionRing S) (h0.trans (map_zero _).symm)).trans
      (map_zero φ).symm))
  have hm₂ : algebraMap S (FractionRing S) (φ m₂) ≠ 0 := fun h0 =>
    hM0 m₂ (hinj ((IsFractionRing.injective S (FractionRing S) (h0.trans (map_zero _).symm)).trans
      (map_zero φ).symm))
  have hs : algebraMap S (FractionRing S) s =
      algebraMap S (FractionRing S) (φ r₁) / algebraMap S (FractionRing S) (φ m₁) := by
    rw [eq_div_iff hm₁, ← map_mul, h₁]
  have ht' : algebraMap S (FractionRing S) t =
      algebraMap S (FractionRing S) (φ r₂) / algebraMap S (FractionRing S) (φ m₂) := by
    rw [eq_div_iff hm₂, ← map_mul, h₂]
  refine ⟨r₁ * m₂, m₁ * r₂, ?_⟩
  rw [halg, halg, hs, ht', map_mul, map_mul, map_mul, map_mul, div_div_eq_mul_div,
    div_mul_eq_mul_div,
    div_div]

theorem exists_isLocalization_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    let : Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) := (X.presheaf.stalkSpecializes
      h).hom.toAlgebra
    ∃ M : Submonoid (X.presheaf.stalk y), IsLocalization M (X.presheaf.stalk x) := by
  intro iyx
  obtain ⟨V, hV, hyV⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ y ∈ V :=
    ⟨(X.affineCover.f (X.affineCover.idx y)).opensRange, isAffineOpen_opensRange _,
      X.affineCover.covers y⟩
  have hxV : x ∈ V := h.mem_open V.2 hyV
  let ay : Algebra Γ(X, V) (X.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk
    X.presheaf ⟨y, hyV⟩
  let ax : Algebra Γ(X, V) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk
    X.presheaf ⟨x, hxV⟩
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk y) (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq'
    change (X.presheaf.germ V x hxV).hom = (X.presheaf.stalkSpecializes h).hom.comp
      (X.presheaf.germ V y hyV).hom
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hLy : IsLocalization.AtPrime (X.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  have hLx : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have hle : hV.primeIdealOf ⟨x, hxV⟩ ≤ hV.primeIdealOf ⟨y, hyV⟩ := by
    rw [PrimeSpectrum.le_iff_specializes]
    have h' : (⟨x, hxV⟩ : V) ⤳ ⟨y, hyV⟩ :=
      (V.isOpenEmbedding'.isInducing.specializes_iff).mp
        (show ((⟨x, hxV⟩ : V) : X) ⤳ ((⟨y, hyV⟩ : V) : X) from h)
    exact h'.map hV.isoSpec.hom.base.hom.continuous
  have hcompl : (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl ≤ (hV.primeIdealOf ⟨x,
    hxV⟩).asIdeal.primeCompl :=
    fun a ha hax => ha (hle hax)
  exact ⟨_, IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk y) (X.presheaf.stalk
    x) _ _ hcompl⟩

end Localizations

open Localizations in
theorem _root_.AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
    {U W : Scheme.{u}} (v : U ⟶ W) (u : U)
    [IsDomain (U.presheaf.stalk u)] [IsDomain (W.presheaf.stalk (v.base u))]
    (U' : U.Opens) [IsOpenImmersion (U'.ι ≫ v)] (hU' : ∃ x : U, x ∈ U' ∧ x ⤳ u) :
    let : Algebra (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) :=
      ((algebraMap (U.presheaf.stalk u) (FractionRing (U.presheaf.stalk u))).comp (v.stalkMap
        u).hom).toAlgebra
    IsFractionRing (W.presheaf.stalk (v.base u)) (FractionRing (U.presheaf.stalk u)) := by
  intro fractionAlgebra
  obtain ⟨x, hx, hxu⟩ := hU'
  have hvxu : v.base x ⤳ v.base u := v.base.hom.map_specializes hxu
  have : IsIso (v.stalkMap x) := by
    have hc : (U'.ι ≫ v).stalkMap ⟨x, hx⟩ = v.stalkMap x ≫ U'.ι.stalkMap ⟨x, hx⟩ :=
      Scheme.Hom.stalkMap_comp U'.ι v ⟨x, hx⟩
    have i1 : IsIso ((U'.ι ≫ v).stalkMap ⟨x, hx⟩) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion (U'.ι ≫ v)›).2 ⟨x, hx⟩
    have i2 : IsIso (U'.ι.stalkMap ⟨x, hx⟩) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion U'.ι)).2 ⟨x, hx⟩
    have i3 : IsIso (v.stalkMap x ≫ U'.ι.stalkMap ⟨x, hx⟩) := by rw [← hc]; exact i1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (v.stalkMap x) (U'.ι.stalkMap ⟨x, hx⟩) i2 i3
  let aW : Algebra (W.presheaf.stalk (v.base u)) (W.presheaf.stalk (v.base x)) :=
    (W.presheaf.stalkSpecializes hvxu).hom.toAlgebra
  let aU : Algebra (U.presheaf.stalk u) (U.presheaf.stalk x) := (U.presheaf.stalkSpecializes
    hxu).hom.toAlgebra
  obtain ⟨M, hM⟩ := exists_isLocalization_stalkSpecializes (X := W) hvxu
  obtain ⟨N, hN⟩ := exists_isLocalization_stalkSpecializes (X := U) hxu
  have hN0 : N ≤ nonZeroDivisors (U.presheaf.stalk u) := by
    intro n hn
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have hu' : IsUnit (algebraMap (U.presheaf.stalk u) (U.presheaf.stalk x) n) :=
      IsLocalization.map_units (M := N) (U.presheaf.stalk x) ⟨n, hn⟩
    rw [h0, map_zero, isUnit_zero_iff] at hu'
    exact zero_ne_one hu'
  have hβ : Function.Injective (U.presheaf.stalkSpecializes hxu).hom :=
    IsLocalization.injective (M := N) (U.presheaf.stalk x) hN0
  refine isFractionRing_of_localization_iso M (v.stalkMap u).hom (U.presheaf.stalkSpecializes
    hxu).hom hβ
    (asIso (v.stalkMap x)).commRingCatIsoToRingEquiv ?_
  intro r
  change (W.presheaf.stalkSpecializes hvxu ≫ v.stalkMap x).hom r =
    (v.stalkMap u ≫ U.presheaf.stalkSpecializes hxu).hom r
  rw [Scheme.Hom.stalkSpecializes_stalkMap]

end SchemeTheory.DVRStalks.BirationalFractionFields
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.AffineNeighborhoods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AffineCharts

variable {X : Scheme.{u}} [IsIntegral X]

lemma genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  (genericPoint_specializes x).mem_open U.isOpen hx

/-- The canonical inclusion of a stalk into the function field. -/
noncomputable def ιK (x : X) : X.presheaf.stalk x →+* X.functionField :=
  algebraMap (X.presheaf.stalk x) X.functionField

lemma ιK_apply (x : X) (w : X.presheaf.stalk x) :
    ιK x w = (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom w := rfl

lemma ιK_injective (x : X) : Function.Injective (ιK x) :=
  IsFractionRing.injective (X.presheaf.stalk x) X.functionField

/-- The image of a stalk in the function field. -/
noncomputable def O (x : X) : Subring X.functionField := (ιK x).range

lemma mem_O_iff {x : X} {k : X.functionField} : k ∈ O x ↔ ∃ w, ιK x w = k := Iff.rfl

lemma ιK_mem_O (x : X) (w : X.presheaf.stalk x) : ιK x w ∈ O x := ⟨w, rfl⟩

/-- Map sections on a nonempty open into the function field. -/
noncomputable def toK (U : X.Opens) {x : X} (hx : x ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) (genericPoint_mem hx)).hom

lemma toK_irrel (U : X.Opens) {x y : X} (hx : x ∈ U) (hy : y ∈ U) : toK U hx = toK U hy := rfl

lemma ιK_germ (U : X.Opens) {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    ιK x (X.presheaf.germ U x hx s) = toK U hx s := by
  rw [ιK_apply, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

lemma toK_mem_O (U : X.Opens) {x : X} (hx : x ∈ U) (s : Γ(X, U)) : toK U hx s ∈ O x :=
  ⟨_, ιK_germ U hx s⟩

lemma toK_injective (U : X.Opens) {x : X} (hx : x ∈ U) : Function.Injective (toK U hx) :=
  germ_injective_of_isIntegral _ _ (genericPoint_mem hx)

lemma toK_res {U V : X.Opens} (h : U ≤ V) {x : X} (hx : x ∈ U) (s : Γ(X, V)) :
    toK U hx (X.presheaf.map (homOfLE h).op s) = toK V (h hx) s := by
  simp only [toK]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

/-- A rational function represented by a unit in the given stalk. -/
def UnitAt (p : X) (k : X.functionField) : Prop := ∃ w : X.presheaf.stalk p, IsUnit w ∧ ιK p w = k

lemma UnitAt.mem {p : X} {k : X.functionField} (h : UnitAt p k) : k ∈ O p := by
  obtain ⟨w, -, rfl⟩ := h; exact ιK_mem_O p w

lemma UnitAt.ne_zero {p : X} {k : X.functionField} (h : UnitAt p k) : k ≠ 0 := by
  obtain ⟨w, hw, rfl⟩ := h
  rw [map_ne_zero_iff _ (ιK_injective p)]
  exact hw.ne_zero

lemma UnitAt.inv_mem {p : X} {k : X.functionField} (h : UnitAt p k) : k⁻¹ ∈ O p := by
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨↑(hw.unit⁻¹), ?_⟩
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, IsUnit.val_inv_mul, map_one]

lemma UnitAt.of_mem_of_inv_mem {p : X} {k : X.functionField} (hk : k ∈ O p) (hk' : k⁻¹ ∈ O p)
    (hk0 : k ≠ 0) : UnitAt p k := by
  obtain ⟨w, rfl⟩ := hk
  obtain ⟨w', hw'⟩ := hk'
  refine ⟨w, ?_, rfl⟩
  refine isUnit_iff_exists_inv.mpr ⟨w', ?_⟩
  apply ιK_injective p
  rw [map_mul, hw', map_one, mul_inv_cancel₀ hk0]

lemma UnitAt.mul {p : X} {k l : X.functionField} (hk : UnitAt p k) (hl : UnitAt p l) :
    UnitAt p (k * l) := by
  obtain ⟨w, hw, rfl⟩ := hk
  obtain ⟨w', hw', rfl⟩ := hl
  exact ⟨w * w', hw.mul hw', map_mul _ _ _⟩

lemma UnitAt.pow {p : X} {k : X.functionField} (hk : UnitAt p k) (n : ℕ) : UnitAt p (k ^ n) := by
  obtain ⟨w, hw, rfl⟩ := hk
  exact ⟨w ^ n, hw.pow n, map_pow _ _ _⟩

lemma UnitAt.inv {p : X} {k : X.functionField} (hk : UnitAt p k) : UnitAt p k⁻¹ :=
  UnitAt.of_mem_of_inv_mem hk.inv_mem (by rw [inv_inv]; exact hk.mem) (inv_ne_zero hk.ne_zero)

lemma unitAt_one (p : X) : UnitAt p 1 := ⟨1, isUnit_one, map_one _⟩

lemma UnitAt.of_isUnit_germ {U : X.Opens} {p : X} (hp : p ∈ U) {s : Γ(X, U)}
    (h : IsUnit (X.presheaf.germ U p hp s)) : UnitAt p (toK U hp s) :=
  ⟨_, h, ιK_germ U hp s⟩

lemma isUnit_germ_of_unitAt {U : X.Opens} {p : X} (hp : p ∈ U) {s : Γ(X, U)}
    (h : UnitAt p (toK U hp s)) : IsUnit (X.presheaf.germ U p hp s) := by
  obtain ⟨w, hw, hw'⟩ := h
  rw [← ιK_germ U hp s] at hw'
  rw [← ιK_injective p hw']
  exact hw

lemma UnitAt.of_subring_le {p : X} {D : Subring X.functionField} (hD : D ≤ O p)
    {k : X.functionField} (hk : k ∈ D) (hk' : k⁻¹ ∈ D) (hk0 : k ≠ 0) : UnitAt p k :=
  UnitAt.of_mem_of_inv_mem (hD hk) (hD hk') hk0

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)
include hU

lemma exists_eq_of_mem_O {p : X} (hp : p ∈ U) {z : X.functionField} (hz : z ∈ O p) :
    ∃ a b : Γ(X, U), IsUnit (X.presheaf.germ U p hp b) ∧ z * toK U hp b = toK U hp a := by
  obtain ⟨w, rfl⟩ := hz
  let : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p, hp⟩ : U)
  have : IsLocalization.AtPrime (X.presheaf.stalk p) (hU.primeIdealOf ⟨p, hp⟩).asIdeal :=
    hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl w
  have hbunit : IsUnit (X.presheaf.germ U p hp b) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl)
      (X.presheaf.stalk p) b
  refine ⟨a, b, hbunit, ?_⟩
  have hab' : w * X.presheaf.germ U p hp b = X.presheaf.germ U p hp a := hab
  rw [← ιK_germ U hp, ← ιK_germ U hp, ← map_mul, hab']

omit [IsIntegral X] in
lemma exists_point_of_prime (𝔮 : Ideal Γ(X, U)) [𝔮.IsPrime] :
    ∃ (p : X) (hp : p ∈ U), ∀ t : Γ(X, U), IsUnit (X.presheaf.germ U p hp t) ↔ t ∉ 𝔮 := by
  let q : PrimeSpectrum Γ(X, U) := ⟨𝔮, inferInstance⟩
  have hp : hU.fromSpec q ∈ U := by
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  refine ⟨hU.fromSpec q, hp, fun t => ?_⟩
  have hloc := hU.isLocalization_stalk' q hp
  have key := @IsLocalization.AtPrime.isUnit_to_map_iff Γ(X, U) _ (X.presheaf.stalk (hU.fromSpec q))
    _ (TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, hp⟩) q.asIdeal _ hloc t
  exact key

lemma mem_range_toK_basicOpen_iff (τ : Γ(X, U)) {p : X} (hp : p ∈ U)
    (hτ : IsUnit (X.presheaf.germ U p hp τ)) (k : X.functionField) :
    k ∈ (toK (X.basicOpen τ) ((X.mem_basicOpen τ p hp).mpr hτ)).range ↔
      ∃ m : ℕ, k * toK U hp τ ^ m ∈ (toK U hp).range := by
  have hpb : p ∈ X.basicOpen τ := (X.mem_basicOpen τ p hp).mpr hτ
  have : IsLocalization.Away τ Γ(X, X.basicOpen τ) := hU.isLocalization_basicOpen τ
  have hle : X.basicOpen τ ≤ U := X.basicOpen_le τ
  have hres : ∀ s : Γ(X, U), toK (X.basicOpen τ) hpb (algebraMap Γ(X, U) Γ(X, X.basicOpen τ) s)
      = toK U hp s := fun s => toK_res hle hpb s
  have hτ0 : toK U hp τ ≠ 0 := (UnitAt.of_isUnit_germ hp hτ).ne_zero
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers τ) s
    refine ⟨m, a, ?_⟩
    have h' : s * algebraMap Γ(X, U) Γ(X, X.basicOpen τ) (τ ^ m) =
        algebraMap Γ(X, U) Γ(X, X.basicOpen τ) a := h
    have := congrArg (toK (X.basicOpen τ) hpb) h'
    rw [map_mul, hres, hres, map_pow] at this
    exact this.symm
  · rintro ⟨m, a, ha⟩
    have hunit : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen τ) τ) :=
      IsLocalization.Away.algebraMap_isUnit τ
    refine ⟨algebraMap Γ(X, U) Γ(X, X.basicOpen τ) a * ↑(hunit.unit⁻¹) ^ m, ?_⟩
    have hinv : toK (X.basicOpen τ) hpb ↑(hunit.unit⁻¹) = (toK U hp τ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hres τ, ← map_mul, IsUnit.val_inv_mul, map_one]
    rw [map_mul, hres, map_pow, hinv, ha, mul_assoc, ← mul_pow, mul_inv_cancel₀ hτ0, one_pow,
      mul_one]

end Affine

/-- Identify a stalk with its image inside the function field. -/
noncomputable def stalkEquivO (p : X) : X.presheaf.stalk p ≃+* O p :=
  RingEquiv.ofBijective (ιK p).rangeRestrict
    ⟨fun _ _ hab => ιK_injective p (congrArg Subtype.val hab :),
      RingHom.rangeRestrict_surjective _⟩

lemma stalkEquivO_apply (p : X) (w : X.presheaf.stalk p) : ((stalkEquivO p w : O p) :
    X.functionField) = ιK p w :=
  rfl

lemma ιK_stalkEquivO_symm (p : X) (k : O p) : ιK p ((stalkEquivO p).symm k) = k := by
  have := stalkEquivO_apply p ((stalkEquivO p).symm k)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

section Separated

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
include f

lemma eq_of_O_eq {p p' : X} (h : O p = O p') : p = p' := by
  classical
  let e : X.presheaf.stalk p' ≃+* X.presheaf.stalk p :=
    ((stalkEquivO p').trans (RingEquiv.subringCongr h.symm)).trans (stalkEquivO p).symm
  have he : ∀ w, ιK p (e w) = ιK p' w := by
    intro w
    change ιK p ((stalkEquivO p).symm (RingEquiv.subringCongr h.symm (stalkEquivO p' w))) = _
    rw [ιK_stalkEquivO_symm]
    rfl
  let φ : X.presheaf.stalk p' ⟶ X.presheaf.stalk p := CommRingCat.ofHom e.toRingHom
  let jhom : X.presheaf.stalk p ⟶ X.functionField :=
    X.presheaf.stalkSpecializes (genericPoint_specializes p)
  have hφj : φ ≫ jhom = X.presheaf.stalkSpecializes (genericPoint_specializes p') := by
    ext w
    change ιK p (e w) = ιK p' w
    exact he w
  let g₁ : Spec (X.presheaf.stalk p) ⟶ X := X.fromSpecStalk p
  let g₂ : Spec (X.presheaf.stalk p) ⟶ X := Spec.map φ ≫ X.fromSpecStalk p'
  let j : Spec X.functionField ⟶ Spec (X.presheaf.stalk p) := Spec.map jhom
  have hj₁ : j ≫ g₁ = X.fromSpecStalk (genericPoint X) := by
    simp only [j, g₁, jhom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hj₂ : j ≫ g₂ = X.fromSpecStalk (genericPoint X) := by
    simp only [j, g₂]
    rw [← Category.assoc, ← Spec.map_comp, hφj, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have : IsDominant j := by
    refine ⟨?_⟩
    have : DenseRange (PrimeSpectrum.comap jhom.hom) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      have : RingHom.ker jhom.hom = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp (ιK_injective p)
      rw [this]
      exact bot_le
    exact this
  have hjg : j ≫ g₁ = j ≫ g₂ := hj₁.trans hj₂.symm
  have hfg : g₁ ≫ f = g₂ ≫ f :=
    ext_of_isDominant (f := g₁ ≫ f) (g := g₂ ≫ f) j (by rw [← Category.assoc, ← Category.assoc,
      hjg])
  have hg : g₁ = g₂ := ext_of_isDominant_of_isSeparated f hfg j hjg
  have h1 : g₁ (IsLocalRing.closedPoint (X.presheaf.stalk p)) = p :=
    Scheme.fromSpecStalk_closedPoint
  have h2 : g₂ (IsLocalRing.closedPoint (X.presheaf.stalk p)) = p' := by
    have : IsLocalHom φ.hom := isLocalHom_toRingHom e
    exact (congrArg (fun q : Spec (X.presheaf.stalk p') => X.fromSpecStalk p' q)
      (Spec_closedPoint (f := φ))).trans Scheme.fromSpecStalk_closedPoint
  rw [← h1, ← h2, hg]

end Separated

section FieldSubring

variable {K : Type*} [Field K]

/-- Adjoin the inverse of a single element to a subring. -/
def adjInv (C : Subring K) (s : K) : Subring K := Subring.closure (insert s⁻¹ (C : Set K))

lemma le_adjInv (C : Subring K) (s : K) : C ≤ adjInv C s := fun _ hx =>
  Subring.subset_closure (Set.mem_insert_of_mem _ hx)

lemma inv_mem_adjInv (C : Subring K) (s : K) : s⁻¹ ∈ adjInv C s :=
  Subring.subset_closure (Set.mem_insert _ _)

lemma adjInv_le {C D : Subring K} {s : K} (hCD : C ≤ D) (hs : s⁻¹ ∈ D) : adjInv C s ≤ D :=
  Subring.closure_le.mpr (Set.insert_subset_iff.mpr ⟨hs, hCD⟩)

lemma mem_adjInv_iff {C : Subring K} {s : K} (hs : s ∈ C) (hs0 : s ≠ 0) (k : K) :
    k ∈ adjInv C s ↔ ∃ m : ℕ, k * s ^ m ∈ C := by
  constructor
  · intro hk
    refine Subring.closure_induction (p := fun k _ => ∃ m : ℕ, k * s ^ m ∈ C) ?_ ?_ ?_ ?_ ?_ ?_ hk
    · rintro x (rfl | hx)
      · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hs0]; exact C.one_mem⟩
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hx⟩
    · exact ⟨0, by rw [zero_mul]; exact C.zero_mem⟩
    · exact ⟨0, by rw [pow_zero, mul_one]; exact C.one_mem⟩
    · rintro x y _ _ ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      have : (x + y) * s ^ (m + n) = x * s ^ m * s ^ n + y * s ^ n * s ^ m := by ring
      rw [this]
      exact C.add_mem (C.mul_mem hm (C.pow_mem hs n)) (C.mul_mem hn (C.pow_mem hs m))
    · rintro x _ ⟨m, hm⟩
      exact ⟨m, by rw [neg_mul]; exact C.neg_mem hm⟩
    · rintro x y _ _ ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      have : x * y * s ^ (m + n) = (x * s ^ m) * (y * s ^ n) := by ring
      rw [this]; exact C.mul_mem hm hn
  · rintro ⟨m, hm⟩
    have : k = (k * s ^ m) * (s⁻¹) ^ m := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hs0), mul_one]
    rw [this]
    exact (adjInv C s).mul_mem (le_adjInv C s hm) ((adjInv C s).pow_mem (inv_mem_adjInv C s) m)

lemma mul_pow_mem_of_le {C : Subring K} {s : K} (hs : s ∈ C) {k : K} {m n : ℕ} (hmn : m ≤ n)
    (hk : k * s ^ m ∈ C) : k * s ^ n ∈ C := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, ← mul_assoc]
  exact C.mul_mem hk (C.pow_mem hs d)

lemma adjInv_adjInv_eq {C : Subring K} {e c : K} (he : e ∈ C) (hc : c ∈ C) (he0 : e ≠ 0)
    (hc0 : c ≠ 0) : adjInv (adjInv C e) c = adjInv C (e * c) := by
  apply le_antisymm
  · apply adjInv_le (adjInv_le (le_adjInv _ _) ?_) ?_
    · have : e⁻¹ = c * (e * c)⁻¹ := by field_simp
      rw [this]; exact Subring.mul_mem _ (le_adjInv _ _ hc) (inv_mem_adjInv _ _)
    · have : c⁻¹ = e * (e * c)⁻¹ := by field_simp
      rw [this]; exact Subring.mul_mem _ (le_adjInv _ _ he) (inv_mem_adjInv _ _)
  · apply adjInv_le ((le_adjInv C e).trans (le_adjInv _ c))
    rw [mul_inv]
    exact Subring.mul_mem _ (le_adjInv _ _ (inv_mem_adjInv C e)) (inv_mem_adjInv _ _)

end FieldSubring

lemma mem_O_or_inv_mem (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (k : X.functionField) : k ∈ O x ∨ k⁻¹ ∈ O x := by
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) k with h | h
  · exact Or.inl (RingHom.mem_rangeS.mp h)
  · exact Or.inr (RingHom.mem_rangeS.mp h)

/-- The valuation subring determined by a discrete valuation stalk. -/
noncomputable def Ov (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    ValuationSubring X.functionField :=
  ⟨O x, mem_O_or_inv_mem x⟩

lemma mem_Ov_iff (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] (k : X.functionField) :
    k ∈ Ov x ↔ k ∈ O x := Iff.rfl

scoped instance (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    IsDiscreteValuationRing (Ov x) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (show X.presheaf.stalk x ≃+* Ov x from stalkEquivO x)

lemma mem_nonunits_Ov_iff (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (k : X.functionField) : k ∈ (Ov x).nonunits ↔ k ∈ O x ∧ ¬ UnitAt x k := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hk, hmax⟩
    refine ⟨hk, fun hu => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff] at hmax
    apply hmax
    obtain ⟨w, hw, hwa⟩ := hu
    have : (stalkEquivO x) w = ⟨k, hk⟩ := Subtype.ext (by rw [stalkEquivO_apply]; exact hwa)
    have hu' : IsUnit ((stalkEquivO x) w) := hw.map _
    rw [this] at hu'
    exact hu'
  · rintro ⟨hk, hku⟩
    refine ⟨hk, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    intro hu
    apply hku
    have hu' : IsUnit ((stalkEquivO x).symm ⟨k, hk⟩) := hu.map _
    exact ⟨_, hu', ιK_stalkEquivO_symm x ⟨k, hk⟩⟩

lemma valuationSubring_eq_of_le {L : Type*} [Field L] {A B : ValuationSubring L}
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] (h : A ≤ B) : A = B := by
  rcases ValuationSubring.eq_self_or_eq_top_of_le h with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hϖ0 : (ϖ : L) ≠ 0 := by
      intro h0; apply hϖ.ne_zero; exact_mod_cast h0
    have hinv : (ϖ : L)⁻¹ ∈ B := h1.ge (ValuationSubring.mem_top _)
    apply hϖ.not_isUnit
    refine ⟨⟨ϖ, ⟨(ϖ : L)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (ϖ : L) * (ϖ : L)⁻¹ = 1
      exact mul_inv_cancel₀ hϖ0
    · apply Subtype.ext
      change (ϖ : L)⁻¹ * (ϖ : L) = 1
      exact inv_mul_cancel₀ hϖ0

lemma exists_forall_pow_mul_mem (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {s : X.functionField} (hs : s ∈ O x) (hsu : ¬ UnitAt x s) (w : X.functionField) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → s ^ n * w ∈ O x := by
  by_cases hw : w ∈ O x
  · exact ⟨0, fun n _ => (O x).mul_mem ((O x).pow_mem hs n) hw⟩
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (O x).zero_mem
  have hwinv : w⁻¹ ∈ O x := (mem_O_or_inv_mem x w).resolve_left hw
  by_cases hs0 : s = 0
  · refine ⟨1, fun n hn => ?_⟩
    subst hs0
    rw [zero_pow (by omega), zero_mul]
    exact (O x).zero_mem
  obtain ⟨t, ht⟩ := hwinv
  obtain ⟨z, rfl⟩ := hs
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at ht; exact inv_ne_zero hw0 ht.symm
  have hzmem : z ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    intro hu; exact hsu ⟨z, hu, rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
  have hspan : Ideal.span ({t} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact ⟨u⁻¹, by rw [hk, mul_assoc, mul_comm (ϖ ^ k), ← mul_assoc, Units.mul_inv, one_mul]⟩
  have hzk : z ^ k ∈ Ideal.span ({t} : Set (X.presheaf.stalk x)) := by
    rw [hspan]; exact Ideal.pow_mem_pow hzmem k
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hzk
  refine ⟨k, fun n hn => ?_⟩
  have hzkw : ιK x z ^ k * w = ιK x c := by
    rw [← map_pow, ← hc, map_mul, ht, mul_assoc, inv_mul_cancel₀ hw0, mul_one]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, mul_comm (ιK x z ^ k), mul_assoc, hzkw, ← map_pow, ← map_mul]
  exact ιK_mem_O x _

section Endgame

/-- Map sections to a stalk whose image contains their rational functions. -/
noncomputable def toStalkOfLE {W : X.Opens} {x : X} (hx : x ∈ W) {p : X}
    (h : (toK W hx).range ≤ O p) : Γ(X, W) →+* X.presheaf.stalk p :=
  (stalkEquivO p).symm.toRingHom.comp
    ((toK W hx).codRestrict (O p) (fun σ => h ⟨σ, rfl⟩))

lemma ιK_toStalkOfLE {W : X.Opens} {x : X} (hx : x ∈ W) {p : X}
    (h : (toK W hx).range ≤ O p) (σ : Γ(X, W)) : ιK p (toStalkOfLE hx h σ) = toK W hx σ := by
  simp only [toStalkOfLE, RingHom.coe_comp, Function.comp_apply]
  exact ιK_stalkEquivO_symm p _

lemma isUnit_toStalkOfLE_iff {W : X.Opens} {x : X} (hx : x ∈ W) {p : X}
    (h : (toK W hx).range ≤ O p) (σ : Γ(X, W)) :
    IsUnit (toStalkOfLE hx h σ) ↔ UnitAt p (toK W hx σ) := by
  constructor
  · intro hu; exact ⟨_, hu, ιK_toStalkOfLE hx h σ⟩
  · rintro ⟨w, hw, hw'⟩
    rw [← ιK_toStalkOfLE hx h σ] at hw'
    rw [← ιK_injective p hw']
    exact hw

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
include f

lemma mem_chart_of_unitAt (C : Subring X.functionField)
    {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hxW : x ∈ W) {ex c : X.functionField}
    (hc : c ∈ C) (hc0 : c ≠ 0)
    (hrange : (toK W hxW).range = adjInv C (ex * c))
    {W' : X.Opens} (hW' : IsAffineOpen W') {y : X} (hyW' : y ∈ W') {ey : X.functionField}
    (hey : ey ∈ C) (hey0 : ey ≠ 0) (hrange' : (toK W' hyW').range = adjInv C (ey * c))
    {p : X} (hp : p ∈ W') (hunit : UnitAt p ex) : p ∈ W := by
  classical
  have hDy : adjInv C (ey * c) ≤ O p := by
    rw [← hrange']; rintro _ ⟨σ, rfl⟩; exact toK_mem_O W' hp σ
  have hCOp : C ≤ O p := (le_adjInv C _).trans hDy
  have heyc : UnitAt p (ey * c) :=
    UnitAt.of_subring_le hDy (le_adjInv _ _ (C.mul_mem hey hc)) (inv_mem_adjInv _ _)
      (mul_ne_zero hey0 hc0)
  have hcu : UnitAt p c := by
    refine UnitAt.of_subring_le hDy (le_adjInv _ _ hc) ?_ hc0
    have : c⁻¹ = ey * (ey * c)⁻¹ := by field_simp
    rw [this]; exact Subring.mul_mem _ (le_adjInv _ _ hey) (inv_mem_adjInv _ _)
  have hexc : UnitAt p (ex * c) := hunit.mul hcu
  have hDx : adjInv C (ex * c) ≤ O p := adjInv_le hCOp hexc.inv_mem
  have hDx' : (toK W hxW).range ≤ O p := hrange ▸ hDx
  let ψ := toStalkOfLE hxW hDx'
  let 𝔮 : Ideal Γ(X, W) := Ideal.comap ψ (IsLocalRing.maximalIdeal (X.presheaf.stalk p))
  have : 𝔮.IsPrime := Ideal.comap_isPrime ψ _
  obtain ⟨p', hp', hunits⟩ := exists_point_of_prime hW 𝔮
  have star : ∀ t : Γ(X, W), IsUnit (X.presheaf.germ W p' hp' t) ↔ UnitAt p (toK W hxW t) := by
    intro t
    rw [hunits t, ← isUnit_toStalkOfLE_iff hxW hDx' t]
    change ψ t ∉ IsLocalRing.maximalIdeal _ ↔ _
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not]
  have hOO : O p' = O p := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, b, hb, hab⟩ := exists_eq_of_mem_O hW hp' hz
      have hbu : UnitAt p (toK W hxW b) := (star b).mp hb
      have hz' : z = toK W hxW a * (toK W hxW b)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hbu.ne_zero]; exact hab
      rw [hz']
      exact (O p).mul_mem (hDx' ⟨a, rfl⟩) hbu.inv_mem
    · intro z hz
      obtain ⟨a, b, hb, hab⟩ := exists_eq_of_mem_O hW' hp hz
      have heyc' : ey * c ∈ C := C.mul_mem hey hc
      have ha : toK W' hyW' a ∈ adjInv C (ey * c) := hrange' ▸ ⟨a, rfl⟩
      have hb' : toK W' hyW' b ∈ adjInv C (ey * c) := hrange' ▸ ⟨b, rfl⟩
      obtain ⟨m, hm⟩ := (mem_adjInv_iff heyc' (mul_ne_zero hey0 hc0) _).mp ha
      obtain ⟨n, hn⟩ := (mem_adjInv_iff heyc' (mul_ne_zero hey0 hc0) _).mp hb'
      have hm' := mul_pow_mem_of_le heyc' (Nat.le_add_right m n) hm
      have hn' := mul_pow_mem_of_le heyc' (Nat.le_add_left n m) hn
      set c₁ := toK W' hyW' a * (ey * c) ^ (m + n) with hc₁
      set c₂ := toK W' hyW' b * (ey * c) ^ (m + n) with hc₂
      have hc₂u : UnitAt p c₂ := (UnitAt.of_isUnit_germ hp hb).mul (heyc.pow _)
      have hc₁W : c₁ ∈ (toK W hxW).range := hrange ▸ le_adjInv _ _ hm'
      have hc₂W : c₂ ∈ (toK W hxW).range := hrange ▸ le_adjInv _ _ hn'
      obtain ⟨t₁, ht₁⟩ := hc₁W
      obtain ⟨t₂, ht₂⟩ := hc₂W
      have ht₂u : IsUnit (X.presheaf.germ W p' hp' t₂) := (star t₂).mpr (ht₂ ▸ hc₂u)
      have hz' : z = c₁ * c₂⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hc₂u.ne_zero, hc₁, hc₂, ← mul_assoc]
        exact congrArg (· * (ey * c) ^ (m + n)) hab
      rw [hz', ← ht₁, ← ht₂]
      exact (O p').mul_mem (toK_mem_O W hp' t₁) (UnitAt.of_isUnit_germ hp' ht₂u).inv_mem
  rw [← eq_of_O_eq f hOO]
  exact hp'

omit f in
lemma exists_section_of_mem_adjInv (S : Finset X) (C : Subring X.functionField)
    (e : X → X.functionField) (c : X.functionField)
    (he : ∀ x ∈ S, e x ∈ C) (he0 : ∀ x ∈ S, e x ≠ 0) (hc0 : c ≠ 0)
    (W : X → X.Opens) (hxW : ∀ x ∈ S, x ∈ W x)
    (hrange : ∀ x (hx : x ∈ S), (toK (W x) (hxW x hx)).range = adjInv C (e x * c))
    {x₀ : X} (hx₀ : x₀ ∈ S) (k : X.functionField) (hk : k ∈ adjInv C c) :
    ∃ σ : Γ(X, ⨆ x ∈ S, W x),
      toK (⨆ x ∈ S, W x) (Opens.mem_iSup.mpr ⟨x₀, Opens.mem_iSup.mpr ⟨hx₀, hxW x₀ hx₀⟩⟩) σ = k := by
  classical
  let V : X.Opens := ⨆ x ∈ S, W x
  have hV₀ : x₀ ∈ V := Opens.mem_iSup.mpr ⟨x₀, Opens.mem_iSup.mpr ⟨hx₀, hxW x₀ hx₀⟩⟩
  have hloc : ∀ x (hx : x ∈ S), ∃ σ : Γ(X, W x), toK (W x) (hxW x hx) σ = k := by
    intro x hx
    have hk' : k ∈ adjInv C (e x * c) := by
      refine adjInv_le (le_adjInv C _) ?_ hk
      have : c⁻¹ = e x * (e x * c)⁻¹ := by field_simp [he0 x hx]
      rw [this]; exact Subring.mul_mem _ (le_adjInv _ _ (he x hx)) (inv_mem_adjInv _ _)
    rw [← hrange x hx] at hk'
    exact hk'
  let U' : S → X.Opens := fun i => W i
  let sf : ∀ i : S, Γ(X, U' i) := fun i => (hloc i i.2).choose
  have hsf : ∀ i : S, toK (W i) (hxW i i.2) (sf i) = k := fun i => (hloc i i.2).choose_spec
  have hcover : V ≤ iSup U' := by
    intro p hp
    obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hp
    obtain ⟨hxS, hpx⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hxS⟩, hpx⟩
  let iUV : ∀ i : S, U' i ⟶ V := fun i => homOfLE (by
    intro p hp; exact Opens.mem_iSup.mpr ⟨(i : X), Opens.mem_iSup.mpr ⟨i.2, hp⟩⟩)
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U' sf := by
    intro i j
    have hη : genericPoint X ∈ U' i ⊓ U' j :=
      ⟨genericPoint_mem (hxW i i.2), genericPoint_mem (hxW j j.2)⟩
    apply toK_injective (U' i ⊓ U' j) hη
    change toK (U' i ⊓ U' j) hη (X.presheaf.map (homOfLE inf_le_left).op (sf i)) =
      toK (U' i ⊓ U' j) hη (X.presheaf.map (homOfLE inf_le_right).op (sf j))
    rw [toK_res inf_le_left hη, toK_res inf_le_right hη]
    exact ((hsf i).trans (hsf j).symm :)
  obtain ⟨gl, hgl, -⟩ :
      ∃ gl : Γ(X, V), (∀ i, (X.sheaf.1.map (iUV i).op) gl = sf i) ∧ _ :=
    X.sheaf.existsUnique_gluing' U' V iUV hcover sf hcompat
  refine ⟨gl, ?_⟩
  have h1 : toK V hV₀ gl = toK (W x₀) (hxW x₀ hx₀) (X.presheaf.map (iUV ⟨x₀, hx₀⟩).op gl) :=
    (toK_res (iUV ⟨x₀, hx₀⟩).le (hxW x₀ hx₀) gl).symm
  rw [h1]
  exact (congrArg (toK (W x₀) (hxW x₀ hx₀)) (hgl ⟨x₀, hx₀⟩)).trans (hsf ⟨x₀, hx₀⟩)

lemma isAffineOpen_iSup_of_charts (S : Finset X) (hSne : S.Nonempty)
    (C : Subring X.functionField) (e : X → X.functionField) (c : X.functionField)
    (he : ∀ x ∈ S, e x ∈ C) (hc : c ∈ C) (he0 : ∀ x ∈ S, e x ≠ 0) (hc0 : c ≠ 0)
    (α : X → X.functionField) (hα : ∀ x ∈ S, α x ∈ C) (hsum : ∑ x ∈ S, α x * e x = c)
    (W : X → X.Opens) (hW : ∀ x ∈ S, IsAffineOpen (W x)) (hxW : ∀ x ∈ S, x ∈ W x)
    (hrange : ∀ x (hx : x ∈ S), (toK (W x) (hxW x hx)).range = adjInv C (e x * c)) :
    IsAffineOpen (⨆ x ∈ S, W x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hSne
  let V : X.Opens := ⨆ x ∈ S, W x
  have hV₀ : x₀ ∈ V := Opens.mem_iSup.mpr ⟨x₀, Opens.mem_iSup.mpr ⟨hx₀, hxW x₀ hx₀⟩⟩
  have hWV : ∀ x ∈ S, W x ≤ V := fun x hx p hp =>
    Opens.mem_iSup.mpr ⟨x, Opens.mem_iSup.mpr ⟨hx, hp⟩⟩
  have hsecε : ∀ x ∈ S, ∃ ε : Γ(X, V), toK V hV₀ ε = e x := fun x hx =>
    exists_section_of_mem_adjInv S C e c he he0 hc0 W hxW hrange hx₀ (e x)
      (le_adjInv C c (he x hx))
  have hsecβ : ∀ x ∈ S, ∃ β : Γ(X, V), toK V hV₀ β = α x * c⁻¹ := fun x hx =>
    exists_section_of_mem_adjInv S C e c he he0 hc0 W hxW hrange hx₀ (α x * c⁻¹)
      (Subring.mul_mem _ (le_adjInv C c (hα x hx)) (inv_mem_adjInv C c))
  choose! ε hε using hsecε
  choose! β hβ using hsecβ
  have hone : ∑ x ∈ S, β x * ε x = 1 := by
    apply toK_injective V hV₀
    rw [map_sum, map_one]
    have : ∀ x ∈ S, toK V hV₀ (β x * ε x) = α x * e x * c⁻¹ := by
      intro x hx; rw [map_mul, hβ x hx, hε x hx]; ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hsum, mul_inv_cancel₀ hc0]
  have hspan : Ideal.span (Set.range fun x : S => ε x) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hone]
    refine Ideal.sum_mem _ (fun x hx => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩))
  have hbasic : ∀ x ∈ S, X.basicOpen (ε x) = W x := by
    intro x hx
    ext p
    constructor
    · intro hp
      have hpV : p ∈ V := X.basicOpen_le (ε x) hp
      have hu : IsUnit (X.presheaf.germ V p hpV (ε x)) := (X.mem_basicOpen (ε x) p hpV).mp hp
      have hunit : UnitAt p (e x) := by
        rw [← hε x hx]; exact UnitAt.of_isUnit_germ hpV hu
      obtain ⟨y, hy⟩ := Opens.mem_iSup.mp hpV
      obtain ⟨hyS, hpy⟩ := Opens.mem_iSup.mp hy
      exact mem_chart_of_unitAt f C (hW x hx) (hxW x hx) hc hc0 (hrange x hx)
        (hW y hyS) (hxW y hyS) (he y hyS) (he0 y hyS) (hrange y hyS) hpy hunit
    · intro hp
      have hpV : p ∈ V := hWV x hx hp
      apply (X.mem_basicOpen (ε x) p hpV).mpr
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWV x hx)) p hp (ε x)]
      apply RingHom.isUnit_map
      set εx := X.presheaf.map (homOfLE (hWV x hx)).op (ε x) with hεx
      have hεxK : toK (W x) (hxW x hx) εx = e x := by
        rw [hεx, toK_res (hWV x hx) (hxW x hx)]; exact hε x hx
      have hinv : (e x)⁻¹ ∈ (toK (W x) (hxW x hx)).range := by
        rw [hrange x hx]
        have : (e x)⁻¹ = c * (e x * c)⁻¹ := by field_simp [he0 x hx]
        rw [this]; exact Subring.mul_mem _ (le_adjInv _ _ hc) (inv_mem_adjInv _ _)
      obtain ⟨ι', hι'⟩ := hinv
      refine isUnit_iff_exists_inv.mpr ⟨ι', ?_⟩
      apply toK_injective (W x) (hxW x hx)
      rw [map_mul, hεxK, hι', map_one, mul_inv_cancel₀ (he0 x hx)]
  apply isAffineOpen_of_isAffineOpen_basicOpen V (Set.range fun x : S => ε x) hspan
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  change IsAffineOpen (X.basicOpen (ε x))
  rw [hbasic x hx]
  exact hW x hx

end Endgame

section Main

lemma unitAt_prod {p : X} {ι : Type*} (s : Finset ι) (g : ι → X.functionField)
    (h : ∀ i ∈ s, UnitAt p (g i)) : UnitAt p (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using unitAt_one p
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Map a subring of the function field to a stalk containing it. -/
noncomputable def toStalk' {p : X} {D : Subring X.functionField} (h : D ≤ O p) :
    D →+* X.presheaf.stalk p :=
  (stalkEquivO p).symm.toRingHom.comp (Subring.inclusion h)

lemma ιK_toStalk' {p : X} {D : Subring X.functionField} (h : D ≤ O p) (d : D) :
    ιK p (toStalk' h d) = d := by
  simp only [toStalk', RingHom.coe_comp, Function.comp_apply]
  exact ιK_stalkEquivO_symm p _

lemma isUnit_toStalk'_iff {p : X} {D : Subring X.functionField} (h : D ≤ O p) (d : D) :
    IsUnit (toStalk' h d) ↔ UnitAt p d := by
  constructor
  · intro hu; exact ⟨_, hu, ιK_toStalk' h d⟩
  · rintro ⟨w, hw, hw'⟩
    rw [← ιK_toStalk' h d] at hw'
    rw [← ιK_injective p hw']
    exact hw

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
include f

lemma exists_unit_mul_mem (S : Finset X) (hS : ∀ x ∈ S, IsDiscreteValuationRing (X.presheaf.stalk
    x))
    {x : X} (hx : x ∈ S) {z : X.functionField} (hz : z ∈ O x) :
    ∃ s : X.functionField, UnitAt x s ∧ (∀ y ∈ S, s ∈ O y) ∧ ∀ y ∈ S, s * z ∈ O y := by
  classical
  have hS' : ∀ y : S, IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := fun y => hS y y.2
  have hxI : IsDiscreteValuationRing (X.presheaf.stalk x) := hS x hx
  let V : S → ValuationSubring X.functionField := fun y => Ov (y : X)
  have hV : ∀ i j : S, V i ≤ V j → i = j := by
    intro i j hij
    have heq : V i = V j := valuationSubring_eq_of_le hij
    have hO : O (i : X) = O (j : X) := by
      ext k
      exact (mem_Ov_iff (i : X) k).symm.trans ((SetLike.ext_iff.mp heq k).trans (mem_Ov_iff (j :
        X) k))
    exact Subtype.ext (eq_of_O_eq f hO)
  let a : S → X.functionField := fun y => if (y : X) = x then 1 else 0
  have ha : ∀ i, a i ∈ V i := by
    intro i
    by_cases h : (i : X) = x
    · simp only [a, ite_eq_left h]; exact (V i).one_mem
    · simp only [a, ite_eq_right h]; exact (V i).zero_mem
  obtain ⟨s₀, hs₀⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits V hV a ha
  have hs₀O : ∀ y ∈ S, s₀ ∈ O y := fun y hy => (hs₀ ⟨y, hy⟩).1
  have hxu : UnitAt x s₀ := by
    obtain ⟨h1, h2⟩ := hs₀ ⟨x, hx⟩
    have h2' : s₀ - 1 ∈ (Ov x).nonunits := by simpa only [a, ite_eq_left rfl] using h2
    rw [mem_nonunits_Ov_iff] at h2'
    obtain ⟨w, hw⟩ := (h1 : s₀ ∈ O x)
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self w with hu | hu
    · exact ⟨w, hu, hw⟩
    · exfalso
      apply h2'.2
      refine ⟨-(1 - w), hu.neg, ?_⟩
      rw [map_neg, map_sub, map_one, hw]; ring
  have harch : ∀ y ∈ S, ∃ N : ℕ, ∀ n, N ≤ n → s₀ ^ n * z ∈ O y := by
    intro y hy
    have : IsDiscreteValuationRing (X.presheaf.stalk y) := hS y hy
    by_cases hyx : y = x
    · subst hyx
      exact ⟨0, fun n _ => (O y).mul_mem ((O y).pow_mem (hs₀O y hy) n) hz⟩
    · obtain ⟨h1, h2⟩ := hs₀ ⟨y, hy⟩
      have h2' : s₀ ∈ (Ov y).nonunits := by
        simpa only [a, ite_eq_right hyx, sub_zero] using h2
      rw [mem_nonunits_Ov_iff] at h2'
      exact exists_forall_pow_mul_mem y h2'.1 h2'.2 z
  choose! N hN using harch
  refine ⟨s₀ ^ (S.sup N), hxu.pow _, fun y hy => (O y).pow_mem (hs₀O y hy) _, fun y hy => ?_⟩
  exact hN y hy _ (Finset.le_sup hy)

variable [LocallyOfFiniteType f]

/-- The image of the base ring inside the function field. -/
noncomputable def R0 : Subring X.functionField :=
  ((toK (f ⁻¹ᵁ ⊤) (show genericPoint X ∈ f ⁻¹ᵁ ⊤ from trivial)).comp (f.app ⊤).hom).range

omit [IsSeparated f] [LocallyOfFiniteType f] in
lemma R0_le_range {U : X.Opens} {x : X} (hx : x ∈ U) : R0 f ≤ (toK U hx).range := by
  rintro _ ⟨r, rfl⟩
  have e : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨X.presheaf.map (homOfLE e).op (f.app ⊤ r), ?_⟩
  rw [toK_res e hx]
  rfl

omit [IsSeparated f] [LocallyOfFiniteType f] in
lemma R0_le_O (y : X) : R0 f ≤ O y := by
  rintro _ ⟨r, rfl⟩
  exact toK_mem_O (f ⁻¹ᵁ ⊤) (show y ∈ f ⁻¹ᵁ ⊤ from trivial) _

omit [IsSeparated f] in
lemma exists_finset_gen {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    ∃ G : Finset X.functionField, (↑G : Set X.functionField) ⊆ (toK U hx).range ∧
      (toK U hx).range ≤ Subring.closure ((R0 f : Set X.functionField) ∪ ↑G) := by
  classical
  have e : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hft : (f.appLE ⊤ U e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  let alg : Algebra Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U) := (f.appLE ⊤ U e).hom.toAlgebra
  have hfg : (⊤ : Subalgebra Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U)).FG := hft.out
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t.image (toK U hx), ?_, ?_⟩
  · rw [Finset.coe_image]; exact Set.image_subset_range _ _
  · rintro _ ⟨σ, rfl⟩
    have hσ : σ ∈ Algebra.adjoin Γ(Spec (CommRingCat.of R), ⊤) (↑t : Set Γ(X, U)) := by
      rw [ht]; exact Algebra.mem_top
    rw [Algebra.mem_adjoin_iff] at hσ
    have : toK U hx σ ∈ (Subring.closure (Set.range (algebraMap Γ(Spec (CommRingCat.of R), ⊤)
        Γ(X, U)) ∪ ↑t)).map (toK U hx) := ⟨σ, hσ, rfl⟩
    rw [RingHom.map_closure] at this
    refine Subring.closure_mono ?_ this
    rintro _ ⟨τ, hτ | hτ, rfl⟩
    · left
      obtain ⟨r, rfl⟩ := hτ
      refine ⟨r, ?_⟩
      change toK (f ⁻¹ᵁ ⊤) _ (f.app ⊤ r) = toK U hx (X.presheaf.map (homOfLE e).op (f.app ⊤ r))
      rw [toK_res e hx]
      rfl
    · right
      rw [Finset.coe_image]; exact ⟨τ, hτ, rfl⟩

theorem main (S : Finset X) (hS : ∀ x ∈ S, IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨⊥, isAffineOpen_bot X, fun x hx => (Finset.notMem_empty x hx).elim⟩
  obtain ⟨x₀, hx₀⟩ := hSne
  have hU : ∀ x ∈ S, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x _ =>
    let ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    ⟨U, hU, hxU⟩
  choose! U hUaff hxU using hU
  have hG : ∀ x (hx : x ∈ S), ∃ G : Finset X.functionField,
      (↑G : Set X.functionField) ⊆ (toK (U x) (hxU x hx)).range ∧
      (toK (U x) (hxU x hx)).range ≤ Subring.closure ((R0 f : Set X.functionField) ∪ ↑G) :=
    fun x hx => exists_finset_gen f (hUaff x hx) (hxU x hx)
  choose! G hGsub hGgen using hG
  have happ : ∀ x ∈ S, ∀ g ∈ G x, ∃ s : X.functionField,
      UnitAt x s ∧ (∀ y ∈ S, s ∈ O y) ∧ ∀ y ∈ S, s * g ∈ O y := by
    intro x hx g hg
    have hgO : g ∈ O x := by
      obtain ⟨σ, hσ⟩ := hGsub x hx hg
      rw [← hσ]; exact toK_mem_O _ (hxU x hx) σ
    exact exists_unit_mul_mem f S hS hx hgO
  choose! s hsu hsO hsgO using happ
  let F : Finset X.functionField :=
    S.biUnion fun x => (G x).image (s x) ∪ (G x).image (fun g => s x g * g)
  let C : Subring X.functionField := Subring.closure ((R0 f : Set _) ∪ ↑F)
  have hFO : ∀ y ∈ S, (↑F : Set X.functionField) ⊆ O y := by
    intro y hy k hk
    simp only [F, Finset.coe_biUnion, Finset.coe_union, Finset.coe_image, Set.mem_iUnion,
      Set.mem_union, Set.mem_image, Finset.mem_coe] at hk
    obtain ⟨x, hx, ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩⟩ := hk
    · exact hsO x hx g hg y hy
    · exact hsgO x hx g hg y hy
  have hCO : ∀ y ∈ S, C ≤ O y := fun y hy =>
    Subring.closure_le.mpr (Set.union_subset (R0_le_O f y) (hFO y hy))
  have hFC : (↑F : Set X.functionField) ⊆ C := fun k hk => Subring.subset_closure (Or.inr hk)
  have hsC : ∀ x ∈ S, ∀ g ∈ G x, s x g ∈ C := by
    intro x hx g hg
    apply hFC
    simp only [F, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, Finset.coe_union,
      Finset.coe_image, Set.mem_union, Set.mem_image]
    exact ⟨x, hx, Or.inl ⟨g, hg, rfl⟩⟩
  have hsgC : ∀ x ∈ S, ∀ g ∈ G x, s x g * g ∈ C := by
    intro x hx g hg
    apply hFC
    simp only [F, Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, Finset.coe_union,
      Finset.coe_image, Set.mem_union, Set.mem_image]
    exact ⟨x, hx, Or.inr ⟨g, hg, rfl⟩⟩
  let sx : X → X.functionField := fun x => ∏ g ∈ G x, s x g
  have hsxC : ∀ x ∈ S, sx x ∈ C := fun x hx => C.prod_mem (fun g hg => hsC x hx g hg)
  have hsxu : ∀ x ∈ S, UnitAt x (sx x) := fun x hx => unitAt_prod _ _ (fun g hg => hsu x hx g hg)
  have hsx0 : ∀ x ∈ S, sx x ≠ 0 := fun x hx => (hsxu x hx).ne_zero
  have hBle : ∀ x (hx : x ∈ S), (toK (U x) (hxU x hx)).range ≤ adjInv C (sx x) := by
    intro x hx
    refine (hGgen x hx).trans (Subring.closure_le.mpr (Set.union_subset ?_ ?_))
    · exact fun k hk => le_adjInv C _ (Subring.subset_closure (Or.inl hk))
    · intro g hg
      have hg' : g ∈ G x := hg
      have hs0 : s x g ≠ 0 := (hsu x hx g hg').ne_zero
      have hP0 : (∏ g' ∈ (G x).erase g, s x g') ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun g' hg'' => (hsu x hx g' (Finset.mem_of_mem_erase
          hg'')).ne_zero
      have : g = (s x g * g) * ((∏ g' ∈ (G x).erase g, s x g') * (sx x)⁻¹) := by
        have hprod : sx x = s x g * ∏ g' ∈ (G x).erase g, s x g' :=
          (Finset.mul_prod_erase (G x) (s x) hg').symm
        rw [hprod]
        field_simp
      rw [this]
      refine Subring.mul_mem _ (le_adjInv _ _ (hsgC x hx g hg')) (Subring.mul_mem _ ?_
        (inv_mem_adjInv _ _))
      exact le_adjInv _ _ (C.prod_mem fun g' hg'' => hsC x hx g' (Finset.mem_of_mem_erase hg''))
  have hab : ∀ x (hx : x ∈ S), ∀ k ∈ F, ∃ ab : Γ(X, U x) × Γ(X, U x),
      IsUnit (X.presheaf.germ (U x) x (hxU x hx) ab.2) ∧
        k * toK (U x) (hxU x hx) ab.2 = toK (U x) (hxU x hx) ab.1 := by
    intro x hx k hk
    obtain ⟨a, b, hb, h⟩ := exists_eq_of_mem_O (hUaff x hx) (hxU x hx) (hFO x hx hk)
    exact ⟨(a, b), hb, h⟩
  choose! ab hab_unit hab_eq using hab
  let τ : ∀ x : X, Γ(X, U x) := fun x => ∏ k ∈ F, (ab x k).2
  have hτu : ∀ x (hx : x ∈ S), IsUnit (X.presheaf.germ (U x) x (hxU x hx) (τ x)) := by
    intro x hx
    simp only [τ, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun k hk => hab_unit x hx k hk)
  let t : X → X.functionField := fun x => if hx : x ∈ S then toK (U x) (hxU x hx) (τ x) else 0
  have ht : ∀ x (hx : x ∈ S), t x = toK (U x) (hxU x hx) (τ x) := fun x hx => dite_eq_left hx
  have htu : ∀ x ∈ S, UnitAt x (t x) := fun x hx =>
    (ht x hx) ▸ UnitAt.of_isUnit_germ (hxU x hx) (hτu x hx)
  have ht0 : ∀ x ∈ S, t x ≠ 0 := fun x hx => (htu x hx).ne_zero
  have htB : ∀ x (hx : x ∈ S), t x ∈ (toK (U x) (hxU x hx)).range := fun x hx =>
    ⟨τ x, (ht x hx).symm⟩
  have hCle : ∀ x (hx : x ∈ S), C ≤ adjInv (toK (U x) (hxU x hx)).range (t x) := by
    intro x hx
    refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
    · exact (R0_le_range f (hxU x hx)).trans (le_adjInv _ _)
    · intro k hk
      have hk' : k ∈ F := hk
      have hb0 : toK (U x) (hxU x hx) (ab x k).2 ≠ 0 :=
        (UnitAt.of_isUnit_germ (hxU x hx) (hab_unit x hx k hk')).ne_zero
      have hprod : t x = toK (U x) (hxU x hx) (ab x k).2 *
          ∏ k' ∈ F.erase k, toK (U x) (hxU x hx) (ab x k').2 := by
        rw [ht x hx]; simp only [τ, map_prod]
        exact (Finset.mul_prod_erase F _ hk').symm
      have hrest0 : ∏ k' ∈ F.erase k, toK (U x) (hxU x hx) (ab x k').2 ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k' hk'' =>
          (UnitAt.of_isUnit_germ (hxU x hx) (hab_unit x hx k' (Finset.mem_of_mem_erase
            hk''))).ne_zero
      have : k = toK (U x) (hxU x hx) (ab x k).1 *
          ((∏ k' ∈ F.erase k, toK (U x) (hxU x hx) (ab x k').2) * (t x)⁻¹) := by
        rw [hprod, mul_inv, ← hab_eq x hx k hk']
        field_simp
      rw [this]
      refine Subring.mul_mem _ (le_adjInv _ _ ⟨_, rfl⟩) (Subring.mul_mem _ ?_ (inv_mem_adjInv _ _))
      exact le_adjInv _ _ (Subring.prod_mem _ fun k' _ => ⟨_, rfl⟩)
  have hm : ∀ x (hx : x ∈ S), ∃ m : ℕ, t x * sx x ^ m ∈ C := fun x hx =>
    (mem_adjInv_iff (hsxC x hx) (hsx0 x hx) (t x)).mp (hBle x hx (htB x hx))
  choose! m hm using hm
  let e : X → X.functionField := fun x => t x * sx x ^ (m x + 1)
  have heC : ∀ x ∈ S, e x ∈ C := fun x hx => mul_pow_mem_of_le (hsxC x hx) (Nat.le_succ _) (hm x hx)
  have heu : ∀ x ∈ S, UnitAt x (e x) := fun x hx => (htu x hx).mul ((hsxu x hx).pow _)
  have he0 : ∀ x ∈ S, e x ≠ 0 := fun x hx => (heu x hx).ne_zero
  have hchart : ∀ x (hx : x ∈ S), ∃ W : X.Opens, IsAffineOpen W ∧ ∃ hxW : x ∈ W,
      (toK W hxW).range = adjInv C (e x) := by
    intro x hx
    let W₁ : X.Opens := X.basicOpen (τ x)
    have hW₁ : IsAffineOpen W₁ := (hUaff x hx).basicOpen (τ x)
    have hxW₁ : x ∈ W₁ := (X.mem_basicOpen (τ x) x (hxU x hx)).mpr (hτu x hx)
    have hr₁ : (toK W₁ hxW₁).range = adjInv (toK (U x) (hxU x hx)).range (t x) := by
      ext k
      rw [mem_range_toK_basicOpen_iff (hUaff x hx) (τ x) (hxU x hx) (hτu x hx) k,
        mem_adjInv_iff (htB x hx) (ht0 x hx), ht x hx]
    have hsxW₁ : sx x ∈ (toK W₁ hxW₁).range := hr₁ ▸ hCle x hx (hsxC x hx)
    obtain ⟨σ, hσ⟩ := hsxW₁
    have hσu : IsUnit (X.presheaf.germ W₁ x hxW₁ σ) :=
      isUnit_germ_of_unitAt hxW₁ (hσ ▸ hsxu x hx)
    let W₂ : X.Opens := X.basicOpen σ
    have hW₂ : IsAffineOpen W₂ := hW₁.basicOpen σ
    have hxW₂ : x ∈ W₂ := (X.mem_basicOpen σ x hxW₁).mpr hσu
    have hr₂ : (toK W₂ hxW₂).range = adjInv (toK W₁ hxW₁).range (sx x) := by
      ext k
      have hmem : sx x ∈ (toK W₁ hxW₁).range := ⟨σ, hσ⟩
      rw [mem_range_toK_basicOpen_iff hW₁ σ hxW₁ hσu k, hσ, mem_adjInv_iff hmem (hsx0 x hx)]
    refine ⟨W₂, hW₂, hxW₂, ?_⟩
    rw [hr₂, hr₁]
    have hsxinv : (sx x)⁻¹ = (t x * sx x ^ m x) * (e x)⁻¹ := by
      simp only [e]; field_simp [ht0 x hx, hsx0 x hx]; ring
    have htinv : (t x)⁻¹ = sx x ^ (m x + 1) * (e x)⁻¹ := by
      simp only [e]; field_simp [ht0 x hx, hsx0 x hx]
    have heinv : (e x)⁻¹ = (t x)⁻¹ * ((sx x)⁻¹) ^ (m x + 1) := by
      simp only [e]; rw [mul_inv, inv_pow]
    apply le_antisymm
    · have h1 : (sx x)⁻¹ ∈ adjInv C (e x) := by
        rw [hsxinv]; exact Subring.mul_mem _ (le_adjInv _ _ (hm x hx)) (inv_mem_adjInv _ _)
      refine adjInv_le (adjInv_le ((hBle x hx).trans (adjInv_le (le_adjInv _ _) h1)) ?_) h1
      rw [htinv]
      exact Subring.mul_mem _ (le_adjInv _ _ (C.pow_mem (hsxC x hx) _)) (inv_mem_adjInv _ _)
    · refine adjInv_le ((hCle x hx).trans (le_adjInv _ _)) ?_
      rw [heinv]
      exact Subring.mul_mem _ (le_adjInv _ _ (inv_mem_adjInv _ _))
        (Subring.pow_mem _ (inv_mem_adjInv _ _) _)
  choose! W hWaff hxW hWrange using hchart
  let 𝔭 : S → Ideal C := fun i =>
    Ideal.comap (toStalk' (hCO i i.2)) (IsLocalRing.maximalIdeal (X.presheaf.stalk (i : X)))
  have h𝔭 : ∀ i : S, (𝔭 i).IsPrime := fun i => Ideal.comap_isPrime _ _
  have hmem𝔭 : ∀ (i : S) (d : C), d ∉ 𝔭 i ↔ UnitAt (i : X) (d : X.functionField) := by
    intro i d
    change toStalk' (hCO i i.2) d ∉ IsLocalRing.maximalIdeal _ ↔ _
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not, isUnit_toStalk'_iff]
  let v : S → C := fun i => ⟨e i, heC i i.2⟩
  let I : Ideal C := Ideal.span (Set.range v)
  have hI : ¬ ∃ i ∈ (Finset.univ : Finset S), I ≤ 𝔭 i := by
    rintro ⟨i, -, hi⟩
    have : v i ∈ 𝔭 i := hi (Ideal.subset_span ⟨i, rfl⟩)
    exact ((hmem𝔭 i (v i)).mpr (heu i i.2)) this
  have havoid : ¬ ((I : Set C) ⊆ ⋃ i ∈ (↑(Finset.univ : Finset S) : Set S), (𝔭 i : Set C)) := by
    rw [Ideal.subset_union_prime ⟨x₀, hx₀⟩ ⟨x₀, hx₀⟩ (fun i _ _ _ => h𝔭 i)]
    exact hI
  obtain ⟨c', hc'I, hc'⟩ := Set.not_subset.mp havoid
  have hc'u : ∀ i : S, UnitAt (i : X) (c' : X.functionField) := by
    intro i
    apply (hmem𝔭 i c').mp
    intro hi
    apply hc'
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), hi⟩
  obtain ⟨αf, hαf⟩ := Ideal.mem_span_range_iff_exists_fun.mp hc'I
  let c : X.functionField := c'
  have hcC : c ∈ C := c'.2
  have hcu : ∀ x ∈ S, UnitAt x c := fun x hx => hc'u ⟨x, hx⟩
  have hc0 : c ≠ 0 := (hcu x₀ hx₀).ne_zero
  let α : X → X.functionField := fun x => if hx : x ∈ S then (αf ⟨x, hx⟩ : X.functionField) else 0
  have hαC : ∀ x ∈ S, α x ∈ C := by
    intro x hx; simp only [α, dite_eq_left hx]; exact (αf ⟨x, hx⟩).2
  have hsum : ∑ x ∈ S, α x * e x = c := by
    rw [← Finset.sum_coe_sort S (fun x => α x * e x)]
    have h1 : (C.subtype (∑ i : S, αf i * v i)) = c := by rw [hαf]; rfl
    rw [map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : α i = (αf i : X.functionField) := by simp only [α, dite_eq_left i.2]
    rw [this, map_mul]
    rfl
  have hchart' : ∀ x (hx : x ∈ S), ∃ W' : X.Opens, IsAffineOpen W' ∧ ∃ hxW' : x ∈ W',
      (toK W' hxW').range = adjInv C (e x * c) := by
    intro x hx
    have hcW : c ∈ (toK (W x) (hxW x hx)).range := (hWrange x hx) ▸ le_adjInv C _ hcC
    obtain ⟨γ, hγ⟩ := hcW
    have hγu : IsUnit (X.presheaf.germ (W x) x (hxW x hx) γ) :=
      isUnit_germ_of_unitAt (hxW x hx) (hγ ▸ hcu x hx)
    refine ⟨X.basicOpen γ, (hWaff x hx).basicOpen γ, (X.mem_basicOpen γ x (hxW x hx)).mpr hγu, ?_⟩
    ext k
    have hmem : c ∈ (toK (W x) (hxW x hx)).range := ⟨γ, hγ⟩
    rw [mem_range_toK_basicOpen_iff (hWaff x hx) γ (hxW x hx) hγu k, hγ,
      ← mem_adjInv_iff hmem hc0 k, hWrange x hx, adjInv_adjInv_eq (heC x hx) hcC (he0 x hx) hc0]
  choose! W' hW'aff hxW' hW'range using hchart'
  refine ⟨⨆ x ∈ S, W' x, ?_, fun x hx => Opens.mem_iSup.mpr ⟨x, Opens.mem_iSup.mpr ⟨hx, hxW' x hx⟩⟩⟩
  exact isAffineOpen_iSup_of_charts f S ⟨x₀, hx₀⟩ C e c heC hcC he0 hc0 α hαC hsum W' hW'aff hxW'
    hW'range

end Main

end AffineCharts

theorem _root_.AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isDiscreteValuationRing_stalk
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [IsSeparated f]
    (S : Finset X) (hS : ∀ x ∈ S, IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U :=
  AffineCharts.main f S hS

end SchemeTheory.DVRStalks.AffineNeighborhoods
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.Specializations

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem _root_.AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes
    {X : Scheme.{u}} {x y : ↥X} (h : y ⤳ x) :
    let : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) := (X.presheaf.stalkSpecializes
      h).hom.toAlgebra
    IsLocalization.AtPrime ↑(X.presheaf.stalk y)
      (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal
        ↑(X.presheaf.stalk y))) := by
  classical
  intro instA
  have halg : ∀ a, algebraMap ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) a =
    (X.presheaf.stalkSpecializes h).hom a := fun a => rfl
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let algX : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  let algY : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyU⟩ : U)
  have hLx : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have halgX : ∀ r, algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x) r =
    (X.presheaf.germ U x hxU).hom r := fun r => rfl
  have halgY : ∀ r, algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) r =
    (X.presheaf.germ U y hyU).hom r := fun r => rfl
  have hLy : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := hU.isLocalization_stalk ⟨y, hyU⟩
  have hgerm : ∀ r : ↑(X.presheaf.obj (Opposite.op U)),
      (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hxU).hom r) = (X.presheaf.germ U y
        hyU).hom r := by
    intro r
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU h r
  have hunit : ∀ s : ↑(X.presheaf.stalk x),
      s ∈ (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal
        ↑(X.presheaf.stalk y))).primeCompl ↔
        IsUnit ((X.presheaf.stalkSpecializes h).hom s) := by
    intro s
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not]
  change IsLocalization _ _
  rw [isLocalization_iff]
  refine ⟨fun s => (hunit s.1).mp s.2, fun z => ?_, fun {a b} hab => ?_⟩
  · obtain ⟨⟨a₀, s₀⟩, e⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨y,
    hyU⟩).asIdeal.primeCompl) z
    have hs₀ : IsUnit ((X.presheaf.germ U y hyU).hom s₀) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl)
        (X.presheaf.stalk y) s₀
    refine ⟨⟨(X.presheaf.germ U x hxU).hom a₀, ⟨(X.presheaf.germ U x hxU).hom s₀, (hunit _).mpr
      (by rw [hgerm]; exact hs₀)⟩⟩, ?_⟩
    simp only [halg, hgerm]
    simpa only [halgY] using e
  · obtain ⟨⟨a₀, ua⟩, ea⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨x,
    hxU⟩).asIdeal.primeCompl) a
    obtain ⟨⟨b₀, ub⟩, eb⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨x,
      hxU⟩).asIdeal.primeCompl) b
    have hua : IsUnit ((X.presheaf.germ U x hxU).hom ua) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
        (X.presheaf.stalk x) ua
    have hub : IsUnit ((X.presheaf.germ U x hxU).hom ub) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
        (X.presheaf.stalk x) ub
    simp only [halgX] at ea eb
    have key : (X.presheaf.germ U y hyU).hom (a₀ * ub) = (X.presheaf.germ U y hyU).hom (b₀ * ua)
      := by
      rw [map_mul, map_mul, ← hgerm, ← hgerm, ← hgerm, ← hgerm, ← ea, ← eb]
      rw [map_mul, map_mul, ← halg a, ← halg b, hab]
      ring
    have key' : algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) (a₀ * ub) =
        algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) (b₀ * ua) := key
    obtain ⟨⟨c₀, hc₀⟩, ec⟩ := (IsLocalization.eq_iff_exists (hU.primeIdealOf ⟨y,
      hyU⟩).asIdeal.primeCompl (X.presheaf.stalk y)).mp key'
    have hc₀u : IsUnit ((X.presheaf.germ U y hyU).hom c₀) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl)
        (X.presheaf.stalk y) ⟨c₀, hc₀⟩
    refine ⟨⟨(X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua *
      (X.presheaf.germ U x hxU).hom ub,
      (hunit _).mpr ?_⟩, ?_⟩
    · rw [map_mul, map_mul, hgerm, hgerm, hgerm]
      exact (hc₀u.mul (by rw [← hgerm]; exact hua.map _)).mul (by rw [← hgerm]; exact hub.map _)
    · simp only
      calc
        (X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua *
            (X.presheaf.germ U x hxU).hom ub * a
          = (X.presheaf.germ U x hxU).hom c₀ * ((a * (X.presheaf.germ U x hxU).hom ua) *
            (X.presheaf.germ U x hxU).hom ub) := by ring
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((X.presheaf.germ U x hxU).hom a₀ *
          (X.presheaf.germ U x hxU).hom ub) := by rw [ea]
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((X.presheaf.germ U x hxU).hom b₀ *
          (X.presheaf.germ U x hxU).hom ua) := by
              rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ec]
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((b * (X.presheaf.germ U x hxU).hom ub) *
          (X.presheaf.germ U x hxU).hom ua) := by rw [eb]
        _ = (X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua * (X.presheaf.germ
          U x hxU).hom ub * b := by ring

end SchemeTheory.DVRStalks.Specializations
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section RingSide

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalizationAway_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ)
      (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x ϖ).mp hx
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ.ne_zero)
  · intro r hr
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero hr) hϖ
    exact ⟨ϖ ^ n, (Submonoid.mem_powers_iff _ ϖ).mpr ⟨n, rfl⟩, hn.dvd⟩

instance isLocalizationAway_uniformizer_zp (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (p : ℤ_[p]) ℚ_[p] :=
  isLocalizationAway_of_irreducible ℚ_[p] (PadicInt.irreducible_p (p := p))

theorem isLocalizationAway_uniformizer_three :
    IsLocalization.Away (3 : ℤ_[3]) ℚ_[3] := by
  exact isLocalizationAway_uniformizer_zp 3

end RingSide

section SchemeSide

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

instance isOpenImmersion_specGenericFibreInclusion :
    IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  rw [specGenericFibreInclusion_eq]
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ

theorem range_specGenericFibreInclusion_eq_basicOpen {ϖ : R} (hϖ : Irreducible ϖ) :
    Set.range (specGenericFibreInclusion R K).base =
      (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum R)) := by
  have : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  have h := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [specGenericFibreInclusion_eq]
  exact h

theorem mono_specGenericFibreInclusion_of_dvr :
    Mono (specGenericFibreInclusion R K) :=
  inferInstance

theorem flat_specGenericFibreInclusion_of_dvr :
    Flat (specGenericFibreInclusion R K) :=
  inferInstance

end SchemeSide

section PadicGates

theorem not_isIso_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  have hmem : IsLocalRing.closedPoint ℤ_[p] ∈
      Set.range (specGenericFibreInclusion ℤ_[p] ℚ_[p]).base :=
    (specGenericFibreInclusion ℤ_[p] ℚ_[p]).surjective (IsLocalRing.closedPoint ℤ_[p])
  rw [range_specGenericFibreInclusion_eq_basicOpen ℤ_[p] ℚ_[p]
    (PadicInt.irreducible_p (p := p))] at hmem
  change (p : ℤ_[p]) ∉ IsLocalRing.maximalIdeal ℤ_[p] at hmem
  exact hmem ((IsLocalRing.mem_maximalIdeal _).mpr
    (PadicInt.irreducible_p (p := p)).not_isUnit)

theorem not_isIso_specGenericFibreInclusion_three :
    ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  not_isIso_specGenericFibreInclusion_zp 3

end PadicGates

end NeronModelInfra

end

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.DVRStalks.SmoothRegularity

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

theorem isRegularLocalRing_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsRegularRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime
      Sₚ p] :
    IsRegularLocalRing Sₚ := by
  classical
  have hp : p.IsPrime := inferInstance
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  set Sf := Localization.Away f with hSf
  have : Algebra.IsStandardSmooth R Sf := hstd
  obtain ⟨ι, σ, hσ, hι, ⟨Pr⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R Sf).out
  have : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension R Sf := ⟨ι, σ, hσ, hι, Pr, rfl⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial Pr.dimension R Sf
  let : Algebra (MvPolynomial (Fin Pr.dimension) R) Sf := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin Pr.dimension) R) Sf := hg
  have hdisj : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  set q : Ideal Sf := p.map (algebraMap S Sf) with hq
  have hqp : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Sf p hp
    hdisj
  have hcomap : q.comap (algebraMap S Sf) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Sf hp hdisj
  have hunit : IsUnit (algebraMap S Sₚ f) := IsLocalization.map_units Sₚ (⟨f, hf⟩ : p.primeCompl)
  let : Algebra Sf Sₚ := (IsLocalization.Away.lift f hunit).toAlgebra
  have : IsScalarTower S Sf Sₚ := IsScalarTower.of_algebraMap_eq fun s => by
    exact (IsLocalization.Away.lift_eq f hunit s).symm
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro _ ⟨k, rfl⟩
    exact fun h => hf (hp.mem_of_pow_mem k h)
  have hloc : IsLocalization (p.primeCompl.map (algebraMap S Sf)) Sₚ :=
    IsLocalization.isLocalization_of_submonoid_le Sf Sₚ (Submonoid.powers f) p.primeCompl hle
  have : IsLocalization.AtPrime Sₚ q := by
    refine IsLocalization.of_le_of_exists_dvd (p.primeCompl.map (algebraMap S Sf)) q.primeCompl ?_
      ?_
    · rintro _ ⟨s, hs, rfl⟩
      change algebraMap S Sf s ∉ q
      intro h
      exact hs (by rw [← hcomap]; exact h)
    · intro n hn
      obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) n
      have hm : (m : S) ∉ p := Set.disjoint_left.mp hdisj m.2
      have hs : s ∉ p := by
        intro hs
        apply hn
        have hspec : IsLocalization.mk' Sf s m * algebraMap S Sf m = algebraMap S Sf s :=
          IsLocalization.mk'_spec Sf s m
        have hmem : algebraMap S Sf s ∈ q := Ideal.mem_map_of_mem _ hs
        rw [← hspec] at hmem
        rcases hqp.mem_or_mem hmem with h | h
        · exact h
        · exact absurd (show (m : S) ∈ p by rw [← hcomap]; exact h) hm
      exact ⟨algebraMap S Sf s, ⟨s, hs, rfl⟩, algebraMap S Sf m, (IsLocalization.mk'_spec Sf s
        m).symm⟩
  have : IsRegularRing (MvPolynomial (Fin Pr.dimension) R) := inferInstance
  have hreg : IsRegularLocalRing (Localization.AtPrime q) :=
    isRegularLocalRing_localization_atPrime_of_etale_of_comap
      (MvPolynomial (Fin Pr.dimension) R) Sf q
      (IsRegularRing.isRegularLocalRing_localization _)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Sₚ).toRingEquiv

theorem _root_.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsRegularLocalRing (T.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth (f := t) x
  have hle' : V ≤ t ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := le_top
  have hQ : (t.appLE ⊤ V hle').hom.Smooth :=
    HasRingHomProperty.appLE @Smooth t inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hle'
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let ψ : R →+* Γ(T, V) := (t.appLE ⊤ V hle').hom.comp e.toRingHom
  have hψ : ψ.Smooth := RingHom.Smooth.respectsIso.2 _ e hQ
  let : Algebra R Γ(T, V) := ψ.toAlgebra
  have : Algebra.Smooth R Γ(T, V) := RingHom.smooth_algebraMap.mp hψ
  let : Algebra Γ(T, V) (T.presheaf.stalk x) := (T.presheaf.germ V x hxV).hom.toAlgebra
  have : IsLocalization.AtPrime (T.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact isRegularLocalRing_of_isLocalization_atPrime R Γ(T, V)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (T.presheaf.stalk x)

end SchemeTheory.DVRStalks.SmoothRegularity
end
